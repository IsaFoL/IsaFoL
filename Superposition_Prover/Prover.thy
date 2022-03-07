theory Prover
  imports
    Ordered_Resolution_Prover.Abstract_Substitution
    SuperCalc.superposition
    Saturation_Framework.Calculus
    Saturation_Framework.Lifting_to_Non_Ground_Calculi
    Saturation_Framework_Extensions.Standard_Redundancy_Criterion
    Saturation_Framework_Extensions.Soundness
    "HOL-Library.Multiset_Order"
begin


subsection \<open>Generic lemmas about HOL definitions\<close>

lemma set_eq_unionI:
  assumes "\<And>x. x \<in> A \<longleftrightarrow> x \<in> B \<or> x \<in> C"
  shows "A = (B \<union> C)"
  using assms by blast

lemma total_trancl: "total R \<Longrightarrow> total (trancl R)"
  by (meson Relation.total_on_def r_into_trancl')

lemma refl_Un: "refl S1 \<or> refl S2 \<Longrightarrow> refl (S1 \<union> S2)"
  by (auto dest: refl_onD intro: refl_onI)

lemma refl_trivial: "refl {(x, x) | x. True}"
  by (rule refl_onI) simp_all

lemma inj_imp_inj_on[simp]: "inj f \<Longrightarrow> inj_on f S"
  by (simp add: inj_def inj_onI)

lemma list_all_ex_iff_ex_list_all2: "list_all (\<lambda>x. \<exists>y. P x y) xs \<longleftrightarrow> (\<exists>ys. list_all2 P xs ys)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof (rule iffI; (elim exE)?)
  show "?lhs \<Longrightarrow> ?rhs"
    by (induction xs) auto
next
  fix ys
  show "list_all2 P xs ys \<Longrightarrow> ?lhs"
    by (induction xs ys rule: list.rel_induct) auto
qed

lemma list_all2_conj_unary_iff:
  "list_all2 (\<lambda>x y. P1 x \<and> Q x y) xs ys \<longleftrightarrow> list_all P1 xs \<and> list_all2 (\<lambda>x y. Q x y) xs ys"
  "list_all2 (\<lambda>x y. P2 y \<and> Q x y) xs ys \<longleftrightarrow> list_all P2 ys \<and> list_all2 (\<lambda>x y. Q x y) xs ys"
  by (auto simp: list_all2_conv_all_nth list_all_length)

lemma list_all_member_iff_subset: "list_all (\<lambda>x. x \<in> N) xs \<longleftrightarrow> set xs \<subseteq> N"
  by (simp add: list.pred_set subset_code(1))

lemma inj_on_image_set_diff': "inj_on f (A \<union> B) \<Longrightarrow> f ` (A - B) = f ` A - f ` B"
  by (metis Un_Diff_cancel2 inj_on_image_set_diff sup_ge1 sup_ge2)

lemma image_set_eq_set: "map f xs = ys \<Longrightarrow> f ` set xs = set ys"
  by force

lemma set_filter_subset_set_filter_conv: "{s \<in> S. P s} \<subseteq> {s \<in> S. Q s} \<longleftrightarrow> (\<forall>s \<in> S. P s \<longrightarrow> Q s)"
  by blast


subsection \<open>Generic lemmas about HOL-Library definitions\<close>

lemma irrefl_mult1:
  assumes "irrefl R"
  shows "irrefl (mult1 R)"
proof (rule irreflI)
  fix x
  show "(x, x) \<notin> mult1 R"
    unfolding mult1_def
    using assms irrefl_def by fastforce
qed

lemma add_mset_image_mset_mset_set_minus[simp]: "finite S \<Longrightarrow> s \<in> S \<Longrightarrow>
  add_mset (f s) (image_mset f (mset_set (S - {s}))) = image_mset f (mset_set S)"
  by (simp add: mset_set.remove)

lemma image_mset_mset_set_minus_multI:
  assumes "finite S" "T \<subseteq> S" "T \<noteq> {}"
  shows "(image_mset f (mset_set (S - T)), image_mset f (mset_set S)) \<in> mult r"
  using one_step_implies_mult[of "image_mset f (mset_set T)" "{#}" _
      "image_mset f (mset_set (S - T))", simplified]
  unfolding mset_set_Diff[OF assms(1,2)]
  unfolding image_mset_union[symmetric]
  unfolding subset_imp_msubset_mset_set[OF assms(2,1),
      THEN Multiset.subset_mset.diff_add[of "mset_set T" "mset_set S"]]
  by (meson assms finite_subset mset_set_empty_iff)

lemma Bex_mset_set[simp]:
  assumes "finite S"
  shows "(\<exists>x \<in># mset_set S. P x) = (\<exists>x \<in> S. P x)"
  (is "?lhs = ?rhs")
  using elem_mset_set[OF assms]
  by blast

lemma image_mset_mset_set_insert_minus_multI:
  assumes
    fin_S: "finite S" and
    T_subseteq_S: "T \<subseteq> S" and
    T_neq_empty: "T \<noteq> {}" and
    Bex_x_less: "\<exists>j\<in>T. (f x, f j) \<in> r" and
    trans_r: "trans r"
  shows "(image_mset f (mset_set (insert x (S - T))), image_mset f (mset_set S)) \<in> mult r"
proof (cases "x \<in> S - T")
  case True
  show ?thesis
    by (auto simp: insert_absorb[OF True]
        intro: image_mset_mset_set_minus_multI[OF fin_S T_subseteq_S T_neq_empty])
next
  case False
  have fin_T: "finite T"
    by (rule rev_finite_subset[OF fin_S T_subseteq_S])
  have "finite (S - T)"
    using fin_S T_subseteq_S by simp
  have "mset_set S = mset_set ((S - T) \<union> T)"
    using T_subseteq_S
    by (simp add: sup.absorb1)
  also have "... = mset_set (S - T) + mset_set T"
    by (metis T_subseteq_S calculation fin_S mset_set_Diff subset_imp_msubset_mset_set subset_mset.diff_add)
  finally have mset_S_conv: "mset_set S = mset_set (S - T) + mset_set T" by assumption
  have mset_insert_minus_conv: "mset_set (insert x (S - T)) = mset_set (S - T) + {#x#}"
    unfolding mset_set.insert[OF \<open>finite (S - T)\<close> False]
    by auto
  show ?thesis
    unfolding mset_insert_minus_conv
    unfolding mset_S_conv image_mset_union
    apply (rule Multiset.one_step_implies_mult)
     apply (meson T_neq_empty T_subseteq_S fin_S image_mset_is_empty_iff infinite_super mset_set_empty_iff)
    using Bex_x_less
    by (simp add: Bex_mset_set[OF fin_T])
qed


subsection \<open>Generic definitions and associated lemmas\<close>

definition uncurry where
  "uncurry f \<equiv> \<lambda>(x, y). f x y"

lemma uncurry_conv[simp]: "uncurry f (x, y) = f x y"
  by (simp add: uncurry_def)

lemma curry_uncurry[simp]: "curry (uncurry f) = f"
  by (simp add: curry_def uncurry_def)

lemma uncurry_curry[simp]: "uncurry (curry f) = f"
  by (simp add: curry_def uncurry_def)

lemma curry_comp_uncurry[simp]: "curry o uncurry = id"
  by (simp add: curry_def uncurry_def id_def comp_def)

lemma uncurry_comp_curry[simp]: "uncurry o curry = id"
  by (simp add: curry_def uncurry_def id_def comp_def)


subsection \<open>Generic lemmas about SuperCalc\<close>

lemma subst_cl_conv: "subst_cl C \<sigma> = (\<lambda>L. equational_clausal_logic.subst_lit L \<sigma>) ` C"
  unfolding subst_cl.simps
  by auto

lemma validate_clause_set_union:
  "validate_clause_set I (S1 \<union> S2) \<longleftrightarrow> validate_clause_set I S1 \<and> validate_clause_set I S2"
  by auto

lemma negative_literal_subst[simp]: "negative_literal (equational_clausal_logic.subst_lit L \<sigma>) = negative_literal L"
  by (cases L) simp_all


lemma vars_of_subst_conv: "vars_of (subst t \<eta>) = \<Union>(vars_of ` (\<lambda>x. subst (Var x) \<eta>) ` vars_of t)"
  by (induction t) simp_all

lemma vars_of_eq_subst_conv: "vars_of_eq (subst_equation eq \<eta>) = \<Union>(vars_of ` (\<lambda>x. subst (Var x) \<eta>) ` vars_of_eq eq)"
  by (cases eq) (simp add: vars_of_subst_conv)

lemma vars_of_lit_subst_conv:
  "vars_of_lit (equational_clausal_logic.subst_lit L \<eta>) =
    \<Union>(vars_of ` (\<lambda>x. subst (Var x) \<eta>) ` vars_of_lit L)"
  by (cases L) (simp_all add: vars_of_eq_subst_conv)

lemma vars_of_cl_subst_renaming_conv:
  assumes renaming_\<eta>: "renaming \<eta> (vars_of_cl C)"
  shows "vars_of_cl (subst_cl C \<eta>) = (\<Union>x \<in> vars_of_cl C. vars_of (subst (Var x) \<eta>))"
  (is "?lhs = ?rhs")
proof (rule Set.equalityI; rule Set.subsetI)
  fix x
  assume "x \<in> ?lhs"
  then obtain L where x_in: "x \<in> vars_of_lit L" and "L \<in> subst_cl C \<eta>" by auto
  then obtain L' where L'_in: "L' \<in> C" and L_def: "L = equational_clausal_logic.subst_lit L' \<eta>"
    by (smt (verit, del_insts) mem_Collect_eq subst_cl.simps)
  from x_in and L_def have "x \<in> vars_of_lit (equational_clausal_logic.subst_lit L' \<eta>)" by simp
  from \<open>x \<in> vars_of_lit L\<close> obtain x' where
    x'_in: "x' \<in> vars_of_lit L'" and "subst (Var x') \<eta> = Var x"
    unfolding L_def
    unfolding vars_of_lit_subst_conv
    apply simp
    by (metis \<open>L' \<in> C\<close> is_a_variable.elims(2) occs.simps(1) renaming_\<eta> renaming_def subsetD
        subst.simps(1) vars_iff_occseq vars_of_cl_lem)

  show "x \<in> ?rhs"
    unfolding UN_iff
  proof (rule bexI[where x = x'])
    show "x \<in> vars_of (Var x' \<lhd> \<eta>)"
      unfolding \<open>subst (Var x') \<eta> = Var x\<close>
      by simp
  next
    show "x' \<in> vars_of_cl C"
      using x'_in L'_in by auto
  qed
next
  fix x'
  assume "x' \<in> ?rhs"
  then obtain x where x_in: "x \<in> vars_of_cl C" and "x' \<in> vars_of (Var x \<lhd> \<eta>)"
    by blast
  hence "subst (Var x) \<eta> = Var x'"
    using renaming_\<eta>[unfolded renaming_def, rule_format]
    by (metis is_a_variable.elims(2) occs.simps(1) vars_iff_occseq)

  from x_in obtain L where x_in: "x \<in> vars_of_lit L" and "L \<in> C"
    by auto

  show "x' \<in> ?lhs"
    unfolding vars_of_cl.simps mem_Collect_eq
  proof (intro exI conjI)
    show "x' \<in> vars_of_lit (equational_clausal_logic.subst_lit L \<eta>)"
      unfolding vars_of_lit_subst_conv
      using x_in \<open>Var x \<lhd> \<eta> = Var x'\<close>
      by fastforce
  next
    show "equational_clausal_logic.subst_lit L \<eta> \<in> subst_cl C \<eta>"
      using \<open>L \<in> C\<close>
      by (auto simp: subst_cl.simps)
  qed
qed

lemma vars_of_cl_conv: "vars_of_cl C = (\<Union>L \<in> C. vars_of_lit L)"
proof (rule Set.equalityI; rule Set.subsetI)
  fix x
  show "x \<in> vars_of_cl C \<Longrightarrow> x \<in> \<Union> (vars_of_lit ` C)"
    by force
next
  fix x
  show "x \<in> \<Union> (vars_of_lit ` C) \<Longrightarrow> x \<in> vars_of_cl C"
    by force
qed


lemma ground_clause_subst_renaming:
  assumes ren_\<eta>: "renaming \<eta> (vars_of_cl C)"
  shows "ground_clause (subst_cl C \<eta>) \<longleftrightarrow> ground_clause C"
proof -
  show ?thesis
    unfolding ground_clause.simps
    using vars_of_cl_subst_renaming_conv[OF ren_\<eta>]
    by (smt (verit, ccfv_threshold) SUP_bot_conv(1) UN_constant is_a_variable.elims(2) ren_\<eta>
        renaming_def vars_iff_occseq)
qed

lemma singleton_set_entails_clause_iff[iff]:
  "set_entails_clause {C} D \<longleftrightarrow> clause_entails_clause C D"
  by (simp add: clause_entails_clause_def set_entails_clause_def)

definition set_entails_set where
  "set_entails_set N1 N2 \<longleftrightarrow>
    (\<forall>I. fo_interpretation I \<longrightarrow> validate_clause_set I N1 \<longrightarrow> validate_clause_set I N2)"

lemma set_entails_set_refl[simp]: "set_entails_set C C"
  unfolding set_entails_set_def
  by blast

lemma transp_set_entails_set: "transp set_entails_set"
  apply (rule transpI)
  unfolding set_entails_set_def
  by blast

lemma sent_entails_subset_eq: "N \<subseteq> N' \<Longrightarrow> set_entails_set N M \<Longrightarrow> set_entails_set N' M"
  unfolding set_entails_set_def
  by (metis subset_Un_eq validate_clause_set_union)

lemma set_entails_set_singleton[simp]: "set_entails_set N {C} \<longleftrightarrow> set_entails_clause N C"
  by (simp add: set_entails_set_def set_entails_clause_def)

context basic_superposition begin

lemma subst_cl_empty[simp]: "subst_cl {} \<sigma> = {}"
  by simp

lemma ground_clause_empty[simp]: "ground_clause {}"
  by simp

lemma instances_subset_eqI:
  assumes subset: "N \<subseteq> N'"
  shows "instances N \<subseteq> instances N'"
  using subset
  unfolding instances_def
  by auto

lemma redundant_clause_subset_eqI:
  assumes subset: "N \<subseteq> N'" and redundant: "redundant_clause C N \<sigma> C'"
  shows "redundant_clause C N' \<sigma> C'"
  using redundant instances_subset_eqI[OF subset]
  unfolding redundant_clause_def
  by fast

lemma redundant_inference_subset:
  assumes subset: "N \<subseteq> N'" and redundant: "redundant_inference concl N prems \<sigma>"
  shows "redundant_inference concl N' prems \<sigma>"
  using redundant instances_subset_eqI[OF subset]
  unfolding redundant_inference_def
  by fast

lemma instances_union: "instances (A \<union> B) = instances A \<union> instances B"
  unfolding instances_def
  by blast

lemma instances_eq_union_singleton:
  shows "C \<in> N \<Longrightarrow> instances N = instances {C} \<union> instances (N - {C})"
  unfolding instances_union[symmetric]
  by (simp add: insert_Diff insert_absorb)

lemma set_entails_clause_member:
  assumes "C \<in> N"
  shows "set_entails_clause (clset_instances (instances N)) (cl_ecl C)"
  unfolding set_entails_clause_def
proof (intro allI impI)
  fix I
  assume "fo_interpretation I" and "validate_clause_set I (clset_instances (instances N))"
  then show "validate_clause I (cl_ecl C)"
    unfolding clset_instances_def instances_def
    using \<open>C \<in> N\<close>
    by (smt (verit, best) fst_eqD mem_Collect_eq snd_eqD substs_preserve_ground_clause
        validate_clause.simps validate_clause_set.elims(1))
qed

lemma set_entails_clause_clset_instances_instancesI:
  assumes N_entails_C: "set_entails_clause (cl_ecl ` N) C"
  shows "set_entails_clause (clset_instances (instances N)) C"
proof (unfold set_entails_clause_def, intro allI impI)
  fix I :: "'a trm \<Rightarrow> 'a trm \<Rightarrow> bool"
  assume
    I_interp: "fo_interpretation I" and
    I_validate: "validate_clause_set I (clset_instances (instances N))"
  show "validate_clause I C"
    apply (rule N_entails_C[unfolded set_entails_clause_def, rule_format, OF I_interp])
    using I_validate
    by (metis (mono_tags, lifting) I_interp set_entails_clause_member imageE
        set_entails_clause_def validate_clause_set.elims(3))
qed

lemma clset_instances_conv: "clset_instances S = (\<lambda>(C, \<sigma>). subst_cl (cl_ecl C) \<sigma>) ` S"
  by (auto simp add: clset_instances_def)

lemma "(\<exists>x. P \<and> Q x) \<longleftrightarrow> P \<and> (\<exists>x. Q x)"
  by simp

lemma ball_instances_singleton_conv: "(\<forall>x\<in>instances {C}. P x) \<longleftrightarrow> (\<forall>(_, \<sigma>)\<in>instances {C}. P (C, \<sigma>))"
  unfolding instances_def
  by simp

lemma subst_set_image_conv: "subst_set T \<sigma> = image (\<lambda>t. subst t \<sigma>) T"
  by auto

lemma occurs_in_refl[simp]: "occurs_in t t"
  unfolding occurs_in_def
proof (rule exI)
  show "subterm t [] t"
    by simp
qed

lemma validate_clause_set_singleton[dest, intro]: "validate_clause_set I {C} \<Longrightarrow> validate_clause I C"
  by simp

lemma validate_clause_subset_eq[intro]:
  assumes "validate_clause_set I ys" and "xs \<subseteq> ys"
  shows "validate_clause_set I xs"
  using assms
  by (simp add: subset_eq)

lemma cl_ord_eq_refl: "refl cl_ord_eq"
proof (rule refl_onI)
  fix x
  show "(x, x) \<in> cl_ord_eq"
    unfolding cl_ord_eq_def
    by simp
qed simp

lemma refl_eq_mset_cl: "refl {(x, y). mset_cl x = mset_cl y}"
  by (simp add: refl_on_def)

lemma irrefl_cl_ord: "irrefl cl_ord"
proof (rule irreflI)
  fix X
  show "(X, X) \<notin> cl_ord"
    unfolding cl_ord_def
    using irrefl_mult[OF] irrefl_mult[OF trm_ord_trans trm_ord_irrefl]  mult_trm_ord_trans
    unfolding irrefl_def
    by auto
qed

lemma cl_ord_eq_almost_antisym:
  "(X, Y) \<in> cl_ord_eq \<Longrightarrow> (Y, X) \<in> cl_ord_eq \<Longrightarrow> (X, Y) \<in> {(x, y). mset_cl x = mset_cl y}"
  unfolding cl_ord_eq_def
  using irrefl_cl_ord[unfolded irrefl_def]
  by (metis (mono_tags, lifting) UnE case_prodD case_prodI cl_ord_trans mem_Collect_eq transD)

lemma cl_ord_eq_not_antisym: "\<not> antisym cl_ord_eq"
proof (rule notI)
  fix x :: "'a" and t :: "'a trm"
  define lit where "lit \<equiv> Pos (Eq (Const x) (Const x))"
  define \<sigma>\<^sub>1 where "\<sigma>\<^sub>1 \<equiv> [(x, t)]"
  define \<sigma>\<^sub>2 where "\<sigma>\<^sub>2 \<equiv> [(x, t), (x, t)]"
  define X where "X \<equiv> ({lit}, \<sigma>\<^sub>1)"
  define Y where "Y \<equiv> ({lit}, \<sigma>\<^sub>2)"

  have "mset_cl X = mset_cl Y"
    by (simp add: X_def Y_def lit_def)
  hence x_le_y: "(X, Y) \<in> cl_ord_eq" and y_le_x: "(Y, X)\<in> cl_ord_eq"
    by (simp_all add: cl_ord_eq_def)

  assume "antisym cl_ord_eq"
  show False
    using antisymD[OF \<open>antisym cl_ord_eq\<close> x_le_y y_le_x]
    by (simp add: X_def Y_def \<sigma>\<^sub>1_def \<sigma>\<^sub>2_def)
qed

lemma subst_trm_ident[simp]:
  assumes trivial_\<sigma>: "\<And>x d. x \<in> vars_of t \<Longrightarrow> assoc x d \<sigma> = d"
  shows "subst t \<sigma> = t"
  using trivial_\<sigma>
  by (induction t) simp_all

lemma subst_equation_ident[simp]:
  assumes trivial_\<sigma>: "\<And>x d. x \<in> vars_of_eq e \<Longrightarrow> assoc x d \<sigma> = d"
  shows "subst_equation e \<sigma> = e"
  by (cases e) (simp add: trivial_\<sigma>)

lemma subst_lit_ident[simp]:
  assumes trivial_\<sigma>: "\<And>x d. x \<in> vars_of_lit l \<Longrightarrow> assoc x d \<sigma> = d"
  shows "subst_lit l \<sigma> = l"
  by (cases l) (simp_all add: trivial_\<sigma>)

lemma subst_cl_ident[simp]:
  assumes trivial_\<sigma>: "\<And>x d. x \<in> vars_of_cl C \<Longrightarrow> assoc x d \<sigma> = d"
  shows "subst_cl C \<sigma> = C"
proof -
  have "subst_cl C \<sigma> = (\<lambda>l. subst_lit l \<sigma>) ` C"
    by auto
  also have "... = C"
    by (rule image_cong[of C C _ id, simplified])
      (auto dest: vars_of_cl_lem simp add: subset_iff trivial_\<sigma>)
  finally show ?thesis
    by assumption
qed

lemma subst_ecl_ident[simp]:
  assumes trivial_\<sigma>: "\<And>x d. x \<in> vars_of_cl (cl_ecl C) \<union> \<Union>(vars_of ` (trms_ecl C)) \<Longrightarrow> assoc x d \<sigma> = d"
  shows "subst_ecl C \<sigma> = C"
proof (cases C)
  case (Ecl C' ts)
  note trivial_\<sigma>' = trivial_\<sigma>[unfolded Ecl cl_ecl.simps trms_ecl.simps Un_iff]
  show ?thesis
    unfolding Ecl subst_ecl.simps eclause.inject
  proof (rule conjI)
    show "subst_cl C' \<sigma> = C'"
      using disjI1[THEN trivial_\<sigma>'] subst_cl_ident
      by blast
  next
    show "{t \<lhd> \<sigma> |t. t \<in> ts} = ts"
      unfolding Setcompr_eq_image
      apply (rule image_cong[of ts ts _ id, simplified])
      using disjI2[THEN trivial_\<sigma>']
      by (meson UnionI imageI subst_trm_ident)
  qed
qed

fun sym_eq where
  "sym_eq (Eq t s) = Eq s t"

fun sym_lit :: "'a literal \<Rightarrow> 'a literal" where
  "sym_lit (Pos e) = Pos (sym_eq e)" |
  "sym_lit (Neg e) = Neg (sym_eq e)"

lemma mset_lit_eq_conv: "mset_lit x = mset_lit y \<Longrightarrow> x = y \<or> x = sym_lit y"
  apply (cases x rule: mset_lit.cases; cases y rule: mset_lit.cases)
     apply simp_all
     apply (metis add_eq_conv_ex add_mset_eq_singleton_iff)
    apply (simp add: add_eq_conv_ex)
   apply (simp add: add_eq_conv_ex)
  by (smt (verit, ccfv_threshold) add_mset_eq_single add_mset_remove_trivial diff_union_swap)

lemma trans_irrefl_imp_antisym:
  assumes "trans R" and "irrefl R"
  shows "antisym R"
proof (rule antisymI)
  fix x y
  assume "(x, y) \<in> R" and "(y, x) \<in> R"
  hence "(x, x) \<in> R"
    using transD[OF \<open>trans R\<close>] by blast
  moreover have "(x, x) \<notin> R"
    using \<open>irrefl R\<close> by (simp add: irrefl_def)
  ultimately show "x = y"
    by contradiction
qed

lemma antisym_Un_cl_ord_trivial_refl:
  defines ord_def: "ord \<equiv> cl_ord \<union> {(x, x) |x. True}"
  shows "antisym (Set.filter (\<lambda>((_, \<sigma>\<^sub>x), (_, \<sigma>\<^sub>y)). \<sigma>\<^sub>x = [] \<and> \<sigma>\<^sub>y = []) ord)"
proof (rule antisymI)
  note antisym_cl_ord = trans_irrefl_imp_antisym[OF cl_ord_trans irrefl_cl_ord]
  fix x y
  assume
    "(x, y) \<in> Set.filter (\<lambda>((_, \<sigma>\<^sub>x), _, \<sigma>\<^sub>y). \<sigma>\<^sub>x = [] \<and> \<sigma>\<^sub>y = []) ord" and
    "(y, x) \<in> Set.filter (\<lambda>((_, \<sigma>\<^sub>y), _, \<sigma>\<^sub>x). \<sigma>\<^sub>y = [] \<and> \<sigma>\<^sub>x = []) ord"
  then obtain x' y' where
    "x = (x', [])" and "(x, y) \<in> ord" and
    "y = (y', [])" and "(y, x) \<in> ord"
    using Set.member_filter by auto
  hence
    "(x, y) \<in> cl_ord \<or> x = y" and
    "(y, x) \<in> cl_ord \<or> x = y"
    by (auto simp add: cl_ord_eq_def ord_def)
  then show "x = y"
    by (auto intro: antisymD[OF antisym_cl_ord])
qed

lemma wf_cl_ord:
  shows "wf cl_ord"
proof -
  have "wf (mult trm_ord)" using trm_ord_wf and wf_mult  by auto
  then have "wf (mult (mult trm_ord))" using wf_mult  by auto
  thus ?thesis
    using cl_ord_def
      and measure_wf [of "(mult (mult trm_ord))" cl_ord mset_cl]
      by blast
qed

lemma cl_ord_iff_cl_ord_eq_and_not:
  "\<And>x y. (x, y) \<in> cl_ord \<longleftrightarrow> (x, y) \<in> cl_ord_eq \<and> (y, x) \<notin> cl_ord_eq"
  by (smt (verit, best) Un_iff case_prod_conv cl_ord_def cl_ord_eq_almost_antisym cl_ord_eq_def
      irrefl_def irrefl_mult mem_Collect_eq mult_trm_ord_trans trm_ord_irrefl trm_ord_trans)

lemma cl_ord_iff_reflcl_cl_ord_and_not:
  "\<And>x y. (x, y) \<in> cl_ord \<longleftrightarrow> (x, y) \<in> cl_ord\<^sup>= \<and> (y, x) \<notin> cl_ord\<^sup>="
  using cl_ord_iff_cl_ord_eq_and_not by force

lemma renaming_Nil[simp]: "renaming [] vs"
  by (simp add: renaming_def)

lemma renaming_ident[simp]: "renaming_cl C C"
  unfolding renaming_cl_def
proof (rule exI)
  show "renaming [] (vars_of_cl (cl_ecl C)) \<and> C = subst_ecl C []"
    by simp
qed

lemma subst_ecl_subst_ecl[simp]: "subst_ecl (subst_ecl C \<sigma>\<^sub>1) \<sigma>\<^sub>2 = subst_ecl C (\<sigma>\<^sub>1 \<lozenge> \<sigma>\<^sub>2)"
proof (cases C)
  case (Ecl C' ts)
  show ?thesis
    unfolding Ecl subst_ecl.simps
    unfolding eclause.inject
  proof (rule conjI)
    show "subst_cl (subst_cl C' \<sigma>\<^sub>1) \<sigma>\<^sub>2 = subst_cl C' (\<sigma>\<^sub>1 \<lozenge> \<sigma>\<^sub>2)"
      unfolding composition_of_substs_cl
      by (rule refl)
  next
    show "{t \<lhd> \<sigma>\<^sub>2 |t. t \<in> {t \<lhd> \<sigma>\<^sub>1 |t. t \<in> ts}} = {t \<lhd> \<sigma>\<^sub>1 \<lozenge> \<sigma>\<^sub>2 |t. t \<in> ts}"
      unfolding Setcompr_eq_image
      by (simp add: image_image)
  qed
qed

lemma all_trms_irreducible_empty[simp]: "all_trms_irreducible {} f"
  unfolding all_trms_irreducible_def by simp

lemma derivable_finite_conclusion:
  assumes "\<forall>C \<in> P. finite (cl_ecl C)" and  "derivable C P S \<sigma> k C'"
  shows "finite C'"
  using assms
  by (auto simp: derivable_def superposition_def factorization_def reflexion_def)

lemma ecl_ord_conv[simp]:
  "((Ecl C ts\<^sub>C, \<sigma>\<^sub>C), (Ecl D ts\<^sub>D, \<sigma>\<^sub>D)) \<in> ecl_ord \<longleftrightarrow>
  ((C, \<sigma>\<^sub>C), (D, \<sigma>\<^sub>D)) \<in> cl_ord"
  unfolding cl_ord_def ecl_ord_def
  by simp

lemma ck_unifier_conv: "ck_unifier t s \<sigma> k \<longleftrightarrow>
  Unifier \<sigma> t s \<and> (k = FirstOrder \<longrightarrow> (\<forall>\<theta>. Unifier \<theta> t s \<longrightarrow> (\<exists>\<gamma>. \<theta> \<doteq> \<sigma> \<lozenge> \<gamma>)))"
  unfolding ck_unifier_def
  by (cases k) (simp_all add: MGU_def)

lemma reflexion_conclusion_smaller:
  assumes refl_C': "reflexion P1 C \<sigma> k C'" and fin_P1: "finite (cl_ecl P1)"
  shows "((C', \<sigma>), (cl_ecl P1, \<sigma>)) \<in> cl_ord"
proof -
  show ?thesis
    using refl_C'[unfolded reflexion_def]
    unfolding cl_ord_def
    using image_mset_mset_set_minus_multI[OF fin_P1, of "{x}" for x, simplified]
    by auto
qed

lemma factorization_conclusion_smaller:
  assumes fact_C': "factorization P1 C \<sigma> k C'" and fin_P1: "finite (cl_ecl P1)" and
    total_trm_ord: "Relation.total_on
      (\<Union>(case_equation (\<lambda>t1 t2. {t1, t2}) ` atom ` cl_ecl P1)) trm_ord"
  shows "((C', \<sigma>), (cl_ecl P1, \<sigma>)) \<in> cl_ord"
proof -
  from fact_C' obtain L1 L2 t s u v where
    "eligible_literal L1 P1 \<sigma>" and
    L1_in_P1: "L1 \<in> cl_ecl P1" and
    L2_in_P1: "L2 \<in> cl_ecl P1 - {L1}" and
    orient_L1: "orient_lit_inst L1 t s pos \<sigma>" and
    orient_L2: "orient_lit_inst L2 u v pos \<sigma>" and
    t_neq_s: "t \<lhd> \<sigma> \<noteq> s \<lhd> \<sigma>" and
    t_neq_v: "t \<lhd> \<sigma> \<noteq> v \<lhd> \<sigma>" and
    unif_t_u: "ck_unifier t u \<sigma> k" and
    C'_def: "C' = cl_ecl P1 - {L2} \<union> {equational_clausal_logic.literal.Neg (Eq s v)}"
    by (auto simp: factorization_def)

  have
    "s \<in> case_equation (\<lambda>t1 t2. {t1, t2}) (atom L1)" and
    "t \<in> case_equation (\<lambda>t1 t2. {t1, t2}) (atom L1)"
    using orient_L1 by (auto simp: orient_lit_inst_def)
  hence
    t_in_P1: "t \<in> \<Union>(case_equation (\<lambda>t1 t2. {t1, t2}) ` atom ` cl_ecl P1)" and
    s_in_P1: "s \<in> \<Union>(case_equation (\<lambda>t1 t2. {t1, t2}) ` atom ` cl_ecl P1)"
    using L1_in_P1 by blast+

  have
    "u \<in> case_equation (\<lambda>t1 t2. {t1, t2}) (atom L2)" and
    "v \<in> case_equation (\<lambda>t1 t2. {t1, t2}) (atom L2)"
    using orient_L2 by (auto simp: orient_lit_inst_def)
  hence
    u_in_P1: "u \<in> \<Union>(case_equation (\<lambda>t1 t2. {t1, t2}) ` atom ` cl_ecl P1)" and
    v_in_P1: "v \<in> \<Union> (case_equation (\<lambda>t1 t2. {t1, t2}) ` atom ` cl_ecl P1)"
    using L2_in_P1 by blast+

  have "(t \<lhd> \<sigma>, s \<lhd> \<sigma>) \<notin> trm_ord"
    using orient_L1 by (simp add: orient_lit_inst_def)
  hence "(s \<lhd> \<sigma>, t \<lhd> \<sigma>) \<in> trm_ord"
    using total_trm_ord[unfolded Relation.total_on_def, rule_format, OF t_in_P1 s_in_P1]
    using t_neq_s
    using trm_ord_subst by blast
  moreover have "t \<lhd> \<sigma> = u \<lhd> \<sigma>"
    using unif_t_u
    by (cases k) (simp_all add: ck_unifier_def MGU_def Unifier_def)
  ultimately have "(mset_lit (subst_lit (equational_clausal_logic.literal.Neg (Eq s v)) \<sigma>),
    mset_lit (subst_lit L2 \<sigma>)) \<in> mult trm_ord"
    using orient_L2 unfolding orient_lit_inst_def
    using total_trm_ord[unfolded Relation.total_on_def, rule_format, OF u_in_P1 v_in_P1]
    using t_neq_v
    apply -
    apply (rule one_step_implies_mult[of _ _ _ "{#}", simplified])
    apply auto [1]
    apply safe
    by (auto intro: trm_ord_subst[rule_format])

  then show ?thesis
    unfolding C'_def cl_ord_def
    apply auto
    apply (rule image_mset_mset_set_insert_minus_multI)
    using fin_P1 apply blast
    using \<open>L2 \<in> cl_ecl P1 - {L1}\<close> apply blast
      apply simp
     apply simp
    using mult_trm_ord_trans by fastforce
qed

lemma trm_ord_replace_subterm:
  assumes
    "subterm t p v"
    "replace_subterm t p v' t'"
  shows "(v', v) \<in> trm_ord \<Longrightarrow> (t', t) \<in> trm_ord"
  using assms
proof (induction t p v' t' rule: replace_subterm.induct)
  case (4 x y "next" u S)
  then show ?case
    by (auto intro: trm_ord_reduction_left[rule_format])
next
  case (5 x y "next" u S)
  then show ?case
    by (auto intro: trm_ord_reduction_right[rule_format])
qed simp_all

lemma mset_cl_minus_plus:
  assumes fin_P: "finite P" and L_in_P: "L \<in> P"
  shows "mset_cl (P - {L}, \<sigma>) + mset_cl ({L}, \<sigma>) = mset_cl (P, \<sigma>)"
  using L_in_P
  using add_mset_image_mset_mset_set_minus[OF fin_P L_in_P]
  by force

lemma superposition_conclusion_smaller:
  assumes super_C': "superposition P1 P2 C \<sigma> Ground C'" and
    fin_P1: "finite (cl_ecl P1)" and
    fin_P2: "finite (cl_ecl P2)" and
    total_trm_ord: "Relation.total_on
      (\<Union>(case_equation (\<lambda>t1 t2. {t1, t2}) ` atom ` cl_ecl P2)) trm_ord"
  shows "((C', \<sigma>), (cl_ecl P1, \<sigma>)) \<in> cl_ord"
proof -
  from super_C' obtain L1 t s u v L2 p polarity t' u' where
    L1_in_P1: "L1 \<in> cl_ecl P1" and
    L2_in_P2: "L2 \<in> cl_ecl P2" and
    "eligible_literal L1 P1 \<sigma>" and
    "eligible_literal L2 P2 \<sigma>" and
    "variable_disjoint P1 P2" and
    "\<not> is_a_variable u'" and
    orient_L2: "orient_lit_inst L2 u v pos \<sigma>" and
    orient_L1: "orient_lit_inst L1 t s polarity \<sigma>" and
    u_neq_v: "u \<lhd> \<sigma> \<noteq> v \<lhd> \<sigma>" and
    subterm_t_p: "subterm t p u'" and
    ck_unif_u'_u: "ck_unifier u' u \<sigma> Ground" and
    replace_t_v: "replace_subterm t p v t'" and
    L2_lt_L1: "(subst_lit L2 \<sigma>, subst_lit L1 \<sigma>) \<in> lit_ord" and
    L2_max_P2: "strictly_maximal_literal P2 L2 \<sigma>" and
    C'_def: "C' = cl_ecl P1 - {L1} \<union> (cl_ecl P2 - {L2} \<union> {mk_lit polarity (Eq t' s)})"
    unfolding superposition_def
    by blast

  have
    "u \<in> case_equation (\<lambda>t1 t2. {t1, t2}) (atom L2)" and
    "v \<in> case_equation (\<lambda>t1 t2. {t1, t2}) (atom L2)"
    using orient_L2 by (auto simp: orient_lit_inst_def)
  hence
    u_in_P2: "u \<in> \<Union>(case_equation (\<lambda>t1 t2. {t1, t2}) ` atom ` cl_ecl P2)" and
    v_in_P2: "v \<in> \<Union>(case_equation (\<lambda>t1 t2. {t1, t2}) ` atom ` cl_ecl P2)"
    using L2_in_P2 by blast+

  have trm_ord_v_u: "(v \<lhd> \<sigma>, u \<lhd> \<sigma>) \<in> trm_ord"
    using orient_L2[unfolded orient_lit_inst_def]
    apply simp
    using total_trm_ord[unfolded Relation.total_on_def, rule_format, OF u_in_P2 v_in_P2]
    using u_neq_v
    using trm_ord_subst by blast

  have "(t \<lhd> \<sigma>, s \<lhd> \<sigma>) \<notin> trm_ord"
    using orient_L1[unfolded orient_lit_inst_def] by blast

  have u_eq_u': "u \<lhd> \<sigma> = u' \<lhd> \<sigma>"
    using ck_unif_u'_u by (simp add: ck_unifier_conv Unifier_def)

  have t'_lt_t:  "(t' \<lhd> \<sigma>, t \<lhd> \<sigma>) \<in> trm_ord"
    by (rule replacement_monotonic[OF trm_ord_v_u[unfolded u_eq_u'] subterm_t_p replace_t_v])

  define L where
    "L \<equiv> mk_lit polarity (Eq t' s)"

  have *: "(mset_lit (subst_lit L \<sigma>), mset_lit (subst_lit L1 \<sigma>)) \<in> mult trm_ord"
    using orient_L1[unfolded orient_lit_inst_def]
  proof (elim disjE conjE)
    assume "polarity = pos" and "L1 = equational_clausal_logic.literal.Pos (Eq t s)"
    thus ?thesis
      using t'_lt_t L_def
      by (auto intro: one_step_implies_mult[of "{#t \<lhd> \<sigma>#}" "{#t' \<lhd> \<sigma>#}" _ "{#s \<lhd> \<sigma>#}", simplified])
  next
    assume "polarity = pos" and "L1 = equational_clausal_logic.literal.Pos (Eq s t)"
    thus ?thesis
      using t'_lt_t L_def
      by (auto simp add: add_mset_commute
          intro: one_step_implies_mult[of "{#t \<lhd> \<sigma>#}" "{#t' \<lhd> \<sigma>#}" _ "{#s \<lhd> \<sigma>#}", simplified])
  next
    assume "polarity = neg" and "L1 = equational_clausal_logic.literal.Neg (Eq t s)"
    thus ?thesis
      using t'_lt_t L_def
      by (auto intro: one_step_implies_mult[of "{#t \<lhd> \<sigma>, t \<lhd> \<sigma>#}" "{#t' \<lhd> \<sigma>, t' \<lhd> \<sigma>#}" _
            "{#s \<lhd> \<sigma>, s \<lhd> \<sigma>#}", simplified])
  next
    assume "polarity = neg" and "L1 = equational_clausal_logic.literal.Neg (Eq s t)"
    thus ?thesis
      using t'_lt_t L_def
      by (auto simp add: add_mset_commute
          intro: one_step_implies_mult[of "{#t \<lhd> \<sigma>, t \<lhd> \<sigma>#}" "{#t' \<lhd> \<sigma>, t' \<lhd> \<sigma>#}" _
            "{#s \<lhd> \<sigma>, s \<lhd> \<sigma>#}", simplified])
  qed

  have foo:
    "mset_set (cl_ecl P1 - {L1} \<union> (cl_ecl P2 - {L2} \<union> {L})) =
      mset_set (cl_ecl P1 - {L1}) +
      mset_set (cl_ecl P1 - {L1} \<union> (cl_ecl P2 - {L2} \<union> {L}) - (cl_ecl P1 - {L1}))"
    by (smt (verit, best) Diff_disjoint Un_Diff_cancel Un_absorb Un_commute Un_left_commute fin_P1
        fin_P2 finite.emptyI finite.insertI finite_Diff finite_UnI mset_set_Union)

  have mset_set_insert_minusI: "\<And>P a A B. P a \<Longrightarrow> (\<forall>x\<in>#mset_set (A - B). P x) \<Longrightarrow>
    (\<forall>x\<in>#mset_set (insert a A - B). P x)"
    by (metis finite_insert finite_set_mset_mset_set infinite_set_mset_mset_set insertE insert_Diff_if)
  have union_minus_conv: "\<And>A B. (A \<union> B) - A = B - A"
    by blast

  have **: "\<forall>k \<in># mset_set (cl_ecl P2 - {L2}).
    (mset_lit (subst_lit k \<sigma>), mset_lit (subst_lit L1 \<sigma>)) \<in> mult trm_ord"
  proof (intro ballI)
    fix LL
    assume "LL \<in># mset_set (cl_ecl P2 - {L2})"
    hence "(subst_lit LL \<sigma>, subst_lit L2 \<sigma>) \<in> lit_ord" 
      using L2_max_P2
      unfolding strictly_maximal_literal_def
      by (metis elem_mset_set fin_P2 finite_Diff)
    hence "(subst_lit LL \<sigma>, subst_lit L1 \<sigma>) \<in> lit_ord"
      using L2_lt_L1
      using lit_ord_trans[THEN transD]
      by blast
    thus "(mset_lit (subst_lit LL \<sigma>), mset_lit (subst_lit L1 \<sigma>)) \<in>  mult trm_ord"
      unfolding lit_ord_def by auto
  qed

  show ?thesis
     unfolding C'_def
    apply (fold L_def)
    unfolding cl_ord_def
    apply (simp del: mset_cl.simps)
    unfolding mset_cl_minus_plus[OF fin_P1 L1_in_P1, symmetric]
    unfolding mset_cl.simps
    unfolding insert_is_Un[of L "cl_ecl P1 - {L1} \<union> (cl_ecl P2 - {L2})"]
    unfolding Un_commute[of "{L}"]
    unfolding Un_assoc
    unfolding foo
    unfolding image_mset_union
    apply (rule one_step_implies_mult)
     apply simp
    apply simp
    apply (rule mset_set_insert_minusI)
     apply (rule "*")
    unfolding union_minus_conv
    using **
    by (simp add: fin_P2)
qed

lemma subterms_inclusion_empty[simp]: "subterms_inclusion {} T"
  by (simp add: subterms_inclusion_def)

lemma clset_instances_union:
  "clset_instances (S1 \<union> S2) = clset_instances S1 \<union> clset_instances S2"
  by (auto simp add: clset_instances_def)

lemma ground_clause_subset: "C2 \<subseteq> C1 \<Longrightarrow> ground_clause C1 \<Longrightarrow> ground_clause C2"
  by auto

lemma ground_clause_union: "ground_clause C1 \<Longrightarrow> ground_clause C2 \<Longrightarrow> ground_clause (C1 \<union> C2)"
  by auto

term "(\<lambda>eq. case eq of Eq t1 t2 \<Rightarrow> vars_of t1 \<union> vars_of t2) ` atom ` L"
term "\<Union>((\<lambda>eq. case eq of Eq t1 t2 \<Rightarrow> vars_of t1 \<union> vars_of t2) ` atom ` L) = {}"

lemma ground_clause_lit:
  assumes "ground_clause C" and "L \<in> C"
  shows "vars_of_lit L = {}"
  using assms by auto

lemma ground_clause_reflexion:
  assumes refl_P1: "reflexion P1 C \<sigma> k C'" and ground_P1: "ground_clause (cl_ecl P1)"
  shows "ground_clause C'"
  apply (rule ground_clause_subset[OF _ ground_P1])
  using refl_P1
  by (auto simp: reflexion_def)

lemma ground_clause_factorization:
  assumes fact_P1: "factorization P1 C \<sigma> k C'" and ground_P1: "ground_clause (cl_ecl P1)"
  shows "ground_clause C'"
proof -
  from fact_P1[unfolded factorization_def] obtain L1 L2 t s u v where
    L1_in_P1: "L1 \<in> cl_ecl P1" and
    L2_in_P1: "L2 \<in> cl_ecl P1 - {L1}" and
    L1_t_s: "orient_lit_inst L1 t s pos \<sigma>" and
    L2_u_v: "orient_lit_inst L2 u v pos \<sigma>" and
    C'_def: "C' = cl_ecl P1 - {L2} \<union> {equational_clausal_logic.literal.Neg (Eq s v)}"
    by auto

  have ground_P1_less_lit: "ground_clause (cl_ecl P1 - {L})" for L
    by (rule ground_clause_subset[OF _ ground_P1]) simp

  show ?thesis
    unfolding C'_def
  proof (rule ground_clause_union)
    show "ground_clause (cl_ecl P1 - {L2})"
      by (rule ground_P1_less_lit)
  next
    have "vars_of s = {}"
      using orient_lit_inst_vars[OF L1_t_s]
      unfolding ground_clause_lit[OF ground_P1 L1_in_P1]
      by simp
    moreover have "vars_of v = {}"
      using orient_lit_inst_vars[OF L2_u_v]
      unfolding ground_clause_lit[OF ground_P1_less_lit L2_in_P1]
      by simp
    ultimately show "ground_clause {equational_clausal_logic.literal.Neg (Eq s v)}"
      by simp
  qed
qed

lemma ground_clause_superposition:
  assumes super_P1_P2: "superposition P1 P2 C \<sigma> k C'" and
    ground_P1: "ground_clause (cl_ecl P1)" and
    ground_P2: "ground_clause (cl_ecl P2)"
  shows "ground_clause C'"
proof -
  from super_P1_P2[unfolded superposition_def] obtain L1 L2 polarity t s u v p t' where
    L1_in_P1: "L1 \<in> cl_ecl P1" and
    L2_in_P2: "L2 \<in> cl_ecl P2" and
    L1_t_s: "orient_lit_inst L1 t s polarity \<sigma>" and
    L2_u_v: "orient_lit_inst L2 u v pos \<sigma>" and
    replace_t: "replace_subterm t p v t'" and
    C'_def: "C' = cl_ecl P1 - {L1} \<union> (cl_ecl P2 - {L2} \<union> {mk_lit polarity (Eq t' s)})"
    by blast

  show ?thesis
    unfolding C'_def
  proof (intro ground_clause_union)
    show "ground_clause (cl_ecl P1 - {L1})"
      using ground_P1
      by (auto intro: ground_clause_subset)
  next
    show "ground_clause (cl_ecl P2 - {L2})"
      using ground_P2
      by (auto intro: ground_clause_subset)
  next
    have "vars_of u = {}" and "vars_of v = {}"
      using orient_lit_inst_vars[OF L2_u_v]
      using ground_clause_lit[OF ground_P2 L2_in_P2]
      by simp_all
    have "vars_of t = {}" and "vars_of s = {}"
      using orient_lit_inst_vars[OF L1_t_s]
      using ground_clause_lit[OF ground_P1 L1_in_P1]
      by simp_all
    moreover hence "vars_of t' = {}"
      using replace_t \<open>vars_of v = {}\<close>
      by (induction t p v t' rule: replace_subterm.induct) auto
    ultimately show "ground_clause {mk_lit polarity (Eq t' s)}"
      by (cases polarity) simp_all
  qed
qed

lemma cl_ord_ground_subst:
  "((C, \<sigma>), D, \<sigma>) \<in> cl_ord \<Longrightarrow> ground_clause C \<Longrightarrow> ground_clause D \<Longrightarrow> ((C, \<delta>), D, \<delta>) \<in> cl_ord"
  by (smt (verit, best) case_prodD case_prodI cl_ord_def equal_image_mset mem_Collect_eq
      mset_cl.simps substs_preserve_ground_lit)

lemma ground_clause_imp_ground_term:
  assumes ground_C: "ground_clause C"
  shows "t \<in> \<Union> (case_equation (\<lambda>t1 t2. {t1, t2}) ` atom ` C) \<Longrightarrow> ground_term t"
  unfolding UN_iff
proof (elim bexE)
  fix eq
  assume eq_in: "eq \<in> atom ` C" and t_in: "t \<in> (case eq of Eq t1 t2 \<Rightarrow> {t1, t2})"
  from eq_in have "vars_of_eq eq = {}"
    unfolding image_iff
    apply safe
    using ground_C[unfolded ground_clause.simps vars_of_cl.simps]
    by (metis (no_types, lifting) atom.simps(1) atom.simps(2) empty_iff mem_Collect_eq subset_eq
        vars_of_lit.elims)
  with t_in show "ground_term t"
    by (cases eq) (auto simp: ground_term_def)
qed

lemma trm_ord_total_on_ground_clause:
  assumes ground_C: "ground_clause C"
  shows "Relation.total_on (\<Union>(case_equation (\<lambda>t1 t2. {t1, t2}) ` atom ` C)) trm_ord"
    apply (rule Relation.total_onI)
    apply (erule trm_ord_ground_total[rule_format, rotated 2])
    by (auto intro: ground_clause_imp_ground_term[OF ground_C])

end


subsection \<open>Prover\<close>

primrec to_SuperCalc_lit
  :: "'a equation Clausal_Logic.literal \<Rightarrow> 'a equational_clausal_logic.literal" where
  "to_SuperCalc_lit (Clausal_Logic.Pos a) = equational_clausal_logic.Pos a" |
  "to_SuperCalc_lit (Clausal_Logic.Neg a) = equational_clausal_logic.Neg a"

lemma inj_to_SuperCalc_lit: "inj to_SuperCalc_lit"
proof (rule injI)
  fix L1 L2 :: "'a equation Clausal_Logic.literal"
  show "to_SuperCalc_lit L1 = to_SuperCalc_lit L2 \<Longrightarrow> L1 = L2"
    by (cases L1; cases L2; simp)
qed

primrec from_SuperCalc_lit
  :: "'a equational_clausal_logic.literal \<Rightarrow> 'a equation Clausal_Logic.literal" where
  "from_SuperCalc_lit (equational_clausal_logic.Pos a) = Clausal_Logic.Pos a" |
  "from_SuperCalc_lit (equational_clausal_logic.Neg a) = Clausal_Logic.Neg a"

lemma to_from_SuperCalc_lit[simp]: "to_SuperCalc_lit (from_SuperCalc_lit L) = L"
  by (cases L) simp_all

lemma inj_from_SuperCalc_lit[simp]: "inj from_SuperCalc_lit"
proof (rule injI)
  fix L1 L2 :: "'a equational_clausal_logic.literal"
  assume "from_SuperCalc_lit L1 = from_SuperCalc_lit L2"
  thus "L1 = L2"
    by (cases L1; cases L2; simp)
qed

definition to_SuperCalc_cl
  :: "'a equation Clausal_Logic.clause \<Rightarrow> 'a equational_clausal_logic.clause" where
  "to_SuperCalc_cl C \<equiv> to_SuperCalc_lit ` (set_mset C)"

lemma to_SuperCalc_cl_eq_conv: "to_SuperCalc_cl C = to_SuperCalc_cl D \<longleftrightarrow> set_mset C = set_mset D"
  unfolding to_SuperCalc_cl_def
  by (rule inj_image_eq_iff[OF inj_to_SuperCalc_lit])

lemma to_SuperCalc_cl_empty_mset[simp]: "to_SuperCalc_cl {#} = {}"
  by (simp add: to_SuperCalc_cl_def)

lemma finite_to_SuperCalc_cl[simp]: "finite (to_SuperCalc_cl C)"
  by (simp add: to_SuperCalc_cl_def)

definition from_SuperCalc_cl
  :: "'a equational_clausal_logic.clause \<Rightarrow> 'a equation Clausal_Logic.clause" where
  "from_SuperCalc_cl C \<equiv> image_mset from_SuperCalc_lit (mset_set C)"

lemma from_SuperCalc_cl_eq_mempty: "finite C \<Longrightarrow> from_SuperCalc_cl C = {#} \<longleftrightarrow> C = {}"
  by (simp add: from_SuperCalc_cl_def mset_set_empty_iff)

lemma to_from_SuperCalc_cl[simp]:
  "finite C \<Longrightarrow> to_SuperCalc_cl (from_SuperCalc_cl C) = C"
  by (simp add: to_SuperCalc_cl_def from_SuperCalc_cl_def image_image)

abbreviation to_SuperCalc_ecl where
  "to_SuperCalc_ecl C \<equiv> Ecl (to_SuperCalc_cl C) {}"

lemma cl_ecl_comp_to_SuperCalc_ecl_conv[simp]: "cl_ecl \<circ> to_SuperCalc_ecl = to_SuperCalc_cl"
  by auto

sledgehammer_params

locale superposition_prover =
    substitution_renamings subst_equation "[]" Unification.comp renamings_apart
  for
    renamings_apart :: "'a equation Clausal_Logic.clause list \<Rightarrow> 'a subst list" +
  fixes
    \<comment> \<open>For SuperCalc\<close>
    trm_ord :: "('a trm \<times> 'a trm) set" and
    select :: "'a literal set \<Rightarrow> 'a literal set" and

    \<comment> \<open>Voir si pos_ord influence SuperCalc.derivable. Si oui, garder comme paramètre. Sinon, mettre
    quelque chose de bidon\<close>
    pos_ord :: "'a eclause \<Rightarrow> 'a trm \<Rightarrow> (indices list \<times> indices list) set"
  assumes
    trm_ord_wf: "wf trm_ord" and
    trm_ord_total_on_ground: "Relation.total_on {t. ground_term t} trm_ord" and
    trm_ord_trans: "trans trm_ord" and
    trm_ord_irrefl:  "irrefl trm_ord" and
    trm_ord_reduction_left:
      "\<forall>x1 x2 y. (x1,x2)  \<in> trm_ord \<longrightarrow> ((Comb x1 y),(Comb x2 y)) \<in> trm_ord" and
    trm_ord_reduction_right:
      "\<forall>x1 x2 y. (x1,x2)  \<in> trm_ord \<longrightarrow> ((Comb y x1),(Comb y x2)) \<in> trm_ord" and
    trm_ord_subterm: "\<forall>x1 x2. (x1, Comb x1 x2)  \<in> trm_ord \<and> (x2, Comb x1 x2) \<in> trm_ord" and
    trm_ord_subst: "\<forall>s x y. (x, y) \<in> trm_ord \<longrightarrow> (subst x s, subst y s) \<in> trm_ord" and
    pos_ord_irrefl: "\<forall>x y. irrefl (pos_ord x y)" and
    pos_ord_trans: "\<forall>x y. trans (pos_ord x y)" and
    pos_ord_prefix: "\<forall>x y p q r. (q, p) \<in> pos_ord x y \<longrightarrow> (q @ r, p) \<in> pos_ord x y" and
    pos_ord_nil: "\<forall>x y p . p \<noteq> [] \<longrightarrow> (p, []) \<in> pos_ord x y" and
    select_neg: "(\<forall>C. select C \<subseteq> C \<and> (\<forall>L \<in> select C. negative_literal L))" and
    select_renaming: "\<forall>\<eta> C. renaming \<eta> (vars_of_cl C) \<longrightarrow> select C = {} \<longrightarrow> select (subst_cl C \<eta>) = {}" and
    infinite_vars: "infinite (UNIV :: 'a set)"
begin

text \<open>
These simplification rules often hurt more than they help.
Better to remove it and selectively add them tho @{method simp} when necessary.
\<close>

lemmas [simp del] = equational_clausal_logic.ground_clause.simps
lemmas [simp del] = equational_clausal_logic.subst_cl.simps
lemmas [simp del] = equational_clausal_logic.validate_ground_clause.simps
lemmas [simp del] = terms.subst_set.simps

lemma subst_set_empty[simp]: "subst_set {} \<sigma> = {}"
  by (simp add: subst_set.simps)

lemma to_SuperCalc_cl_subst_cls: "to_SuperCalc_cl (subst_cls C \<sigma>) = subst_cl (to_SuperCalc_cl C) \<sigma>"
  (is "?lhs = ?rhs")
proof -
  have "to_SuperCalc_lit (local.subst_lit L \<sigma>) =
    equational_clausal_logic.subst_lit (to_SuperCalc_lit L) \<sigma>" for L
    by (cases L) (simp_all add: subst_lit_def)
  moreover have "?lhs = to_SuperCalc_lit ` (\<lambda>A. local.subst_lit A \<sigma>) ` set_mset C"
    unfolding subst_cls_def to_SuperCalc_cl_def
    by simp
  moreover have "?rhs = (\<lambda>x. equational_clausal_logic.subst_lit (to_SuperCalc_lit x) \<sigma>) ` set_mset C"
    unfolding to_SuperCalc_cl_def
    by (auto simp add: setcompr_eq_image subst_cl.simps)
  ultimately show "?lhs = ?rhs"
    by (simp add: image_image)
qed

subsubsection \<open>Ground selection at an Arbitrary Limit\<close>

definition ground_select :: "'a clause set \<Rightarrow> 'a clause \<Rightarrow> 'a clause" where
  "ground_select M C =
    (if C \<in> (\<Union>D \<in> M. {subst_cl D \<sigma> | \<sigma>. ground_clause (subst_cl D \<sigma>)}) then
      (SOME C'. \<exists>D \<in> M. \<exists>\<sigma>. C = subst_cl D \<sigma> \<and> ground_clause (subst_cl D \<sigma>) \<and>
        C' = subst_cl (select D) \<sigma>)
    else
      select C)"

lemma ground_select_at_limit_grounding:
  assumes "C \<in> (\<Union>D \<in> M. {subst_cl D \<sigma> | \<sigma>. ground_clause (subst_cl D \<sigma>)})"
  shows "\<exists>D \<in> M. \<exists>\<sigma>. C = subst_cl D \<sigma> \<and> ground_clause (subst_cl D \<sigma>) \<and>
    ground_select M C = subst_cl (select D) \<sigma>"
  unfolding ground_select_def eqTrueI[OF assms] if_True
proof (rule someI_ex)
  from assms show "\<exists>D'. \<exists>D\<in>M. \<exists>\<sigma>. C = subst_cl D \<sigma> \<and> ground_clause (subst_cl D \<sigma>) \<and>
    D' = subst_cl (select D) \<sigma>"
    by blast
qed

lemma ground_select_at_limit_not_grounding:
  assumes "C \<notin> (\<Union>D \<in> M. {subst_cl D \<sigma> | \<sigma>. ground_clause (subst_cl D \<sigma>)})"
  shows "ground_select M C = select C"
  unfolding ground_select_def
  using assms by argo

lemma ground_select_subset: "ground_select M C \<subseteq> C"
proof (rule subsetI)
  fix L :: "'a literal"
  assume L_in: "L \<in> ground_select M C"
  show "L \<in> C"
  proof (cases "C \<in> (\<Union>D \<in> M. {subst_cl D \<sigma> | \<sigma>. ground_clause (subst_cl D \<sigma>)})")
    case True
    show ?thesis
      using L_in ground_select_at_limit_grounding[OF True]
      using select_neg[rule_format, THEN conjunct1]
      by (smt (verit) Collect_mono_iff subsetD subst_cl.simps)
  next
    case False
    then show ?thesis
      using L_in
      by (metis (no_types, lifting) ground_select_def select_neg subsetD)
  qed
qed

lemma ground_select_negative_literal:
  assumes L_in_grsel_M_C: "L \<in> ground_select M C"
  shows "negative_literal L"
proof (cases "C \<in> (\<Union>D\<in>M. {subst_cl D \<sigma> |\<sigma>. ground_clause (subst_cl D \<sigma>)})")
  case True
  obtain D :: "'a clause" and \<sigma> :: "'a subst" where
    D_in: "D \<in> M" and
    C_conv: "C = subst_cl D \<sigma>" and
    ground_D_\<sigma>: "ground_clause (subst_cl D \<sigma>)" and
    grsel_M_C_conv: "ground_select M C = subst_cl (select D) \<sigma>"
    using ground_select_at_limit_grounding[OF True] by blast
  from L_in_grsel_M_C and grsel_M_C_conv have "L \<in> subst_cl (select D) \<sigma>" by simp
  then obtain L' where "L' \<in> select D" and "L = equational_clausal_logic.subst_lit L' \<sigma>"
    by (smt (verit, ccfv_SIG) mem_Collect_eq subst_cl.simps)
  thus ?thesis
    using select_neg by simp
next
  case False
  then show ?thesis
    using assms
    by (metis (no_types, lifting) ground_select_def select_neg)
qed


subsubsection \<open>Ground SuperCalc at an Arbitrary Limit\<close>

interpretation G_SuperCalc: basic_superposition trm_ord "ground_select M" pos_ord "UNIV :: 'a set" "\<lambda>_ _. {}"
  using trm_ord_wf trm_ord_trans trm_ord_irrefl trm_ord_reduction_left trm_ord_reduction_right
    trm_ord_subterm trm_ord_subst pos_ord_irrefl pos_ord_prefix pos_ord_nil infinite_vars
proof unfold_locales
  show "\<forall>x y. ground_term x \<longrightarrow> ground_term y \<longrightarrow> x \<noteq> y \<longrightarrow> (x, y) \<in> trm_ord \<or> (y, x) \<in> trm_ord"
    using trm_ord_total_on_ground by (simp add: Relation.total_on_def)
next
  fix y :: "'a trm"
  show "\<forall>x. trans (pos_ord x y)"
    using pos_ord_trans by simp
next
  show "\<forall>x. ground_select M (cl_ecl x) \<subseteq> cl_ecl x \<and>
    (\<forall>y\<in>ground_select M (cl_ecl x). negative_literal y)"
    using ground_select_subset ground_select_negative_literal
    by simp
next
  show "\<forall>\<eta> C. renaming \<eta> (vars_of_cl C) \<longrightarrow> ground_select M C = {} \<longrightarrow>
    ground_select M (subst_cl C \<eta>) = {}"
  proof (intro allI impI)
    fix \<eta> :: "'a subst" and C :: "'a clause"
    assume renaming_\<eta>: "renaming \<eta> (vars_of_cl C)" and grsel_M_C: "ground_select M C = {}"
    show "ground_select M (subst_cl C \<eta>) = {}"
    proof (cases "C \<in> (\<Union>D\<in>M. {subst_cl D \<sigma> |\<sigma>. ground_clause (subst_cl D \<sigma>)})")
      case True
      with grsel_M_C show ?thesis
        by (auto simp: substs_preserve_ground_clause)
    next
      case False
      note C_not_in = this
      with grsel_M_C have "select C = {}"
        using ground_select_at_limit_not_grounding by simp
      hence "select (subst_cl C \<eta>) = {}"
        by (rule select_renaming[rule_format, OF renaming_\<eta>])
      moreover have "subst_cl C \<eta> \<notin> (\<Union>D\<in>M. {subst_cl D \<sigma> |\<sigma>. ground_clause (subst_cl D \<sigma>)})"
      proof (cases "ground_clause C")
        case True
        thus ?thesis
          using C_not_in by (simp add: substs_preserve_ground_clause)
      next
        case False
        with renaming_\<eta> have "\<not> ground_clause (subst_cl C \<eta>)"
          by (simp add: ground_clause_subst_renaming)
        then show ?thesis
          by fastforce
      qed
      ultimately show ?thesis
        unfolding ground_select_def
        by argo
    qed
  qed
next
  fix E
  show "{} \<subseteq> E"
    by simp
qed assumption+

lemmas [simp del] = G_SuperCalc.trm_rep.simps

definition G_derivable_list where
  "G_derivable_list M C Ps \<sigma> k C' \<longleftrightarrow>
    (\<exists>P1. \<exists>P2. Ps = [P2, P1] \<and> G_SuperCalc.superposition M P1 P2 C \<sigma> k C') \<or>
    (\<exists>P1. Ps = [P1] \<and> G_SuperCalc.factorization M P1 C \<sigma> k C') \<or>
    (\<exists>P1. Ps = [P1] \<and> G_SuperCalc.reflexion M P1 C \<sigma> k C')"

lemma G_derivable_list_imp_derivable:
  "G_derivable_list M C Ps \<sigma> k C' \<Longrightarrow> set Ps \<subseteq> S \<Longrightarrow> G_SuperCalc.derivable M C (set Ps) S \<sigma> k C'"
  unfolding G_derivable_list_def G_SuperCalc.derivable_def
  by (auto simp: insert_commute)

lemma G_derivable_list_non_empty_premises: "G_derivable_list M C Ps \<sigma> k C' \<Longrightarrow> Ps \<noteq> []"
  by (auto simp add: G_derivable_list_def)

lemma G_derivable_list_ground_premises:
  assumes "\<forall>C \<in> set Ps. ground_clause (cl_ecl C)" and "G_derivable_list M C Ps \<sigma> k C'"
  shows "ground_clause C'"
  using assms
  by (auto simp: G_derivable_list_def
      intro: G_SuperCalc.ground_clause_reflexion
             G_SuperCalc.ground_clause_factorization
             G_SuperCalc.ground_clause_superposition)

lemma G_derivable_list_finite_conclusion:
  "\<forall>C\<in>set Ps. finite (cl_ecl C) \<Longrightarrow> G_derivable_list M C Ps \<sigma> k C' \<Longrightarrow> finite C'"
  using G_SuperCalc.derivable_finite_conclusion[OF _ G_derivable_list_imp_derivable]
  by blast

lemma G_derivable_list_concl_conv:
  "G_derivable_list M C Ps \<sigma> k C' \<Longrightarrow> cl_ecl C = subst_cl C' \<sigma>"
  unfolding G_derivable_list_def G_SuperCalc.derivable_def
  by (auto simp: G_SuperCalc.reflexion_def G_SuperCalc.factorization_def
      G_SuperCalc.superposition_def)


subsubsection \<open>Ground calculus\<close>

definition G_Inf :: "'a equational_clausal_logic.clause set \<Rightarrow>
  'a equation Clausal_Logic.clause inference set" where
  "G_Inf M \<equiv> {Infer Ps (from_SuperCalc_cl (subst_cl C' \<sigma>)) | Ps C \<sigma> C'.
    (\<forall>D \<in> set Ps. ground_clause (to_SuperCalc_cl D)) \<and>
    G_derivable_list M C (map to_SuperCalc_ecl Ps) \<sigma> G_SuperCalc.Ground C'}"

lemma G_Inf_have_prems: "\<iota> \<in> G_Inf M \<Longrightarrow> prems_of \<iota> \<noteq> []"
  by (auto simp: G_Inf_def G_derivable_list_def)

lemma G_Inf_ground_concl: "\<iota> \<in> G_Inf M \<Longrightarrow> ground_clause (to_SuperCalc_cl (concl_of \<iota>))"
  unfolding G_Inf_def mem_Collect_eq
  apply safe
  apply simp
  apply (frule G_derivable_list_ground_premises[rotated])
   apply simp
  unfolding substs_preserve_ground_clause
  using G_derivable_list_finite_conclusion[THEN to_from_SuperCalc_cl, rotated]
  by simp

definition fclause_ord
  :: "'a equation Clausal_Logic.clause \<Rightarrow> 'a equation Clausal_Logic.clause \<Rightarrow> bool"
  where
  "fclause_ord C D \<equiv> ((to_SuperCalc_cl C, []), (to_SuperCalc_cl D, [])) \<in> G_SuperCalc.cl_ord"

lemma transp_fclause_ord: "transp fclause_ord"
  unfolding fclause_ord_def
  by (auto intro: transpI G_SuperCalc.cl_ord_trans[THEN transD])

lemma wfP_fclause_ord: "wfP fclause_ord"
  unfolding fclause_ord_def wfP_def
  by (rule compat_wf[of _ _ "\<lambda>C. (to_SuperCalc_cl C, [])", OF _ G_SuperCalc.wf_cl_ord])
    (simp add: compat_def)

lemma G_Inf_reductive:
  assumes \<iota>_in: "\<iota> \<in> G_Inf M"
  shows "fclause_ord (concl_of \<iota>) (main_prem_of \<iota>)"
proof -
  from \<iota>_in[unfolded G_Inf_def mem_Collect_eq] obtain Ps C \<sigma> C' where
    \<iota>_def: "\<iota> = Infer Ps (from_SuperCalc_cl (subst_cl C' \<sigma>))" and
    Ps_ground: "\<forall>C \<in> set Ps. ground_clause (to_SuperCalc_cl C)" and
    deriv_Ps: "G_derivable_list M C (map to_SuperCalc_ecl Ps) \<sigma> G_SuperCalc.Ground C'"
    by blast

  have Ps_ground': "\<forall>C \<in> set (map to_SuperCalc_ecl Ps). ground_clause (cl_ecl C)"
    using Ps_ground by simp

  have ground_C': "ground_clause C'"
    by (rule G_derivable_list_ground_premises[OF Ps_ground' deriv_Ps])

  have "fclause_ord (from_SuperCalc_cl C') (last Ps)"
    using deriv_Ps[unfolded G_derivable_list_def]
  proof (elim disjE exE conjE)
    fix P1
    assume map_Ps_conv: "map to_SuperCalc_ecl Ps = [P1]" and
      refl_P1: "G_SuperCalc.reflexion M P1 C \<sigma> G_SuperCalc.Ground C'"
    
    from map_Ps_conv have fin_P1: "finite (cl_ecl P1)"
      by force

    from map_Ps_conv have ground_P1: "ground_clause (cl_ecl P1)"
      using Ps_ground' by simp

    from map_Ps_conv have last_Ps_conv: "to_SuperCalc_cl (last Ps) = cl_ecl P1"
      by force

    from fin_P1 refl_P1 have fin_C': "finite C'"
      using G_SuperCalc.reflexion_preserves_finiteness
      by blast

    show ?thesis
      unfolding fclause_ord_def to_from_SuperCalc_cl[OF fin_C'] last_Ps_conv
      using G_SuperCalc.reflexion_conclusion_smaller[OF refl_P1 fin_P1]
      using ground_C' ground_P1
      by (auto elim: G_SuperCalc.cl_ord_ground_subst)
  next
    fix P1
    assume
      map_Ps_conv: "map to_SuperCalc_ecl Ps = [P1]" and
      fact_P1: "G_SuperCalc.factorization M P1 C \<sigma> G_SuperCalc.Ground C'"
    
    from map_Ps_conv have fin_P1: "finite (cl_ecl P1)"
      by force

    from map_Ps_conv have ground_P1: "ground_clause (cl_ecl P1)"
      using Ps_ground' by simp

    from map_Ps_conv have last_Ps_conv: "to_SuperCalc_cl (last Ps) = cl_ecl P1"
      by force

    from fin_P1 fact_P1 have fin_C': "finite C'"
      using G_SuperCalc.factorization_preserves_finiteness
      by blast

    show "fclause_ord (from_SuperCalc_cl C') (last Ps)"
      unfolding fclause_ord_def to_from_SuperCalc_cl[OF fin_C'] last_Ps_conv
      using G_SuperCalc.factorization_conclusion_smaller[OF fact_P1 fin_P1]
      using G_SuperCalc.trm_ord_total_on_ground_clause
      using ground_C' ground_P1
      by (auto elim: G_SuperCalc.cl_ord_ground_subst)
  next
    fix P1 P2
    assume
      map_Ps_conv: "map to_SuperCalc_ecl Ps = [P2, P1]" and
      super_P1_P2: "G_SuperCalc.superposition M P1 P2 C \<sigma> G_SuperCalc.Ground C'"

    from map_Ps_conv have fin_P1: "finite (cl_ecl P1)" and fin_P2: "finite (cl_ecl P2)"
      by force+

    from map_Ps_conv have
      ground_P1: "ground_clause (cl_ecl P1)" and
      ground_P2: "ground_clause (cl_ecl P2)"
      using Ps_ground' by simp_all

    from fin_P1 fin_P2 super_P1_P2 have fin_C': "finite C'"
      using G_SuperCalc.superposition_preserves_finiteness
      by blast

    from map_Ps_conv have last_Ps_conv: "to_SuperCalc_cl (last Ps) = cl_ecl P1"
      by force

    show "fclause_ord (from_SuperCalc_cl C') (last Ps)"
      unfolding fclause_ord_def to_from_SuperCalc_cl[OF fin_C'] last_Ps_conv
      using G_SuperCalc.superposition_conclusion_smaller[OF super_P1_P2 fin_P1 fin_P2]
      using G_SuperCalc.trm_ord_total_on_ground_clause
      using ground_C' ground_P1 ground_P2
      by (auto elim: G_SuperCalc.cl_ord_ground_subst)
  qed

  thus ?thesis
    by (simp add: \<iota>_def substs_preserve_ground_clause[OF ground_C'])
qed


definition entails :: "'a equation Clausal_Logic.clause set \<Rightarrow>
  'a equation Clausal_Logic.clause set \<Rightarrow> bool" (infix "\<TTurnstile>e" 50) where
  "N1 \<TTurnstile>e N2 \<equiv> set_entails_set (to_SuperCalc_cl ` N1) (to_SuperCalc_cl ` N2)"


interpretation G: consequence_relation "{{#}}" entails
proof unfold_locales
  show "{{#}} \<noteq> {}"
    by simp
next
  show "\<And>B N1. B \<in> {{#}} \<Longrightarrow> {B} \<TTurnstile>e N1"
    unfolding entails_def
    by (simp add: set_entails_set_def to_SuperCalc_cl_def subst_cl.simps
        ground_clause.simps validate_ground_clause.simps)
next
  show "\<And>N2 N1. N2 \<subseteq> N1 \<Longrightarrow> N1 \<TTurnstile>e N2"
    unfolding entails_def
    by (auto simp add: set_entails_set_def)
next
  show "\<And>N2 N1. \<forall>C\<in>N2. N1 \<TTurnstile>e {C} \<Longrightarrow> N1 \<TTurnstile>e N2"
    unfolding entails_def
    by (auto simp: set_entails_set_def)
next
  show "\<And>N1 N2 N3. N1 \<TTurnstile>e N2 \<Longrightarrow> N2 \<TTurnstile>e N3 \<Longrightarrow> N1 \<TTurnstile>e N3"
    unfolding entails_def
    using transp_set_entails_set[THEN transpD]
    by blast
qed

interpretation G: sound_inference_system "G_Inf M" "{{#}}" entails
proof unfold_locales
  fix \<iota> :: "'a equation Clausal_Logic.literal multiset inference"
  assume "\<iota> \<in> G_Inf M"
  then obtain P C \<sigma> C' where
    \<iota>_def: "\<iota> = Infer P (from_SuperCalc_cl (subst_cl C' \<sigma>))" and
    ball_P_ground: "\<forall>C\<in>set P. ground_clause (to_SuperCalc_cl C)" and
    deriv_P: "G_derivable_list M C (map to_SuperCalc_ecl P) \<sigma> G_SuperCalc.Ground C'"
    unfolding G_Inf_def mem_Collect_eq by blast

  from deriv_P have cl_ecl_C_conv: "cl_ecl C = subst_cl C' \<sigma>"
    by (simp add: G_derivable_list_concl_conv)

  have "finite (subst_cl C' \<sigma>)"
    apply (rule substs_preserve_finiteness)
    apply (rule G_derivable_list_finite_conclusion[OF _ deriv_P])
    by simp
  hence to_from_SuperCalc_cl_subst_C':
    "to_SuperCalc_cl (from_SuperCalc_cl (subst_cl C' \<sigma>)) = subst_cl C' \<sigma>"
    by simp

  have to_SuperCalc_cl_set_P_conv: "to_SuperCalc_cl ` set P = cl_ecl ` set (map to_SuperCalc_ecl P)"
    by (simp add: image_comp)

  from deriv_P show "set (prems_of \<iota>) \<TTurnstile>e {concl_of \<iota>}"
    unfolding G_derivable_list_def
  proof (elim disjE exE conjE)
    fix P1 P2
    assume
      map_P_conv: "map to_SuperCalc_ecl P = [P2, P1]" and
      super_P1_P2: "G_SuperCalc.superposition M P1 P2 C \<sigma> G_SuperCalc.Ground C'"
    hence "set_entails_clause {cl_ecl P1, cl_ecl P2} (cl_ecl C)"
      by (auto intro: G_SuperCalc.superposition_is_sound)
    then show "set (prems_of \<iota>) \<TTurnstile>e {concl_of \<iota>}"
      by (simp add: entails_def \<iota>_def cl_ecl_C_conv to_from_SuperCalc_cl_subst_C'
          to_SuperCalc_cl_set_P_conv[unfolded map_P_conv] insert_commute)
  next
    fix P1
    assume
      map_P_conv: "map to_SuperCalc_ecl P = [P1]" and
      fact_P1: "G_SuperCalc.factorization M P1 C \<sigma> G_SuperCalc.Ground C'"
    hence "clause_entails_clause (cl_ecl P1) (cl_ecl C)"
      by (auto intro: G_SuperCalc.factorization_is_sound)
    then show "set (prems_of \<iota>) \<TTurnstile>e {concl_of \<iota>}"
      by (simp add: entails_def \<iota>_def cl_ecl_C_conv to_from_SuperCalc_cl_subst_C'
          to_SuperCalc_cl_set_P_conv[unfolded map_P_conv])
  next
    fix P1
    assume
      map_P_conv: "map to_SuperCalc_ecl P = [P1]" and
      refl_P1: "G_SuperCalc.reflexion M P1 C \<sigma> G_SuperCalc.Ground C'"
    hence "clause_entails_clause (cl_ecl P1) (cl_ecl C)"
      by (auto intro: G_SuperCalc.reflexion_is_sound)
    then show "set (prems_of \<iota>) \<TTurnstile>e {concl_of \<iota>}"
      by (simp add: entails_def \<iota>_def cl_ecl_C_conv to_from_SuperCalc_cl_subst_C'
          to_SuperCalc_cl_set_P_conv[unfolded map_P_conv])
  qed
qed

interpretation G: calculus_with_finitary_standard_redundancy "G_Inf M" "{{#}}" "(\<TTurnstile>e)" fclause_ord
  using wfP_fclause_ord transp_fclause_ord G_Inf_have_prems G_Inf_reductive
  by (unfold_locales)

lemma
  assumes satur_N: "G.saturated M N"
  shows "G_SuperCalc.ground_inference_saturated M (to_SuperCalc_ecl ` N)"
  unfolding G_SuperCalc.ground_inference_saturated_def
proof (intro allI impI)
  from satur_N have red_inferI: "\<forall>\<iota>\<in>G_Inf M. set (prems_of \<iota>) \<subseteq> N \<longrightarrow> G.redundant_infer N \<iota>"
    unfolding G.saturated_def G.Inf_from_def G.Red_I_def
    unfolding set_filter_subset_set_filter_conv
    by assumption

  fix C P \<sigma> C'
  assume
    derivable_P: "G_SuperCalc.derivable M C P (to_SuperCalc_ecl ` N) \<sigma> G_SuperCalc.Ground C'" and
    ground_C: "ground_clause (cl_ecl C)" and
    grounding_P: "G_SuperCalc.grounding_set P \<sigma>"

  from derivable_P have "\<exists>Ps. set Ps = P \<and> G_derivable_list M C Ps \<sigma> G_SuperCalc.Ground C'"
    unfolding G_derivable_list_def
    unfolding G_SuperCalc.derivable_def
    apply safe
      apply (metis (full_types) insert_commute list.simps(15) set_empty2)
     apply (metis empty_set list.simps(15))
    by (metis list.simps(15) set_empty)
  then obtain Ps where "set Ps = P" and G_deriv_list: "G_derivable_list M C Ps \<sigma> G_SuperCalc.Ground C'"
    by blast
  then obtain Ps' where Ps_def: "Ps = map to_SuperCalc_ecl Ps'"
    by (smt (verit) G_SuperCalc.derivable_premisses derivable_P ex_map_conv imageE subsetD)

  let ?\<iota> = "Infer Ps' (from_SuperCalc_cl (subst_cl C' \<sigma>))"

  have gr_N: "\<forall>D\<in>N. ground_clause (to_SuperCalc_cl D)" sorry

  from derivable_P have "P \<subseteq> to_SuperCalc_ecl ` N"
    by (simp add: G_SuperCalc.derivable_premisses)

  then have "set Ps' \<subseteq> N"
    unfolding \<open>set Ps = P\<close>[symmetric] Ps_def
    apply simp
    using inj_image_subset_iff
    find_theorems "_ ` _ = _ ` _"
    sorry

  from gr_N have gr_Ps': "\<forall>D\<in>set Ps'. ground_clause (to_SuperCalc_cl D)"
    using \<open>set Ps' \<subseteq> N\<close>
    by blast

  have \<iota>_G_Inf: "?\<iota> \<in> G_Inf M"
    unfolding G_Inf_def
    apply simp
    apply (rule exI[where x = C])
    apply (rule exI[where x = \<sigma>])
    apply (rule exI[where x = C'])
    using G_deriv_list
    apply (simp add: Ps_def)
    using gr_Ps' by simp


  have FOO: "{C. \<exists>x\<in>DD \<union> set (butlast Ps'). C = to_SuperCalc_cl x} =
      to_SuperCalc_cl ` (DD \<union> set (butlast Ps'))" for DD
    by blast

  have BAR: "cl_ecl C = subst_cl C' \<sigma>"
    using G_deriv_list G_derivable_list_concl_conv by blast

  have BAZ: "to_SuperCalc_cl (from_SuperCalc_cl (subst_cl C' \<sigma>)) = subst_cl C' \<sigma>"
    apply (rule to_from_SuperCalc_cl)
    apply (rule substs_preserve_finiteness)
    apply (rule G_derivable_list_finite_conclusion[OF _ G_deriv_list])
    unfolding Ps_def
    by simp

  from red_inferI[rule_format, OF \<iota>_G_Inf, simplified, OF \<open>set Ps' \<subseteq> N\<close>,
      unfolded G.redundant_infer_def, simplified]
  obtain DD where "DD\<subseteq>N" and
     "finite DD" and
     "DD \<union> set (butlast Ps') \<TTurnstile>e {from_SuperCalc_cl (subst_cl C' \<sigma>)}" and
     ball_DD_lt: "(\<forall>D\<in>DD. fclause_ord D (last Ps'))"
    by auto

  then show "G_SuperCalc.redundant_inference C (to_SuperCalc_ecl ` N) P \<sigma>"
    unfolding G_SuperCalc.redundant_inference_def
    apply -
    apply (rule exI[where x = "(\<lambda>C. (C, [])) ` to_SuperCalc_ecl ` (DD \<union> set (butlast Ps'))"])
    apply (intro conjI)
    subgoal
      apply safe
      subgoal for _ _ _ D
        using gr_N
        unfolding G_SuperCalc.instances_def
        apply simp
        apply (rule bexI[where x = D])
        subgoal
          by simp
        subgoal
          by blast
        done
      subgoal for _ _ _ D
        using gr_N \<open>set Ps' \<subseteq> N\<close>
        unfolding G_SuperCalc.instances_def
        apply simp
        apply (rule bexI[where x = D])
         apply (simp add: in_set_butlastD)
        by (meson in_set_butlastD subsetD)
      done
    subgoal
      by (simp add: entails_def G_SuperCalc.clset_instances_def FOO BAR BAZ)
    subgoal
      by simp
    subgoal
      apply simp
      using gr_Ps'
      apply safe
      subgoal for D
        apply (rule bexI[where x = "to_SuperCalc_ecl (last Ps')"])
         apply simp
        using ball_DD_lt[rule_format, of D, unfolded fclause_ord_def]
         apply simp
        unfolding  G_SuperCalc.cl_ord_def
         apply simp
        oops

interpretation G: statically_complete_calculus "{{#}}" "G_Inf M" "(\<TTurnstile>e)" "G.Red_I M" G.Red_F
proof unfold_locales
  fix
    B :: "'a equation Clausal_Logic.clause" and
    N :: "'a equation Clausal_Logic.clause set"
  assume "B \<in> {{#}}" and "G.saturated M N" and "N \<TTurnstile>e {B}"
  hence B_def: "B = {#}" by simp

  from \<open>G.saturated M N\<close>
  have gr_inf_satur_N: "G_SuperCalc.ground_inference_saturated M (to_SuperCalc_ecl ` N)"
    sorry

  have all_finite_N: "\<forall>x\<in>to_SuperCalc_ecl ` N. finite (cl_ecl x)"
    by simp

  have Ball_well_constrained_N': "Ball (to_SuperCalc_ecl ` N) G_SuperCalc.well_constrained"
    by (simp add: G_SuperCalc.well_constrained_def)

  have closed_renaming_N: "closed_under_renaming (to_SuperCalc_ecl ` N)"
    unfolding closed_under_renaming_def
  proof (intro allI impI)
    fix C D
    assume C_in: "C \<in> to_SuperCalc_ecl ` N" and renaming_C: "renaming_cl C D"
    then show "D \<in> to_SuperCalc_ecl ` N"
      sorry
  qed

  note int_clset_is_a_model' =
    G_SuperCalc.int_clset_is_a_model[OF gr_inf_satur_N all_finite_N Ball_well_constrained_N' _
      closed_renaming_N]

  define I where "I \<equiv> G_SuperCalc.same_values (\<lambda>t. G_SuperCalc.trm_rep M t (to_SuperCalc_ecl ` N))"

  have fo_int_I: "fo_interpretation I"
    unfolding I_def
    using G_SuperCalc.same_values_fo_int G_SuperCalc.trm_rep_compatible_with_structure by blast

  obtain C \<sigma> where
    C_in_N: "C \<in> to_SuperCalc_ecl ` N" and
    gr_cl_C_\<sigma>: "ground_clause (subst_cl (cl_ecl C) \<sigma>)" and
    not_val_gr_cl_C_\<sigma>: "\<not> validate_ground_clause I (subst_cl (cl_ecl C) \<sigma>)"
    using \<open>N \<TTurnstile>e {B}\<close>[unfolded B_def entails_def, simplified, unfolded set_entails_clause_def,
        rule_format, OF fo_int_I, unfolded validate_clause.simps, simplified]
    unfolding set_entails_clause_def
    sorry

  have "trms_ecl C = {}"
    using C_in_N by force
  hence all_trms_irreducible: "G_SuperCalc.all_trms_irreducible
    (subst_set (trms_ecl C) \<sigma>) (\<lambda>t. G_SuperCalc.trm_rep M t (to_SuperCalc_ecl ` N))"
    by (simp add: subst_set.simps)

  have "\<not> (\<forall>x\<in>to_SuperCalc_ecl ` N. cl_ecl x \<noteq> {})"
    apply (rule contrapos_nn[OF not_val_gr_cl_C_\<sigma>])
    apply (rule int_clset_is_a_model'[rule_format, of "(C, \<sigma>)" C \<sigma>,
          OF _ _ _ C_in_N gr_cl_C_\<sigma> all_trms_irreducible, simplified, folded I_def])
    by blast
  then obtain C where "Ecl (to_SuperCalc_cl C) {} \<in> to_SuperCalc_ecl ` N" and
    "cl_ecl (Ecl (to_SuperCalc_cl C) {}) = {}"
    by (auto simp: to_SuperCalc_cl_def)
  hence "C \<in> N" and "C = {#}"
    by (auto simp: to_SuperCalc_cl_def)
  thus "\<exists>B' \<in> {{#}}. B' \<in> N"
    by simp
qed


subsubsection \<open>First-Order SuperCalc\<close>

interpretation SuperCalc: basic_superposition trm_ord select pos_ord "UNIV :: 'a set" "\<lambda>_ _. {}"
  using trm_ord_wf trm_ord_trans trm_ord_irrefl trm_ord_reduction_left trm_ord_reduction_right
    trm_ord_subterm trm_ord_subst pos_ord_irrefl pos_ord_prefix pos_ord_nil infinite_vars select_neg
    select_renaming G_SuperCalc.trm_ord_ground_total G_SuperCalc.pos_ord_trans
  by unfold_locales simp_all

lemmas [simp del] = SuperCalc.trm_rep.simps

definition derivable_list where
  "derivable_list C Ps \<sigma> k C' \<longleftrightarrow>
    (\<exists>P1. \<exists>P2. Ps = [P2, P1] \<and> SuperCalc.superposition P1 P2 C \<sigma> k C') \<or>
    (\<exists>P1. Ps = [P1] \<and> SuperCalc.factorization P1 C \<sigma> k C') \<or>
    (\<exists>P1. Ps = [P1] \<and> SuperCalc.reflexion P1 C \<sigma> k C')"

lemma derivable_list_imp_derivable:
  "derivable_list C Ps \<sigma> k C' \<Longrightarrow> set Ps \<subseteq> S \<Longrightarrow> SuperCalc.derivable C (set Ps) S \<sigma> k C'"
  unfolding derivable_list_def SuperCalc.derivable_def
  by (auto simp: insert_commute)

lemma derivable_list_non_empty_premises: "derivable_list C Ps \<sigma> k C' \<Longrightarrow> Ps \<noteq> []"
  by (auto simp add: derivable_list_def)

lemma derivable_list_ground_premises:
  assumes "\<forall>C \<in> set Ps. ground_clause (cl_ecl C)" and "derivable_list C Ps \<sigma> k C'"
  shows "ground_clause C'"
  using assms
  by (auto simp: derivable_list_def
      intro: SuperCalc.ground_clause_reflexion
             SuperCalc.ground_clause_factorization
             SuperCalc.ground_clause_superposition)

lemma derivable_list_finite_conclusion:
  "\<forall>C\<in>set Ps. finite (cl_ecl C) \<Longrightarrow> derivable_list C Ps \<sigma> k C' \<Longrightarrow> finite C'"
  using SuperCalc.derivable_finite_conclusion[OF _ derivable_list_imp_derivable]
  by blast

lemma derivable_list_concl_conv:
  "derivable_list C Ps \<sigma> k C' \<Longrightarrow> cl_ecl C = subst_cl C' \<sigma>"
  unfolding derivable_list_def SuperCalc.derivable_def
  by (auto simp: SuperCalc.reflexion_def SuperCalc.factorization_def
      SuperCalc.superposition_def)

lemma assumes "finite (cl_ecl C)" "renaming_cl C D" shows "renaming_cl D C"
proof -
  from \<open>renaming_cl C D\<close> obtain \<rho> where
    ren_\<rho>: "renaming \<rho> (vars_of_cl (cl_ecl C))" and
    "D = subst_ecl C \<rho>"
    unfolding renaming_cl_def by blast

  from \<open>finite (cl_ecl C)\<close> have "finite (vars_of_cl (cl_ecl C))"
    using set_of_variables_is_finite_cl by blast

  with ren_\<rho> obtain \<rho>_inv where
    \<rho>_\<rho>_inv_ident: "\<forall>x\<in>vars_of_cl (cl_ecl C). Var x \<lhd> \<rho> \<lhd> \<rho>_inv = Var x" and
    "\<forall>x. x \<notin> subst_codomain \<rho> (vars_of_cl (cl_ecl C)) \<longrightarrow> Var x \<lhd> \<rho>_inv = Var x"
    using renamings_admit_inverse by blast

  show ?thesis
    unfolding renaming_cl_def
  proof (intro exI conjI)
    show "C = subst_ecl D \<rho>_inv"
      unfolding \<open>D = subst_ecl C \<rho>\<close>
      unfolding SuperCalc.subst_ecl_subst_ecl
      apply (rule SuperCalc.subst_ecl_ident[symmetric])
      unfolding Un_iff
      apply (erule disjE)
      subgoal for x t
        apply (drule \<rho>_\<rho>_inv_ident[rule_format])
  

lemma
  fixes \<sigma>
  assumes
    refl: "SuperCalc.reflexion P1 C \<sigma>\<^sub>C k C'" and
    ren: "renaming_cl P1 P1'" and
    fin_P1: "finite (cl_ecl P1)"
  shows "\<exists>D \<sigma>\<^sub>D D'. SuperCalc.reflexion P1' D \<sigma>\<^sub>D k D' \<and> renaming_cl C D"
proof -
  from refl obtain L1 t s Cl_P Cl_C trms_C where
    "SuperCalc.eligible_literal L1 P1 \<sigma>\<^sub>C" and
    "L1 \<in> cl_ecl P1" and
    "Cl_C = cl_ecl C" and
    "Cl_P = cl_ecl P1" and
    "SuperCalc.orient_lit_inst L1 t s neg \<sigma>\<^sub>C" and
    "SuperCalc.ck_unifier t s \<sigma>\<^sub>C k" and
    "C = Ecl Cl_C trms_C" and
    "trms_C = SuperCalc.get_trms Cl_C
      (SuperCalc.dom_trms Cl_C (subst_set (trms_ecl P1 \<union> {t}) \<sigma>\<^sub>C)) k" and
    "Cl_C = subst_cl C' \<sigma>\<^sub>C \<and> C' = Cl_P - {L1}"
    unfolding SuperCalc.reflexion_def by blast

  from ren obtain \<rho> where
    ren_\<rho>: "renaming \<rho> (vars_of_cl (cl_ecl P1))" and
    "P1' = subst_ecl P1 \<rho>"
    unfolding renaming_cl_def by blast

  from fin_P1 have "finite (vars_of_cl (cl_ecl P1))"
    using set_of_variables_is_finite_cl by blast

  with ren_\<rho> obtain \<rho>_inv where
    "\<forall>x\<in>vars_of_cl (cl_ecl P1). Var x \<lhd> \<rho> \<lhd> \<rho>_inv = Var x" and
    "\<forall>x. x \<notin> subst_codomain \<rho> (vars_of_cl (cl_ecl P1)) \<longrightarrow> Var x \<lhd> \<rho>_inv = Var x"
    using renamings_admit_inverse by blast

  define D' where
    "D' = cl_ecl (subst_ecl P1' \<rho>) - {equational_clausal_logic.subst_lit L1 \<rho>}"
  
  define \<sigma>\<^sub>D where
    "\<sigma>\<^sub>D = \<sigma>\<^sub>C \<lozenge> \<rho>_inv"

  define D where
    "D = (let Cl_D = subst_cl D' \<sigma>\<^sub>D in
      Ecl Cl_D (SuperCalc.get_trms Cl_D
        (SuperCalc.dom_trms Cl_D (subst_set (trms_ecl P1' \<union> {t}) \<sigma>\<^sub>D)) k))"

  show ?thesis
  proof (intro exI conjI)
    show "SuperCalc.reflexion P1' D \<sigma>\<^sub>D k D'"
      unfolding \<open>P1' = subst_ecl P1 \<rho>\<close>
      unfolding SuperCalc.reflexion_def
      sorry
  next
    show "renaming_cl C D"
      find_theorems name: SuperCalc "renaming_cl _ _"
      unfolding renaming_cl_def
      unfolding \<open>C = Ecl Cl_C trms_C\<close> subst_ecl.simps
      unfolding D_def Let_def
      unfolding D'_def
      apply simp

lemma
  assumes deriv: "derivable_list C Ps \<sigma> k C'" and renam: "list_all2 renaming_cl Ps Ps'"
  shows "\<exists>D \<sigma>\<^sub>D D'. derivable_list D Ps' \<sigma>\<^sub>D k D' \<and> renaming_cl C D"
  using deriv unfolding derivable_list_def
proof (elim disjE exE conjE)
  

subsubsection \<open>First-Order Calculus\<close>

text \<open>
Renaming is performed here in order to keep @{const G_derivable_list} as similar as possible to
@{const SuperCalc.derivable}. Renaming would not strictly be necessary for
@{const SuperCalc.factorization} and @{const SuperCalc.reflexion}, but it does not hurt either.

If it ever cause a problem, change the structure to have access to @{type Clausal_Logic.clause} in
@{const G_derivable_list}.
\<close>

definition F_Inf :: "'a equation Clausal_Logic.clause inference set" where
  "F_Inf \<equiv> {Infer Ps (subst_cls (from_SuperCalc_cl C') \<sigma>) | Ps C \<sigma> C'.
    derivable_list C (map to_SuperCalc_ecl (map2 subst_cls Ps (renamings_apart Ps))) \<sigma>
      SuperCalc.FirstOrder C'}"

lemma F_Inf_have_prems: "\<iota> \<in> F_Inf \<Longrightarrow> prems_of \<iota> \<noteq> []"
  by (auto simp: F_Inf_def derivable_list_def)

interpretation F: inference_system F_Inf .

definition \<G>_F :: "'a equation Clausal_Logic.clause \<Rightarrow> 'a equation Clausal_Logic.clause set" where
  "\<G>_F C \<equiv> subst_cls C ` {\<sigma>. ground_on (vars_of_cl (to_SuperCalc_cl C)) \<sigma>}"

lemma \<G>_F_mempty[simp]: "\<G>_F {#} = {{#}}"
  using ground_subst_exists[OF finite.emptyI]
  by (auto simp add: \<G>_F_def intro: image_constant)

definition \<G>_I where
  "\<G>_I M \<iota> \<equiv> {\<iota>' \<in> G_Inf M.
    (\<exists>\<rho>s. subst_cls_lists (prems_of \<iota>) \<rho>s = prems_of \<iota>') \<and>
    (\<exists>\<rho>. subst_cls (concl_of \<iota>) \<rho> = concl_of \<iota>')}"

lemma grounding_of_inferences_are_grounded_inferences: "\<iota> \<in> F_Inf \<Longrightarrow> \<iota>' \<in> \<G>_I M \<iota> \<Longrightarrow> \<iota>' \<in> G_Inf M"
  by (simp add: \<G>_I_def)


interpretation F: lifting_intersection F_Inf "{{#}}" UNIV G_Inf "\<lambda>_. (\<TTurnstile>e)" G.Red_I "\<lambda>_. G.Red_F"
  "{{#}}" "\<lambda>_. \<G>_F" "\<lambda>M. Some \<circ> \<G>_I M" "\<lambda>_ _ _. False"
proof (unfold_locales; (intro ballI)?)
  show "UNIV \<noteq> {}"
    by (rule UNIV_not_empty)
next
  show "consequence_relation {{#}} (\<TTurnstile>e)"
    by (rule G.consequence_relation_axioms)
next
  show "\<And>M. tiebreaker_lifting {{#}} F_Inf {{#}} (\<TTurnstile>e) (G_Inf M) (G.Red_I M) G.Red_F \<G>_F
    (Some \<circ> \<G>_I M) (\<lambda>_ _ _. False)"
  proof unfold_locales
    fix M \<iota>
    assume \<iota>_in: "\<iota> \<in> F_Inf"
    have "\<G>_I M \<iota> \<subseteq> G.Red_I M (\<G>_F (concl_of \<iota>))"
    proof (rule subsetI)
      fix \<iota>'
      assume \<iota>'_grounding: "\<iota>' \<in> \<G>_I M \<iota>"
      with \<iota>_in have \<iota>'_in: "\<iota>' \<in> G_Inf M"
        by (rule grounding_of_inferences_are_grounded_inferences)

      obtain \<rho> where concl_\<iota>'_conv:"concl_of \<iota>' = subst_cls (concl_of \<iota>) \<rho>"
        using \<iota>'_grounding[unfolded \<G>_I_def mem_Collect_eq]
        by metis
      
      show "\<iota>' \<in> G.Red_I M (\<G>_F (concl_of \<iota>))"
      apply (rule G.Red_I_of_Inf_to_N[OF \<iota>'_in])
      unfolding concl_\<iota>'_conv
      unfolding \<G>_F_def Let_def
      apply (rule imageI)
      unfolding mem_Collect_eq
      using G_Inf_ground_concl[OF \<iota>'_in]
      by (metis concl_\<iota>'_conv ground_clauses_and_ground_substs to_SuperCalc_cl_subst_cls)
    qed
    thus "the ((Some \<circ> \<G>_I M) \<iota>) \<subseteq> G.Red_I M (\<G>_F (concl_of \<iota>))"
      by simp
  next
    show "po_on (\<lambda>_ _. False) UNIV"
      by (simp add: irreflp_onI po_onI transp_onI)
  qed (auto simp add: \<G>_F_def ground_subst_exists)
qed

lemma vars_of_subst_conv:
  fixes t and \<sigma>
  shows "vars_of (subst t \<sigma>) = \<Union>((\<lambda>v. vars_of (assoc v (Var v) \<sigma>)) ` vars_of t)"
  by (induction t) auto

lemma vars_of_eq_subst_equation_conv:
  fixes e and \<sigma>
  shows "vars_of_eq (subst_equation e \<sigma>) = \<Union>((\<lambda>v. vars_of (assoc v (Var v) \<sigma>)) ` vars_of_eq e)"
  by (cases e) (auto simp: vars_of_subst_conv)

lemma vars_of_lit_subst_lit_conv:
  fixes L and \<sigma>
  shows "vars_of_lit (equational_clausal_logic.subst_lit L \<sigma>) =
    \<Union>((\<lambda>v. vars_of (assoc v (Var v) \<sigma>)) ` vars_of_lit L)"
  by (cases L) (auto simp: vars_of_eq_subst_equation_conv)

lemma vars_of_cl_subst_cl_conv:
  fixes C \<sigma>
  shows "vars_of_cl (subst_cl C \<sigma>) = \<Union>((\<lambda>v. vars_of (assoc v (Var v) \<sigma>)) ` vars_of_cl C)"
    (is "?lhs = ?rhs")
proof (rule Set.equalityI; rule Set.subsetI)
  fix x
  assume "x \<in> ?lhs"
  then obtain L where x_in_L: "x \<in> vars_of_lit L" and L_in_subst_C: "L \<in> subst_cl C \<sigma>"
    by auto
  obtain L' where L'_in_C: "L' \<in> C" and L_def: "L = equational_clausal_logic.subst_lit L' \<sigma>"
    using L_in_subst_C by (auto simp: subst_cl.simps)
  then show "x \<in> ?rhs"
    using x_in_L by (auto simp: vars_of_lit_subst_lit_conv)
next
  fix x
  assume "x \<in> ?rhs"
  then obtain L v where
    L_in_C: "L \<in> C " and
    v_in_vars_C: "v \<in> vars_of_lit L" and
    x_in_vars_v_\<sigma>: "x \<in> vars_of (assoc v (Var v) \<sigma>)"
    by auto
  let ?L' = "equational_clausal_logic.subst_lit L \<sigma>"
  show "x \<in> ?lhs"
    unfolding vars_of_cl.simps Set.mem_Collect_eq
  proof (intro exI conjI)
    show "x \<in> vars_of_lit ?L'"
      using v_in_vars_C x_in_vars_v_\<sigma> vars_of_lit_subst_lit_conv by force
  next
    show "?L' \<in> subst_cl C \<sigma>"
      using L_in_C by (auto simp: subst_cl.simps)
  qed
qed

lemma is_a_variable_subst_comp:
  fixes C \<sigma> \<eta>
  assumes
    ball_var_\<sigma>: "\<forall>x\<in>vars_of_cl C. is_a_variable (Var x \<lhd> \<sigma>)" and
    ball_var_\<eta>: "\<forall>x\<in>vars_of_cl (subst_cl C \<sigma>). is_a_variable (Var x \<lhd> \<eta>)"
  shows "\<forall>x\<in>vars_of_cl C. is_a_variable (Var x \<lhd> (\<sigma> \<lozenge> \<eta>))"
proof (intro ballI)
  fix x
  assume x_in_C: "x \<in> vars_of_cl C"
  hence "is_a_variable (Var x \<lhd> \<sigma>)"
    using ball_var_\<sigma> by simp
  then obtain x' where "Var x \<lhd> \<sigma> = Var x'"
    by (auto elim: is_a_variable.elims(2))
  hence "x' \<in> vars_of_cl (subst_cl C \<sigma>)"
    unfolding vars_of_cl_subst_cl_conv
    using x_in_C
    by auto
  then show "is_a_variable (Var x \<lhd> \<sigma> \<lozenge> \<eta>)"
    unfolding Unification.subst_comp \<open>Var x \<lhd> \<sigma> = Var x'\<close>
    using ball_var_\<eta>
    by blast
qed

lemma in_vars_of_cl_subst_cl:
  fixes C x x' \<sigma>
  assumes "x \<in> vars_of_cl C" and "Var x \<lhd> \<sigma> = Var x'"
  shows "x' \<in> vars_of_cl (subst_cl C \<sigma>)"
proof -
  from \<open>x \<in> vars_of_cl C\<close> obtain L where "x \<in> vars_of_lit L" and "L \<in> C"
    by auto
  let ?L' = "equational_clausal_logic.subst_lit L \<sigma>"
  show ?thesis
    unfolding vars_of_cl.simps Set.mem_Collect_eq
  proof (intro exI conjI)
    show "x' \<in> vars_of_lit ?L'"
      using \<open>Var x \<lhd> \<sigma> = Var x'\<close> \<open>x \<in> vars_of_lit L\<close>
      by (auto simp: vars_of_lit_subst_lit_conv intro: bexI[of _ x])
  next
    show "?L' \<in> subst_cl C \<sigma>"
      using \<open>L \<in> C\<close>
      by (auto simp add: subst_cl.simps)
  qed
qed

lemma renaming_imp_ball_var: "\<And>\<sigma> S. renaming \<sigma> S \<Longrightarrow> \<forall>x\<in>S. is_a_variable (Var x \<lhd> \<sigma>)"
  unfolding renaming_def by simp

lemma renaming_imp_ball_neq_imp_neq_subst:
  "\<And>\<sigma> S. renaming \<sigma> S \<Longrightarrow> \<forall>x\<in>S. \<forall>y\<in>S. x \<noteq> y \<longrightarrow> Var x \<lhd> \<sigma> \<noteq> Var y \<lhd> \<sigma>"
  unfolding renaming_def by simp

lemma closed_under_renaming_closure:
  fixes N N'
  defines "N' \<equiv> {subst_cls C \<sigma> |C \<sigma>. C \<in> N \<and> renaming \<sigma> (vars_of_cl (to_SuperCalc_cl C))}"
  shows "closed_under_renaming (to_SuperCalc_ecl ` N')"
  unfolding closed_under_renaming_def
proof (intro allI impI)
  fix C D
  assume "C \<in> to_SuperCalc_ecl ` N'"
  then obtain CC \<sigma> where
    C_def: "C = to_SuperCalc_ecl (subst_cls CC \<sigma>)" and
    "CC \<in> N" and
    renaming_\<sigma>: "renaming \<sigma> (vars_of_cl (to_SuperCalc_cl CC))"
    unfolding N'_def
    by blast

  assume "renaming_cl C D"
  then obtain \<eta> where
    renaming_\<eta>: "renaming \<eta> (vars_of_cl (subst_cl (to_SuperCalc_cl CC) \<sigma>))" and
    D_def: "D = subst_ecl C \<eta>"
    unfolding renaming_cl_def
    unfolding C_def cl_ecl.simps to_SuperCalc_cl_subst_cls
    by blast

  show "D \<in> to_SuperCalc_ecl ` N'"
    unfolding image_iff
  proof (rule bexI)
    show "D = to_SuperCalc_ecl (subst_cls (subst_cls CC \<sigma>) \<eta>)"
      using D_def C_def
      by (simp add: to_SuperCalc_cl_subst_cls)
  next
    show "subst_cls (subst_cls CC \<sigma>) \<eta> \<in> N'"
      unfolding N'_def
    proof (intro CollectI exI conjI)
      show "CC \<in> N"
        by (rule \<open>CC \<in> N\<close>)
    next
      have "\<forall>x\<in>vars_of_cl (to_SuperCalc_cl CC). is_a_variable (Var x \<lhd> comp_subst_abbrev \<sigma> \<eta>)"
        using renaming_imp_ball_var[OF renaming_\<sigma>]
        using renaming_imp_ball_var[OF renaming_\<eta>]
        by (fact is_a_variable_subst_comp)

      moreover have "(\<forall>x y.
          x \<in> vars_of_cl (to_SuperCalc_cl CC) \<longrightarrow>
          y \<in> vars_of_cl (to_SuperCalc_cl CC) \<longrightarrow>
          x \<noteq> y \<longrightarrow> Var x \<lhd> comp_subst_abbrev \<sigma> \<eta> \<noteq> Var y \<lhd> comp_subst_abbrev \<sigma> \<eta>)"
      proof (intro allI impI)
        fix x y
        assume
          x_in_vars_CC: "x \<in> vars_of_cl (to_SuperCalc_cl CC)" and
          y_in_vars_CC: "y \<in> vars_of_cl (to_SuperCalc_cl CC)" and
          "x \<noteq> y"
        hence x_\<sigma>_neq_y_\<sigma>: "Var x \<lhd> \<sigma> \<noteq> Var y \<lhd> \<sigma>"
          using renaming_imp_ball_neq_imp_neq_subst[OF renaming_\<sigma>]
          by simp
        have "is_a_variable (Var x \<lhd> \<sigma>)" and "is_a_variable (Var y \<lhd> \<sigma>)"
          using renaming_imp_ball_var[OF renaming_\<sigma>] x_in_vars_CC y_in_vars_CC by simp_all
        then obtain x' y' where
          x_subst_def: "(Var x \<lhd> \<sigma>) = Var x'" and
          y_subst_def: "(Var y \<lhd> \<sigma>) = Var y'"
          by (meson is_a_variable.elims(2))
        show "Var x \<lhd> comp_subst_abbrev \<sigma> \<eta> \<noteq> Var y \<lhd> comp_subst_abbrev \<sigma> \<eta> "
          unfolding Unification.subst_comp
          unfolding x_subst_def y_subst_def
          using renaming_imp_ball_neq_imp_neq_subst[OF renaming_\<eta>]
          using in_vars_of_cl_subst_cl[OF x_in_vars_CC x_subst_def]
          using in_vars_of_cl_subst_cl[OF y_in_vars_CC y_subst_def]
          using x_\<sigma>_neq_y_\<sigma>[unfolded x_subst_def y_subst_def]
          by simp
      qed

      ultimately show "renaming (\<sigma> \<lozenge> \<eta>) (vars_of_cl (to_SuperCalc_cl CC))"
        unfolding renaming_def by simp
    next
      show "subst_cls (subst_cls CC \<sigma>) \<eta> = subst_cls CC (\<sigma> \<lozenge> \<eta>)"
        by simp
    qed
  qed
qed

lemma renaming_imp_is_renaming:
  fixes \<sigma> :: "('a \<times> 'a trm) list"
  assumes "renaming \<sigma> UNIV"
  shows "is_renaming \<sigma>"
proof -
  show ?thesis
    using assms
    unfolding renaming_def is_renaming_def
    apply simp
    oops

lemma finite_vars_of_to_SuperCalc_cl: "finite (vars_of_cl (to_SuperCalc_cl C))"
  using finite_to_SuperCalc_cl set_of_variables_is_finite_cl by blast

lemma is_renaming_imp_renaming:
  fixes \<sigma> :: "('a \<times> 'a trm) list" and S :: "'a set"
  shows "is_renaming \<sigma> \<Longrightarrow> renaming \<sigma> S"
  unfolding is_renaming_def
  by (auto elim: comp.elims)

lemma ex_eq_map2_if_ball_set_eq:
  assumes "\<forall>x \<in> set xs. \<exists>y z. x = f y z \<and> P y z"
  shows "\<exists>ys zs. xs = map2 f ys zs \<and> length ys = length zs \<and> list_all2 P ys zs"
  using assms
proof (induction xs)
  case Nil
  show ?case
    by (rule exI[where x = "[]"], rule exI[where x = "[]"]) simp
next
  case (Cons x xs)
  then obtain ys zs where
    "length ys = length zs" and "xs = Map2.map2 f ys zs" and "list_all2 P ys zs"
    by auto
  moreover from Cons.prems obtain y z where "x = f y z" and "P y z"
    by auto
  ultimately show ?case
    apply -
    by (rule exI[where x = "y # ys"], rule exI[where x = "z # zs"]) simp
qed


lemma "finite C \<Longrightarrow> from_SuperCalc_cl (subst_cl C \<sigma>) = subst_cls (from_SuperCalc_cl C) \<sigma>"
  unfolding subst_cl_conv from_SuperCalc_cl_def
  apply simp
  oops

sublocale statically_complete_calculus "{{#}}" F_Inf "(\<TTurnstile>e)" F.Red_I_\<G> F.Red_F_\<G>
proof unfold_locales
  show "\<And>N. F.Red_I_\<G> N \<subseteq> F_Inf"
    by (rule F.Red_I_to_Inf)
next
  fix B N
  assume "B \<in> {{#}}" and "N \<TTurnstile>e {B}"
  show "N - F.Red_F_\<G> N \<TTurnstile>e {B}"
    using F.Red_F_Bot[simplified, OF refl, unfolded F.entails_\<G>_def, simplified]
    sorry
next
  fix B and N :: "'a equation Clausal_Logic.clause set"
  assume "B \<in> {{#}}" and "F.saturated N" and "N \<TTurnstile>e {B}"
  hence B_def: "B = {#}" by simp

  \<comment> \<open>We close @{term N} under \<alpha>-renaming.\<close>
  \<comment> \<open>We cannot use @{const is_renaming} because we would need
  @{term "\<And>\<sigma> S. is_renaming \<sigma> \<longleftrightarrow> renaming \<sigma> S"} but only the forward direction holds.\<close>
  define N' :: "'a equation Clausal_Logic.clause set" where
    "N' \<equiv> {subst_cls C \<sigma> | C \<sigma>. C \<in> N \<and> renaming \<sigma> (vars_of_cl (to_SuperCalc_cl C))}"

  find_theorems "renaming _ _ \<Longrightarrow> _"

  have "N \<subseteq> N'"
  proof (rule Set.subsetI)
    fix C
    show "C \<in> N \<Longrightarrow> C \<in> N'"
      unfolding N'_def Set.mem_Collect_eq
      by (auto intro!: exI[of _ C] exI[of _ "[]"])
  qed
  hence "N' \<TTurnstile>e {{#}}"
    using \<open>N \<TTurnstile>e {B}\<close>[unfolded B_def]
    by (auto intro: G.entails_trans[of N' N "{{#}}"] G.subset_entailed)

  have all_finite_N': "\<forall>x\<in>to_SuperCalc_ecl ` N'. finite (cl_ecl x)"
    by simp

  from \<open>F.saturated N\<close> have sat_N_alt: "\<And>\<iota>. \<iota> \<in> F_Inf \<Longrightarrow> set (prems_of \<iota>) \<subseteq> N \<Longrightarrow> \<iota> \<in> F.Red_I_\<G> N"
    unfolding F.saturated_def F.Inf_from_def
    by (auto dest: Set.subsetD)

  have saturated_N': "F.saturated N'"
    unfolding F.saturated_def
  proof (rule Set.subsetI)
    fix \<iota>' :: "'a equation Clausal_Logic.clause inference"
    assume "\<iota>' \<in> F.Inf_from N'"
    hence \<iota>'_in: "\<iota>' \<in> F_Inf" and prems_\<iota>'_subset: "set (prems_of \<iota>') \<subseteq> N'"
      unfolding F.Inf_from_def Set.mem_Collect_eq by simp_all

    from \<iota>'_in obtain C \<sigma>\<^sub>C C' where
      "concl_of \<iota>' = subst_cls (from_SuperCalc_cl C') \<sigma>\<^sub>C" and
      deriv_prems_\<iota>': "derivable_list C
        (map to_SuperCalc_ecl (map2 subst_cls (prems_of \<iota>') (renamings_apart (prems_of \<iota>'))))
        \<sigma>\<^sub>C SuperCalc.FirstOrder C'"
      unfolding F_Inf_def mem_Collect_eq by force

    from prems_\<iota>'_subset obtain Ps \<rho>s where
      prems_\<iota>'_def: "prems_of \<iota>' = Map2.map2 subst_cls Ps \<rho>s" and "length Ps = length \<rho>s" and
      FOO: "list_all2 (\<lambda>C \<sigma>. C \<in> N \<and> renaming \<sigma> (vars_of_cl (to_SuperCalc_cl C))) Ps \<rho>s"
      unfolding N'_def Ball_Collect[symmetric]
      by (auto dest: ex_eq_map2_if_ball_set_eq)

    from deriv_prems_\<iota>' obtain D D' \<sigma>\<^sub>D where
      deriv_Ps: "derivable_list D (map to_SuperCalc_ecl (map2 subst_cls Ps (renamings_apart Ps)))
        \<sigma>\<^sub>D SuperCalc.FirstOrder D'"
      sorry

    obtain \<rho> where concl_\<iota>'_def: "concl_of \<iota>' = subst_cls (subst_cls (from_SuperCalc_cl D') \<sigma>\<^sub>D) \<rho>"
      sorry

    define \<iota> where "\<iota> = Infer Ps (subst_cls (from_SuperCalc_cl D') \<sigma>\<^sub>D)"

    have \<iota>_in: "\<iota> \<in> F_Inf"
      unfolding \<iota>_def F_Inf_def mem_Collect_eq using deriv_Ps by blast

    have prems_\<iota>_in_subset: "set (prems_of \<iota>) \<subseteq> N"
      using FOO by (simp add: \<iota>_def list_all2_conj_unary_iff list_all_member_iff_subset)

    from sat_N_alt[OF \<iota>_in prems_\<iota>_in_subset]
    have \<G>_subset_Red_\<iota>: "\<And>q. \<G>_I q \<iota> \<subseteq> G.Red_I q (\<Union> (\<G>_F ` N))"
      unfolding F.Red_I_\<G>_def F.Red_I_\<G>_q_def by simp

    have "finite D'"
      by (rule derivable_list_finite_conclusion[OF _ deriv_Ps]) simp

    have "\<G>_I q \<iota>' \<subseteq> G.Red_I q (\<Union> (\<G>_F ` N'))" for q
    proof (rule subsetI)
      fix \<iota>g
      assume "\<iota>g \<in> \<G>_I q \<iota>'"
      hence "\<iota>g \<in> \<G>_I q \<iota>"
        unfolding \<G>_I_def mem_Collect_eq \<iota>_def inference.sel
        apply simp
        apply (elim conjE)
        apply (rule conjI)
         apply (metis prems_\<iota>'_def subst_cls_lists_comp_substs subst_cls_lists_def)
        apply (elim exE)
        unfolding concl_\<iota>'_def
        by (metis subst_cls_comp_subst)
      moreover have "G.Red_I q (\<Union> (\<G>_F ` N)) \<subseteq> G.Red_I q (\<Union> (\<G>_F ` N'))"
        by (simp add: G.Red_I_of_subset UN_mono \<open>N \<subseteq> N'\<close>)
      ultimately show "\<iota>g \<in> G.Red_I q (\<Union> (\<G>_F ` N'))"
        using \<G>_subset_Red_\<iota>[THEN subsetD] by auto
    qed

    then have "\<iota>' \<in> F.Red_I_\<G>_q q N'" for q
      unfolding F.Red_I_\<G>_q_def mem_Collect_eq
      using \<iota>'_in by simp
    thus "\<iota>' \<in> F.Red_I_\<G> N'"
      unfolding F.Red_I_\<G>_def by simp
  qed

  have gr_inf_satur_N': "SuperCalc.ground_inference_saturated (to_SuperCalc_ecl ` N')"
    unfolding SuperCalc.ground_inference_saturated_def
  proof (intro allI impI)
    fix C P \<sigma> C'
    assume
      deriv_C_P: "SuperCalc.derivable C P (to_SuperCalc_ecl ` N') \<sigma> SuperCalc.Ground C'" and
      ground_C: "ground_clause (cl_ecl C)" and
      grounding_P: "SuperCalc.grounding_set P \<sigma>"

    then show "SuperCalc.redundant_inference C (to_SuperCalc_ecl ` N') P \<sigma>"
      unfolding SuperCalc.redundant_inference_def
      unfolding SuperCalc.derivable_clauses_lemma[OF deriv_C_P]
      using saturated_N'[unfolded F.empty_ord.saturated_def F.Inf_from_def F.Red_I_\<G>_def
          F.Red_I_\<G>_q_def, simplified]
      sorry
  qed

  have ball_well_constrained_N': "Ball (to_SuperCalc_ecl ` N') SuperCalc.well_constrained"
    by (simp add: SuperCalc.well_constrained_def)

  have closed_renaming_N': "closed_under_renaming (to_SuperCalc_ecl ` N')"
    unfolding N'_def by (fact closed_under_renaming_closure)

  define I where "I \<equiv> SuperCalc.same_values (\<lambda>t. SuperCalc.trm_rep t (to_SuperCalc_ecl ` N'))"

  note int_clset_is_a_model' = SuperCalc.int_clset_is_a_model[OF gr_inf_satur_N' all_finite_N'
      ball_well_constrained_N' _ closed_renaming_N', folded I_def, of "(x, y)" for x y, simplified]

  have fo_int_I: "fo_interpretation I"
    unfolding I_def
    using SuperCalc.same_values_fo_int SuperCalc.trm_rep_compatible_with_structure by blast

  have "\<exists>B \<in> {{#}}. B \<in> N'"
  proof (rule contrapos_pp[OF \<open>N' \<TTurnstile>e {{#}}\<close>])
    assume "\<not> (\<exists>B \<in> {{#}}. B \<in> N')"
    hence ball_N_not_empty: "\<forall>C \<in> N'. to_SuperCalc_cl C \<noteq> {}"
      by (metis insertI1 set_mset_eq_empty_iff to_SuperCalc_cl_empty_mset to_SuperCalc_cl_eq_conv)
  
    have val_I_N': "validate_clause_set I (to_SuperCalc_cl ` N')"
      unfolding validate_clause_set.simps validate_clause.simps
    proof (intro allI impI)
      fix C \<sigma>
      assume "C \<in> to_SuperCalc_cl ` N'" and "ground_clause (subst_cl C \<sigma>)"
      thus "validate_ground_clause I (subst_cl C \<sigma>)"
        using int_clset_is_a_model'[OF ball_N_not_empty, of "Ecl C {}", simplified] by blast
    qed
  
    show "\<not> N' \<TTurnstile>e {{#}}"
    proof (rule notI)
      assume "N' \<TTurnstile>e {{#}}"
      hence "validate_ground_clause I {}"
        using fo_int_I val_I_N' by (simp add: entails_def set_entails_set_def)
      thus False
        by (simp add: validate_ground_clause.simps)
    qed
  qed
  thus "\<exists>B \<in> {{#}}. B \<in> N"
    by (simp add: N'_def)
qed

end

end
