theory Prover
  imports
    Ordered_Resolution_Prover.Abstract_Substitution
    SuperCalc.superposition
    Saturation_Framework.Calculus
    Saturation_Framework_Extensions.Standard_Redundancy_Criterion
    "HOL-Library.FSet"
begin


subsection \<open>Generic lemmas about HOL definitions\<close>

lemma set_eq_unionI:
  assumes "\<And>x. x \<in> A \<longleftrightarrow> x \<in> B \<or> x \<in> C"
  shows "A = (B \<union> C)"
  using assms by blast

lemma total_trancl: "total R \<Longrightarrow> total (trancl R)"
  by (meson r_into_trancl' total_on_def)

lemma refl_Un: "refl S1 \<or> refl S2 \<Longrightarrow> refl (S1 \<union> S2)"
  by (auto dest: refl_onD intro: refl_onI)

lemma refl_trivial: "refl {(x, x) | x. True}"
  by (rule refl_onI) simp_all

lemma asympD: "asymp R \<Longrightarrow> R x y \<Longrightarrow> \<not> R y x"
  by (rule asymD[to_pred])

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

lemma list_all2_conjD:
  "list_all2 (\<lambda>x y. P x \<and> Q x y) xs ys \<longleftrightarrow> list_all P xs \<and> list_all2 (\<lambda>x y. Q x y) xs ys"
  "list_all2 (\<lambda>x y. P y \<and> Q x y) xs ys \<longleftrightarrow> list_all P ys \<and> list_all2 (\<lambda>x y. Q x y) xs ys"
  by (auto simp: list_all2_conv_all_nth list_all_length)

lemma list_all_member_iff_subset: "list_all (\<lambda>x. x \<in> N) xs \<longleftrightarrow> set xs \<subseteq> N"
  by (simp add: list.pred_set subset_code(1))


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

lemma redundant_inference_subset_eqI:
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

definition set_entails_set where
  "set_entails_set N1 N2 \<longleftrightarrow>
    (\<forall>I. fo_interpretation I \<longrightarrow> validate_clause_set I N1 \<longrightarrow> validate_clause_set I N2)"

lemma sent_entails_subset_eq: "N \<subseteq> N' \<Longrightarrow> set_entails_set N M \<Longrightarrow> set_entails_set N' M"
  unfolding set_entails_set_def
  by blast

lemma derivable_finite_conclusion:
  assumes "\<forall>C \<in> P. finite (cl_ecl C)" and  "derivable C P S \<sigma> k C'"
  shows "finite C'"
  using assms
  by (auto simp: derivable_def superposition_def factorization_def reflexion_def)

(* lemma "redundant_inference (Ecl C trms) N P \<sigma> \<Longrightarrow>
  redundant_inference (Ecl (set_mset (mset_set C)) trms) N P \<sigma>" *)


subsection \<open>Generic lemmas about SuperCalc without constraints\<close>

abbreviation ecl where
  "ecl C \<equiv> Ecl C {}"

lemma
  assumes "Ecl C {} \<in> N" and deriv: "derivable (Ecl C {}) prems N \<sigma> k C'"
  shows "redundant_inference (Ecl C {}) N prems \<sigma>"
  unfolding redundant_inference_def
proof (intro exI conjI ballI)
  show "instances {Ecl C {}} \<subseteq> instances N"
    using instances_eq_union_singleton[OF \<open>Ecl C {} \<in> N\<close>]
    by simp
next
  show "set_entails_clause (clset_instances (instances {Ecl C {}})) (cl_ecl (Ecl C {}))"
    using set_entails_clause_member[of "Ecl C {}" "{Ecl C {}}"]
    by simp
next
  fix x
  assume "x \<in> instances {Ecl C {}}"
  hence "fst x = Ecl C {}" and ground: "ground_clause (subst_cl C (snd x))"
    unfolding instances_def by force+
  show "subterms_inclusion (subst_set (trms_ecl (fst x)) (snd x)) (trms_ecl (Ecl C {}))"
    unfolding \<open>fst x = Ecl C {}\<close> by (simp add: subterms_inclusion_def)
next
  fix X
  assume X_inst_C: "X \<in> instances {Ecl C {}}"
  moreover obtain X' \<sigma>\<^sub>X where X_def: "X = (X', \<sigma>\<^sub>X)" by force
  ultimately have X'_def: "X' = Ecl C {}" and ground: "ground_clause (subst_cl C \<sigma>\<^sub>X)"
    unfolding instances_def by force+
  show "\<exists>D'\<in>prems. ((fst X, snd X), D', \<sigma>) \<in> ecl_ord"
    unfolding X_def fst_conv snd_conv X'_def
    (* using deriv conclusion_is_smaller_than_premisses *)
    using deriv[unfolded derivable_def]
    apply (elim disjE exE conjE)
    apply simp_all
    using conclusion_is_smaller_than_premisses
    (* Search in SuperCalc for occurences of "\<in> ecl_ord" or "effective".
       Maybe (probably?) Nicolas already proved something similar. *)
    oops

(* lemma "subst_cl (C - {L1}) \<sigma> = subst_cl C \<sigma> - subst_cl {L1} \<sigma>" (is "?lhs = ?rhs")
proof (rule equalityI; rule subsetI)
  fix x
  assume "x \<in> ?lhs"
  then show "x \<in> ?rhs"
    unfolding subst_cl.simps
    apply safe
     apply auto []
    apply simp
    apply safe *)

lemma reflexion_conclusion_is_small_than_premisse:
  assumes reflexion: "reflexion P (Ecl C {}) \<sigma> k C'" and finite_P: "finite (cl_ecl P)" and
    inst_C: "(Ecl C {}, \<sigma>\<^sub>X) \<in> instances {Ecl C {}}"
  shows "((Ecl C {}, \<sigma>\<^sub>X), P, \<sigma>) \<in> ecl_ord"
  using reflexion[unfolded reflexion_def]
  apply safe
  subgoal premises prems for L1
    unfolding ecl_ord_def mem_Collect_eq case_prod_beta prod.sel
    unfolding mset_ecl.simps cl_ecl.simps
    unfolding \<open>cl_ecl (Ecl C {}) = subst_cl (cl_ecl P - {L1}) \<sigma>\<close>[unfolded cl_ecl.simps]
    using inst_C
    using mset_set_Diff[OF finite_P, of "{L1}"]
  apply (simp add: mset_set_Diff[OF finite_P, of "{L1}"])
  oops

end


subsection \<open>Prover\<close>

primrec to_SuperCalc_lit
  :: "'a equation Clausal_Logic.literal \<Rightarrow> 'a equational_clausal_logic.literal" where
  "to_SuperCalc_lit (Clausal_Logic.Pos a) = equational_clausal_logic.Pos a" |
  "to_SuperCalc_lit (Clausal_Logic.Neg a) = equational_clausal_logic.Neg a"

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

lemma to_SuperCalc_cl_empty_mset[simp]: "to_SuperCalc_cl {#} = {}"
  by (simp add: to_SuperCalc_cl_def)

lemma finite_to_SuperCalc_cl[simp]: "finite (to_SuperCalc_cl C)"
  by (simp add: to_SuperCalc_cl_def)

definition from_SuperCalc_cl
  :: "'a equational_clausal_logic.clause \<Rightarrow> 'a equation Clausal_Logic.clause" where
  "from_SuperCalc_cl C \<equiv> image_mset from_SuperCalc_lit (mset_set C)"

lemma to_from_SuperCalc_cl[simp]:
  "finite C \<Longrightarrow> to_SuperCalc_cl (from_SuperCalc_cl C) = C"
  by (simp add: to_SuperCalc_cl_def from_SuperCalc_cl_def image_image)

abbreviation to_SuperCalc_ecl where
  "to_SuperCalc_ecl C \<equiv> Ecl (to_SuperCalc_cl C) {}"

locale superposition_prover =
    SuperCalc: basic_superposition trm_ord sel pos_ord "UNIV :: 'a set" "\<lambda>_ _. {}" +
    substitution subst_equation "[]" Unification.comp renamings_apart
  for
    \<comment> \<open>For SuperCalc\<close>
    trm_ord :: "('a trm \<times> 'a trm) set" and
    sel :: "'a literal set \<Rightarrow> 'a literal set" and

    \<comment> \<open>Voir si pos_ord influence SuperCalc.derivable. Si oui, garder comme paramètre. Sinon, mettre
    quelque chose de bidon\<close>
    pos_ord :: "'a eclause \<Rightarrow> 'a trm \<Rightarrow> (indices list \<times> indices list) set" and

    renamings_apart :: "'a equation Clausal_Logic.clause list \<Rightarrow> 'a subst list" +
  assumes
    infinite_vars: "\<not> finite (UNIV :: 'a set)"
begin

text \<open>
These simplification rules often hurt more than they help.
Better to remove it and selectively add them tho @{method simp} when necessary.
\<close>

lemmas [simp del] = equational_clausal_logic.ground_clause.simps
lemmas [simp del] = equational_clausal_logic.subst_cl.simps
lemmas [simp del] = equational_clausal_logic.validate_ground_clause.simps
lemmas [simp del] = terms.subst_set.simps
lemmas [simp del] = SuperCalc.trm_rep.simps

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

(*
Definir derivable_list qui est comme SuperCalc.derivable, sauf que les prémisses sont passées dans
une liste et que l'ordre définie la prémisse principale de superposition.

La prémisse principale est celle de droite, qui est parfois positive et parfois négative.
*)

definition derivable_list where
  "derivable_list C P S \<sigma> k C' \<longleftrightarrow>
    (\<exists>P1 \<in> S. \<exists>P2 \<in> S. P = [P2, P1] \<and> SuperCalc.superposition P1 P2 C \<sigma> k C') \<or>
    (\<exists>P1 \<in> S. P = [P1] \<and> SuperCalc.factorization P1 C \<sigma> k C') \<or>
    (\<exists>P1 \<in> S. P = [P1] \<and> SuperCalc.reflexion P1 C \<sigma> k C')"

lemma derivable_list_imp_derivable:
  "derivable_list C P S \<sigma> k C' \<Longrightarrow> SuperCalc.derivable C (set P) S \<sigma> k C'"
  unfolding derivable_list_def SuperCalc.derivable_def
  by (auto simp: insert_commute)

text \<open>
Renaming is performed here in order to keep @{const derivable_list} as similar as possible to
@{const SuperCalc.derivable}. Renaming would not strictly be necessary for
@{const SuperCalc.factorization} and @{const SuperCalc.reflexion}, but it does not hurt either.

If it ever cause a problem, change the structure to have access to @{type Clausal_Logic.clause} in
@{const derivable_list}.
\<close>

definition F_Inf :: "'a equation Clausal_Logic.clause inference set" where
  "F_Inf \<equiv> {Infer P (from_SuperCalc_cl (subst_cl C' \<sigma>)) | P S C \<sigma> k C'.
    derivable_list C (map to_SuperCalc_ecl (map2 subst_cls P (renamings_apart P))) S \<sigma> k C'}"

interpretation F: inference_system F_Inf .

definition entails
  :: "'a equation Clausal_Logic.clause set \<Rightarrow> 'a equation Clausal_Logic.clause set \<Rightarrow> bool"
  (infix "\<TTurnstile>e" 50) where
  "N1 \<TTurnstile>e N2 \<equiv> SuperCalc.set_entails_set (to_SuperCalc_cl ` N1) (to_SuperCalc_cl ` N2)"

interpretation G: consequence_relation "{{#}}" entails
proof unfold_locales
  show "{{#}} \<noteq> {}"
    by simp
next
  show "\<And>B N1. B \<in> {{#}} \<Longrightarrow> {B} \<TTurnstile>e N1"
    unfolding entails_def
    by (simp add: SuperCalc.set_entails_set_def to_SuperCalc_cl_def subst_cl.simps
        ground_clause.simps validate_ground_clause.simps)
next
  show "\<And>N2 N1. N2 \<subseteq> N1 \<Longrightarrow> N1 \<TTurnstile>e N2"
    unfolding entails_def
    by (auto simp add: SuperCalc.set_entails_set_def)
next
  show "\<And>N2 N1. \<forall>C\<in>N2. N1 \<TTurnstile>e {C} \<Longrightarrow> N1 \<TTurnstile>e N2"
    unfolding entails_def
    by (auto simp: SuperCalc.set_entails_set_def)
next
  show "\<And>N1 N2 N3. N1 \<TTurnstile>e N2 \<Longrightarrow> N2 \<TTurnstile>e N3 \<Longrightarrow> N1 \<TTurnstile>e N3"
    unfolding entails_def SuperCalc.set_entails_set_def
    by blast
qed

definition fclause_ord
  :: "'a equation Clausal_Logic.clause \<Rightarrow> 'a equation Clausal_Logic.clause \<Rightarrow> bool" where
  "fclause_ord C D \<equiv> ((to_SuperCalc_cl C, []), (to_SuperCalc_cl D, [])) \<in> SuperCalc.cl_ord"

interpretation Standard_Red_F:
  finitary_standard_formula_redundancy "{{#}}" "(\<TTurnstile>e)" fclause_ord
proof unfold_locales
  show "transp fclause_ord"
    unfolding fclause_ord_def
    by (auto intro: transpI SuperCalc.cl_ord_trans[THEN transD])
next
  show "wfP fclause_ord"
    unfolding fclause_ord_def wfP_def
    by (rule compat_wf[of _ _ "\<lambda>C. (to_SuperCalc_cl C, [])", OF _ SuperCalc.wf_cl_ord])
      (simp add: compat_def)
qed

abbreviation Red_F
  :: "'a equation Clausal_Logic.clause set \<Rightarrow> 'a equation Clausal_Logic.clause set" where
  "Red_F \<equiv> Standard_Red_F.Red_F"

definition Red_I
  :: "'a equation Clausal_Logic.clause set \<Rightarrow> 'a equation Clausal_Logic.clause inference set" where
  "Red_I N \<equiv> {\<iota> \<in> F_Inf.
    (let prems = map to_SuperCalc_ecl (prems_of \<iota>) in
     let concl = to_SuperCalc_ecl (concl_of \<iota>) in
     \<exists>\<sigma>. SuperCalc.redundant_inference concl (to_SuperCalc_ecl ` N) (set prems) \<sigma>)}"

lemma F_Inf_reductive: "\<iota> \<in> F_Inf \<Longrightarrow> fclause_ord (concl_of \<iota>) (main_prem_of \<iota>)"
  sorry

lemma ecl_ord_conv[simp]:
  "((Ecl C ts\<^sub>C, \<sigma>\<^sub>C), (Ecl D ts\<^sub>D, \<sigma>\<^sub>D)) \<in> SuperCalc.ecl_ord \<longleftrightarrow>
  ((C, \<sigma>\<^sub>C), (D, \<sigma>\<^sub>D)) \<in> SuperCalc.cl_ord"
  unfolding SuperCalc.cl_ord_def SuperCalc.ecl_ord_def
  by simp

sublocale calculus "{{#}}" F_Inf entails Red_I Red_F
proof unfold_locales
  show "\<And>N. Red_I N \<subseteq> F_Inf"
    unfolding Red_I_def F_Inf_def Let_def by auto
next
  show "\<And>B N. B \<in> {{#}} \<Longrightarrow> N \<TTurnstile>e {B} \<Longrightarrow> (N - Red_F N) \<TTurnstile>e {B}"
    by (fact Standard_Red_F.Red_F_Bot)
next
  show "\<And>N N'. N \<subseteq> N' \<Longrightarrow> Red_F N \<subseteq> Red_F N'"
    by (fact Standard_Red_F.Red_F_of_subset)
next
  fix N N' :: "'a equation Clausal_Logic.clause set"
  assume "N \<subseteq> N'"
  hence ecl_N_sub_ecl_N': "to_SuperCalc_ecl ` N \<subseteq> to_SuperCalc_ecl ` N'"
    by (auto intro: image_mono)
  show "Red_I N \<subseteq> Red_I N'"
  proof (rule subsetI)
    fix \<iota> :: "'a equation Clausal_Logic.clause inference"
    show "\<iota> \<in> Red_I N \<Longrightarrow> \<iota> \<in> Red_I N' "
      unfolding Red_I_def Let_def
      using SuperCalc.redundant_inference_subset_eqI[OF ecl_N_sub_ecl_N']
      by auto
  qed
next
  show "\<And>N' N. N' \<subseteq> Red_F N \<Longrightarrow> Red_F N \<subseteq> Red_F (N - N')"
    by (fact Standard_Red_F.Red_F_of_Red_F_subset)
next
  fix N N' :: "'a equation Clausal_Logic.clause set"
  assume N'_Red: "N' \<subseteq> Red_F N"
  show "Red_I N \<subseteq> Red_I (N - N')"
  proof (rule subsetI)
    fix \<iota> :: "'a equation Clausal_Logic.clause inference"
    assume "\<iota> \<in> Red_I N"
    then obtain \<sigma> where
      "\<iota> \<in> F_Inf" and
      red_inf: "SuperCalc.redundant_inference (to_SuperCalc_ecl (concl_of \<iota>)) (to_SuperCalc_ecl ` N)
        (set (map to_SuperCalc_ecl (prems_of \<iota>))) \<sigma>"
      unfolding Red_I_def by auto
    have "SuperCalc.redundant_inference (to_SuperCalc_ecl (concl_of \<iota>))
      (to_SuperCalc_ecl ` (N - N')) (set (map to_SuperCalc_ecl (prems_of \<iota>))) \<sigma>"
      using red_inf
      using N'_Red[unfolded Standard_Red_F.Red_F_def]
      sorry
    then show "\<iota> \<in> Red_I (N - N')"
      using \<open>\<iota> \<in> F_Inf\<close>
      unfolding Red_I_def Let_def
      by blast
  qed
next
  fix
    \<iota> :: "'a equation Clausal_Logic.clause inference" and
    N  :: "'a equation Clausal_Logic.clause set"
  assume in_\<iota>: "\<iota> \<in> F_Inf" and concl_in: "concl_of \<iota> \<in> N"

  from in_\<iota> obtain P S C \<sigma> k C' where
    \<iota>_def: "\<iota> = Infer P (from_SuperCalc_cl (subst_cl C' \<sigma>))" and
    deriv: "derivable_list C (map to_SuperCalc_ecl (map2 subst_cls P (renamings_apart P))) S \<sigma> k C'"
    unfolding F_Inf_def by blast

  from concl_in have "from_SuperCalc_cl (subst_cl C' \<sigma>) \<in> N"
    unfolding \<iota>_def by simp

  have "finite C'"
    by (rule SuperCalc.derivable_finite_conclusion[OF _ derivable_list_imp_derivable[OF deriv],
          simplified])
  hence to_from_subst_C'[simp]: "to_SuperCalc_cl (from_SuperCalc_cl (subst_cl C' \<sigma>)) = subst_cl C' \<sigma>"
    using to_from_SuperCalc_cl
    by (simp add: subst_cl.simps)

  obtain \<sigma>\<^sub>g where gr_C'_\<sigma>_\<sigma>\<^sub>g: "ground_clause (subst_cl (subst_cl C' \<sigma>) \<sigma>\<^sub>g)"
    by (meson \<open>finite C'\<close> ground_instance_exists substs_preserve_finiteness)
  (* Le problème est que nous n'obtenons ici qu'un seul grounding et qu'il les faut tous.
     Solution, avoir une définition qui fournisse un ensemble possiblement infini de tous les groundings.
     Si toutes les intances sont vrai, alors la formule non-ground est vrai *)

  have "\<exists>\<sigma>. SuperCalc.redundant_inference
    (to_SuperCalc_ecl (concl_of \<iota>))
    (to_SuperCalc_ecl ` N)
    (to_SuperCalc_ecl ` set (prems_of \<iota>))
    \<sigma>"
    unfolding SuperCalc.redundant_inference_def
    apply (rule exI[where x = "[]"])
    unfolding SuperCalc.redundant_inference_def
    apply simp
    (* Pas bien: Ici il faut instancier avec l'ensemble de tou les groundings *)
    apply (rule exI[where x = "{(to_SuperCalc_ecl (concl_of \<iota>), \<sigma>\<^sub>g)}"])
  proof (intro conjI)
    show "{(to_SuperCalc_ecl (concl_of \<iota>), \<sigma>\<^sub>g)} \<subseteq> SuperCalc.instances (to_SuperCalc_ecl ` N)"
      apply (simp add: SuperCalc.instances_def)
      apply (rule bexI[where x = "concl_of \<iota>"])
      using gr_C'_\<sigma>_\<sigma>\<^sub>g concl_in
      by (auto simp: \<iota>_def)
  next
    show "set_entails_clause (SuperCalc.clset_instances {(to_SuperCalc_ecl (concl_of \<iota>), \<sigma>\<^sub>g)})
      (to_SuperCalc_cl (concl_of \<iota>))"
      apply (simp add: \<iota>_def SuperCalc.clset_instances_def)
      unfolding set_entails_clause_def (* SHOW Sophie here *)
      apply simp
      apply safe
      unfolding validate_ground_clause.simps
      using gr_C'_\<sigma>_\<sigma>\<^sub>g
      sorry
  next
    show "\<forall>x\<in>{(to_SuperCalc_ecl (concl_of \<iota>), \<sigma>\<^sub>g)}.
      SuperCalc.subterms_inclusion (subst_set (trms_ecl (fst x)) (snd x)) {}"
      by (simp add: SuperCalc.subst_set_image_conv SuperCalc.subterms_inclusion_def)
  next
    have "P \<noteq> []" sorry
    show "\<forall>x\<in>{(to_SuperCalc_ecl (concl_of \<iota>), \<sigma>\<^sub>g)}.
     \<exists>D'\<in>set (prems_of \<iota>). (x, to_SuperCalc_ecl D', []) \<in> SuperCalc.ecl_ord"
      apply (simp add: \<iota>_def)
      apply (rule bexI[where x = "main_prem_of \<iota>"])
       apply (simp_all add: \<iota>_def last_in_set[OF \<open>P \<noteq> []\<close>])
      using F_Inf_reductive
      using F_Inf_reductive[OF in_\<iota>, unfolded fclause_ord_def \<iota>_def, simplified]
      (* SHOW Sophie here *)
      using derivable_list_imp_derivable[OF deriv]
      using SuperCalc.redundant_inference_clause
      sorry
  qed

  then show "\<iota> \<in> Red_I N"
    by (simp add: Red_I_def in_\<iota>)
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

lemma is_renaming_imp_renaming:
  fixes \<sigma> :: "('a \<times> 'a trm) list" and S :: "'a set"
  shows "is_renaming \<sigma> \<Longrightarrow> renaming \<sigma> S"
  unfolding is_renaming_def
  by (auto elim: comp.elims)

sublocale statically_complete_calculus "{{#}}" F_Inf entails Red_I Red_F
proof unfold_locales
  fix B and N :: "'a equation Clausal_Logic.clause set"
  assume "B \<in> {{#}}" and "saturated N" and "N \<TTurnstile>e {B}"
  hence B_def: "B = {#}" by simp

  \<comment> \<open>We close @{term N} under \<alpha>-renaming.\<close>
  \<comment> \<open>We cannot use @{const is_renaming} because we would need
  @{term "\<And>\<sigma> S. is_renaming \<sigma> \<longleftrightarrow> renaming \<sigma> S"} but only the forward direction holds.\<close>
  define N' :: "'a equation Clausal_Logic.clause set" where
    "N' \<equiv> { subst_cls C \<sigma> | C \<sigma>. C \<in> N \<and> renaming \<sigma> (vars_of_cl (to_SuperCalc_cl C))}"

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

  from \<open>saturated N\<close> have sat_N_alt: "\<And>\<iota>. \<iota> \<in> F_Inf \<Longrightarrow> set (prems_of \<iota>) \<subseteq> N \<Longrightarrow> \<iota> \<in> Red_I N"
    unfolding saturated_def F.Inf_from_def
    by (auto dest: Set.subsetD)

  \<comment> \<open>Still not used?\<close>
  have "saturated N'"
    unfolding saturated_def
  proof (rule Set.subsetI)
    fix \<iota>' :: "'a equation Clausal_Logic.clause inference"
    obtain Ps' C' where \<iota>'_def: "\<iota>' = Infer Ps' C'"
      by (cases \<iota>') simp
    assume "\<iota>' \<in> F.Inf_from N'"
    hence "\<iota>' \<in> F_Inf" and "set Ps' \<subseteq> N'"
      unfolding F.Inf_from_def Set.mem_Collect_eq
      by (simp_all add: \<iota>'_def)
    have "\<forall>P' \<in> N'. \<exists>P. P \<in> N \<and> (\<exists>\<sigma>.
      P' = subst_cls P \<sigma> \<and> renaming \<sigma> (vars_of_cl (to_SuperCalc_cl P)))"
      unfolding N'_def
      by blast
    hence "\<forall>P' \<in> set Ps'. \<exists>P. P \<in> N \<and> (\<exists>\<sigma>.
      P' = subst_cls P \<sigma> \<and> renaming \<sigma> (vars_of_cl (to_SuperCalc_cl P)))"
      using \<open>set Ps' \<subseteq> N'\<close>
      by blast
    hence *: "list_all (\<lambda>P'. \<exists>P. P \<in> N \<and> (\<exists>\<sigma>.
      P' = subst_cls P \<sigma> \<and> renaming \<sigma> (vars_of_cl (to_SuperCalc_cl P)))) Ps'"
      by (simp add: Ball_set)

    from * have "\<exists>Ps \<sigma>s. Ps' = map2 (subst_cls) Ps \<sigma>s \<and> set Ps \<subseteq> N \<and>
      list_all2 (\<lambda>P \<sigma>. renaming \<sigma> (vars_of_cl (to_SuperCalc_cl P))) Ps \<sigma>s"
    proof (induction Ps')
      case Nil
      show ?case
        apply (rule exI[of _ "[]"])
        apply (rule exI[of _ "[]"])
        by simp
    next
      case (Cons P' Ps')
      from Cons.prems obtain P \<sigma> where
        P_mem_N: "P \<in> N" and
        P'_def: "P' = subst_cls P \<sigma>" and
        renaming_\<sigma>: "renaming \<sigma> (vars_of_cl (to_SuperCalc_cl P))" and
        all_Ps': "list_all (\<lambda>P'. \<exists>P. P \<in> N \<and> (\<exists>\<sigma>. P' = subst_cls P \<sigma> \<and>
          renaming \<sigma> (vars_of_cl (to_SuperCalc_cl P)))) Ps'"
        by auto
      from Cons.IH[OF all_Ps'] obtain Ps \<sigma>s where
        Ps_subseteq_N: "set Ps \<subseteq> N" and
        Ps'_def: "Ps' = Map2.map2 subst_cls Ps \<sigma>s" and
        renaming_\<sigma>s: "list_all2 (\<lambda>P \<sigma>. renaming \<sigma> (vars_of_cl (to_SuperCalc_cl P))) Ps \<sigma>s"
        by auto
      show ?case
      proof (intro exI conjI)
        show "P' # Ps' = Map2.map2 subst_cls (P # Ps) (\<sigma> # \<sigma>s)"
          using P'_def Ps'_def by simp
      next
        show "set (P # Ps) \<subseteq> N"
          using P_mem_N Ps_subseteq_N by simp
      next
        show "list_all2 (\<lambda>P \<sigma>. renaming \<sigma> (vars_of_cl (to_SuperCalc_cl P))) (P # Ps) (\<sigma> # \<sigma>s)"
          using renaming_\<sigma> renaming_\<sigma>s by simp
      qed
    qed

    then obtain Ps \<sigma>s where
      Ps'_def: "Ps' = map2 (subst_cls) Ps \<sigma>s" and
      Ps_subseteq_N: "set Ps \<subseteq> N" and
      "list_all2 (\<lambda>P \<sigma>. renaming \<sigma> (vars_of_cl (to_SuperCalc_cl P))) Ps \<sigma>s"
      by auto

    define \<iota> :: "'a equation Clausal_Logic.clause inference" where
      "\<iota> = Infer Ps C'"

    from \<open>\<iota>' \<in> F_Inf\<close> have "\<iota> \<in> F_Inf"
    proof -
      from \<open>\<iota>' \<in> F_Inf\<close> obtain S C \<sigma> k C'a where
        C'_def: "C' = from_SuperCalc_cl (subst_cl C'a \<sigma>)" and
        deriv_list_C: "derivable_list C (map to_SuperCalc_ecl (Map2.map2 subst_cls Ps' (renamings_apart Ps')))
          S \<sigma> k C'a"
        unfolding \<iota>'_def F_Inf_def
        unfolding Set.mem_Collect_eq
        by auto
      have "cl_ecl C = subst_cl C'a \<sigma>"
        using derivable_list_imp_derivable[OF deriv_list_C] SuperCalc.derivable_clauses_lemma
        by blast
      show "\<iota> \<in> F_Inf"
        unfolding \<iota>_def F_Inf_def
        unfolding Set.mem_Collect_eq
        apply (rule exI[of _ Ps])
        apply (rule exI[of _ S])
        apply (rule exI[of _ C])
        apply (rule exI[of _ \<sigma>])
        apply (rule exI[of _ k])
        apply (rule exI[of _ C'a])
        apply (simp add: C'_def)
        using deriv_list_C[unfolded derivable_list_def]
      proof (elim disjE bexE conjE)
        fix P1
        assume "P1 \<in> S" and
          eq_P1: "map to_SuperCalc_ecl (Map2.map2 subst_cls Ps' (renamings_apart Ps')) = [P1]"
        from eq_P1 have "length Ps' = Suc 0"
          
        proof (induction Ps')
          case Nil
          then show ?case by simp
        next
          case (Cons a Ps')
          then show ?case
            sledgehammer
            sorry
        qed
        
        show "SuperCalc.factorization P1 C \<sigma> k
           C'a \<Longrightarrow>
          derivable_list C
           (map (to_SuperCalc_ecl \<circ>
                 (\<lambda>(x, y). subst_cls x y))
             (zip Ps (renamings_apart Ps)))
           S \<sigma> k C'a"
          sorry
      next
        show "\<And>P1 P2.
       P1 \<in> S \<Longrightarrow>
       P2 \<in> S \<Longrightarrow>
       map to_SuperCalc_ecl
        (Map2.map2 subst_cls Ps'
          (renamings_apart Ps')) =
       [P2, P1] \<Longrightarrow>
       SuperCalc.superposition P1 P2 C \<sigma> k
        C'a \<Longrightarrow>
       derivable_list C
        (map (to_SuperCalc_ecl \<circ>
              (\<lambda>(x, y). subst_cls x y))
          (zip Ps (renamings_apart Ps)))
        S \<sigma> k C'a" sorry
      next
        show "\<And>P1. P1 \<in> S \<Longrightarrow>
          map to_SuperCalc_ecl
           (Map2.map2 subst_cls Ps'
             (renamings_apart Ps')) =
          [P1] \<Longrightarrow>
          SuperCalc.reflexion P1 C \<sigma> k C'a \<Longrightarrow>
          derivable_list C
           (map (to_SuperCalc_ecl \<circ>
                 (\<lambda>(x, y). subst_cls x y))
             (zip Ps (renamings_apart Ps)))
           S \<sigma> k C'a " sorry
      qed
    hence "\<iota> \<in> Red_I N"
      using sat_N_alt \<iota>_def Ps_subseteq_N by simp

    have "\<exists>\<sigma>. SuperCalc.redundant_inference (to_SuperCalc_ecl C') (to_SuperCalc_ecl ` N')
      (set (map to_SuperCalc_ecl Ps')) \<sigma>"
      using \<open>\<iota> \<in> Red_I N\<close>[unfolded Red_I_def, simplified]
      unfolding SuperCalc.redundant_inference_def
      apply simp
      apply safe
      sorry

    then show "\<iota>' \<in> Red_I N'"
      using \<open>\<iota>' \<in> F_Inf\<close>
      using \<iota>'_def N'_def
      unfolding Red_I_def Let_def Set.mem_Collect_eq
      by simp
  qed
  have gr_inf_satur_N': "SuperCalc.ground_inference_saturated (to_SuperCalc_ecl ` N')"
    unfolding SuperCalc.ground_inference_saturated_def
  proof (intro allI impI)
    fix C P \<sigma> C'
    assume deriv_C_P: "SuperCalc.derivable C P (to_SuperCalc_ecl ` N') \<sigma> SuperCalc.Ground C'"
    show "ground_clause (cl_ecl C) \<Longrightarrow> SuperCalc.grounding_set P \<sigma> \<Longrightarrow>
      SuperCalc.redundant_inference C (to_SuperCalc_ecl ` N') P \<sigma>"
      using \<open>saturated N'\<close>[unfolded saturated_def, THEN Set.subsetD]
      using deriv_C_P[THEN SuperCalc.derivable_premisses]
      sorry
  qed

  have ball_well_constrained_N': "Ball (to_SuperCalc_ecl ` N') SuperCalc.well_constrained"
    by (simp add: SuperCalc.well_constrained_def)

  have closed_renaming_N': "closed_under_renaming (to_SuperCalc_ecl ` N')"
    unfolding N'_def by (fact closed_under_renaming_closure)

  note int_clset_is_a_model' = SuperCalc.int_clset_is_a_model[OF gr_inf_satur_N' all_finite_N'
      ball_well_constrained_N' _ closed_renaming_N', rule_format]

  define I where "I \<equiv> SuperCalc.same_values (\<lambda>t. SuperCalc.trm_rep t (to_SuperCalc_ecl ` N'))"

  have fo_int_I: "fo_interpretation I"
    unfolding I_def
    using SuperCalc.same_values_fo_int SuperCalc.trm_rep_compatible_with_structure by blast

  obtain C \<sigma> where
    C_in_N': "C \<in> to_SuperCalc_ecl ` N'" and
    gr_cl_C_\<sigma>: "ground_clause (subst_cl (cl_ecl C) \<sigma>)" and
    not_val_gr_cl_C_\<sigma>: "\<not> validate_ground_clause I (subst_cl (cl_ecl C) \<sigma>)"
    using \<open>N' \<TTurnstile>e {{#}}\<close>[unfolded entails_def SuperCalc.set_entails_set_def,
        rule_format, OF fo_int_I, simplified]
    sorry

  have "trms_ecl C = {}"
    using C_in_N'[unfolded N'_def] by force
  hence all_trms_irreducible: "SuperCalc.all_trms_irreducible
    (subst_set (trms_ecl C) \<sigma>) (\<lambda>t. SuperCalc.trm_rep t (to_SuperCalc_ecl ` N'))"
    by (simp add: subst_set.simps)

  have "\<not> (\<forall>x\<in>to_SuperCalc_ecl ` N'. cl_ecl x \<noteq> {})"
    by (rule contrapos_nn[OF not_val_gr_cl_C_\<sigma>])
      (auto simp: I_def intro: int_clset_is_a_model'[of "(C, \<sigma>)" C \<sigma>,
          OF _ _ _ C_in_N' gr_cl_C_\<sigma> all_trms_irreducible, simplified])
  then obtain C' where
    "Ecl (to_SuperCalc_cl C') {} \<in> to_SuperCalc_ecl ` N'" and
    "cl_ecl (Ecl (to_SuperCalc_cl C') {}) = {}"
    by blast
  then obtain C where "Ecl (to_SuperCalc_cl C) {} \<in> to_SuperCalc_ecl ` N" and
    "cl_ecl (Ecl (to_SuperCalc_cl C) {}) = {}"
    by (auto simp: N'_def to_SuperCalc_cl_def)
  hence "C \<in> N" and "C = {#}"
    by (auto simp: to_SuperCalc_cl_def)
  thus "\<exists>B\<in>{{#}}. B \<in> N"
    by simp
qed

end

end
