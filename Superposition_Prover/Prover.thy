theory Prover
  imports
    SuperCalc.superposition
    Saturation_Framework.Calculus
    Saturation_Framework_Extensions.Standard_Redundancy_Criterion
    "HOL-Library.FSet"
begin

(*
1. use fset (HOL-Libary) or multiset (HOL-Library) instead of set for clauses here.
2. sorry for compactness proof. (probably long and annoying)
3. do the rest up to instantiation.
4. prove compactness.

if 4. fails, maybe redefine standard redundancy criteria to try to not need compactness.
*)


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

lemma irrefl_mult:
  assumes "irrefl R" "trans R"
  shows "irrefl (mult R)"
proof (intro irreflI notI)
  fix X
  assume "(X, X) \<in> mult R"
  then show False
    using add.commute assms(1) assms(2) mult_cancel mult_implies_one_step
      subset_mset.zero_eq_add_iff_both_eq_0
    by metis
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
    using irrefl_mult[OF irrefl_mult[OF trm_ord_irrefl trm_ord_trans] mult_trm_ord_trans]
    unfolding irrefl_def
    by simp
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

(* lemma
  assumes ren_\<sigma>\<^sub>1: "renaming \<sigma>\<^sub>1 vs" and ren_\<sigma>\<^sub>2: "renaming \<sigma>\<^sub>2 vs"
  shows "renaming (\<sigma>\<^sub>1 \<lozenge> \<sigma>\<^sub>2) vs"
proof -
  from ren_\<sigma>\<^sub>1 have
    all_var_\<sigma>\<^sub>1: "\<forall>x\<in>vs. is_a_variable (Var x \<lhd> \<sigma>\<^sub>1)" and
    "\<forall>x y. x \<in> vs \<longrightarrow> y \<in> vs \<longrightarrow> x \<noteq> y \<longrightarrow> Var x \<lhd> \<sigma>\<^sub>1 \<noteq> Var y \<lhd> \<sigma>\<^sub>1"
    unfolding renaming_def by simp_all
  from ren_\<sigma>\<^sub>2 have
    all_var_\<sigma>\<^sub>2: "\<forall>x\<in>vs. is_a_variable (Var x \<lhd> \<sigma>\<^sub>2)" and
    "\<forall>x y. x \<in> vs \<longrightarrow> y \<in> vs \<longrightarrow> x \<noteq> y \<longrightarrow> Var x \<lhd> \<sigma>\<^sub>2 \<noteq> Var y \<lhd> \<sigma>\<^sub>2"
    unfolding renaming_def by simp_all

  from all_var_\<sigma>\<^sub>1 have all_var_\<sigma>\<^sub>1': "\<forall>x\<in>vs. \<exists>y. Var x \<lhd> \<sigma>\<^sub>1 = Var y"
    by (meson is_a_variable.elims(2))

  show ?thesis
    unfolding renaming_def
  proof (intro conjI ballI allI impI)
    fix v
    assume "v \<in> vs"
    show "is_a_variable (Var v \<lhd> \<sigma>\<^sub>1 \<lozenge> \<sigma>\<^sub>2)"
      apply simp
      using all_var_\<sigma>\<^sub>1'[rule_format, OF \<open>v \<in> vs\<close>] apply simp
      apply safe
      apply simp
      using all_var_\<sigma>\<^sub>2
      oops *)

(* lemma transp_renaming_cl: "transp renaming_cl"
proof (rule transpI)
  fix C D E
  assume "renaming_cl C D" and "renaming_cl D E"
  then obtain \<sigma>\<^sub>1 \<sigma>\<^sub>2 where
    ren_\<sigma>\<^sub>1: "renaming \<sigma>\<^sub>1 (vars_of_cl (cl_ecl C))" and
    ren_\<sigma>\<^sub>2: "renaming \<sigma>\<^sub>2 (vars_of_cl (cl_ecl D))" and
    D_def: "D = subst_ecl C \<sigma>\<^sub>1" and
    E_def: "E = subst_ecl D \<sigma>\<^sub>2"
    unfolding renaming_cl_def
    by blast
  show "renaming_cl C E"
    unfolding renaming_cl_def
  proof (intro exI conjI)
    show "renaming (\<sigma>\<^sub>1 \<lozenge> \<sigma>\<^sub>2) (vars_of_cl (cl_ecl C))"
      using ren_\<sigma>\<^sub>1 ren_\<sigma>\<^sub>2
      (* This is sadly not true as the second argument to renaming should also contain substituted
          variables from \<sigma>\<^sub>1. *)
      sorry
  next
    show "E = subst_ecl C (\<sigma>\<^sub>1 \<lozenge> \<sigma>\<^sub>2)"
      using D_def E_def by simp
  qed
qed *)

(* lemma
  fixes N :: "'a eclause set"and C :: "'a eclause"
  assumes saturated_N: "inference_saturated N" and deriv_C: "derivable_ecl C N"
  shows "C \<in> N \<or> (\<exists>C'. C' \<in> N \<and> renaming_cl C' C)"
  using deriv_C saturated_N
proof (induction C N rule: derivable_ecl.induct)
  case (init C N)
  thus ?case by simp
next
  case (rn C N D)
  show ?case
  proof (rule disjI2, rule rn.IH[OF rn.prems, THEN disjE]; (elim exE conjE)?)
    assume "C \<in> N"
    thus "\<exists>E. E \<in> N \<and> renaming_cl E D"
      using rn.hyps by fast
  next
    fix E
    show "E \<in> N \<Longrightarrow> renaming_cl E C \<Longrightarrow> \<exists>E. E \<in> N \<and> renaming_cl E D"
      (* using rn.hyps transp_renaming_cl[THEN transpD, of E C D]
      by blast *)
      sorry
  qed
next
  case (deriv P S C S' \<sigma> C')
  show ?case
    apply (cases "C \<in> S")
     apply simp
    using deriv.hyps
    using deriv.prems
    using deriv.IH[rule_format]
  oops *)
  
(* lemma
  fixes C' \<sigma>
  defines "eC' \<equiv> Ecl (subst_cl C' \<sigma>) {}"
  assumes
    in_N: "eC' \<in> N" and
    ball_S_fin_cl: "\<forall>x\<in>S. finite (cl_ecl x)" and
    "derivable C P S \<sigma> Ground C'"
  shows "\<exists>\<eta>. redundant_inference eC' N P \<eta>"
  unfolding redundant_inference_def
proof (intro exI conjI ballI)
  show "instances {eC'} \<subseteq> instances N"
    using in_N by (simp add: instances_subset_eqI)
next
  show "set_entails_clause (clset_instances (instances {eC'})) (cl_ecl eC')"
    by (auto intro: set_entails_clause_member)
next
  fix x
  assume "x \<in> instances {eC'}"
  then obtain \<eta> where x_def: "x = (eC', \<eta>)"
    unfolding instances_def by blast
  show "subterms_inclusion (subst_set (trms_ecl (fst x)) (snd x)) (trms_ecl eC')"
    by (simp add: x_def eC'_def subterms_inclusion_refl)
next
  fix x
  assume "x \<in> instances {eC'}"
  then obtain \<eta> where x_def: "x = (eC', \<eta>)"
    unfolding instances_def by blast
  show "\<exists>D'\<in>P. ((fst x, snd x), D', \<sigma>) \<in> ecl_ord"
    apply (simp add: x_def)
    using \<open>derivable C P S \<sigma> Ground C'\<close>
    unfolding ecl_ord_def mem_Collect_eq case_prod_beta prod.sel
    using conclusion_is_smaller_than_premisses[OF \<open>derivable C P S \<sigma> Ground C'\<close> ball_S_fin_cl]
    unfolding mset_ecl.simps mset_cl.simps
    unfolding eC'_def cl_ecl.simps
    find_theorems "derivable _ _ _ _ Ground" *)
    

end

subsection \<open>Prover\<close>

locale superposition_prover =
    SuperCalc: basic_superposition trm_ord sel pos_ord "UNIV :: 'a set" "\<lambda>_ _. {}"
  for
    \<comment> \<open>For SuperCalc\<close>
    trm_ord :: "('a trm \<times> 'a trm) set" and
    sel :: "'a literal set \<Rightarrow> 'a literal set" and
    pos_ord :: "'a eclause \<Rightarrow> 'a trm \<Rightarrow> (indices list \<times> indices list) set" +
  
  fixes
    \<comment> \<open>For the Framework\<close>
    Bot :: "'f set" and
    entails :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" and
    Red_F :: "'f set \<Rightarrow> 'f set" and

    \<comment> \<open>Glue between the Framework and SuperCalc\<close>
    formula_to_eclause :: "'f \<Rightarrow> 'a eclause" and
    eclause_to_formula :: "'a eclause \<Rightarrow> 'f"

  assumes
    infinite_vars: "\<not> finite (UNIV :: 'a set)" and

    formula_has_empty_trms: "\<And>f. trms_ecl (formula_to_eclause f) = {}" and
    formula_has_finite_cl: "\<And>f. finite (cl_ecl (formula_to_eclause f))" and
    entails_bottom_imp_unsatisfiable: "\<And>B N.
      B \<in> Bot \<Longrightarrow> entails N {B} \<Longrightarrow> \<not> satisfiable_clause_set (cl_ecl ` formula_to_eclause ` N)" and
    empty_cl_imp_formula_in_Bot: "\<And>C. cl_ecl C = {} \<Longrightarrow> eclause_to_formula C \<in> Bot" and
    eclause_mem_conv: "\<And>C N. eclause_to_formula C \<in> N \<Longrightarrow> C \<in> formula_to_eclause ` N" and
    cl_formula_eclause_conv: "\<And> C. cl_ecl (formula_to_eclause (eclause_to_formula C)) = cl_ecl C"
begin

definition Inf where
  "Inf \<equiv> {Infer P (eclause_to_formula (Ecl (subst_cl C' \<sigma>) {})) | P S C \<sigma> k C'.
    SuperCalc.derivable C (formula_to_eclause ` set P) S \<sigma> k C'}"

definition Red_I where
  "Red_I N \<equiv> {\<iota> \<in> Inf.
    (let prems = formula_to_eclause ` (set (prems_of \<iota>)) in
     let concl = formula_to_eclause (concl_of \<iota>) in
     \<exists>\<sigma>. SuperCalc.redundant_inference concl (formula_to_eclause ` N) prems \<sigma>)}"

sublocale inference_system Inf .

sublocale consequence_relation Bot entails
proof unfold_locales
  show "Bot \<noteq> {}" sorry
next
  show "\<And>B N1. B \<in> Bot \<Longrightarrow> entails {B} N1" sorry
next
  show "\<And>N2 N1. N2 \<subseteq> N1 \<Longrightarrow> entails N1 N2" sorry
next
  show "\<And>N2 N1. \<forall>C\<in>N2. entails N1 {C} \<Longrightarrow> entails N1 N2" sorry
next
  show "\<And>N1 N2 N3. entails N1 N2 \<Longrightarrow> entails N2 N3 \<Longrightarrow> entails N1 N3" sorry
qed

lemma False
  by (metis Collect_mem_eq eclause_mem_conv empty_Collect_eq formula_has_empty_trms image_iff insert_iff trms_ecl.simps)

sublocale calculus Bot Inf entails Red_I Red_F
proof unfold_locales
  show "\<And>N. Red_I N \<subseteq> Inf"
    unfolding Red_I_def Inf_def Let_def by auto
next
  show "\<And>B N. B \<in> Bot \<Longrightarrow> entails N {B} \<Longrightarrow> entails (N - Red_F N) {B}" sorry
next
  show "\<And>N N'. N \<subseteq> N' \<Longrightarrow> Red_F N \<subseteq> Red_F N'" sorry
next
  show "\<And>N N'. N \<subseteq> N' \<Longrightarrow> Red_I N \<subseteq> Red_I N'" sorry
next
  show "\<And>N' N. N' \<subseteq> Red_F N \<Longrightarrow> Red_F N \<subseteq> Red_F (N - N')" sorry
next
  show "\<And>N' N. N' \<subseteq> Red_F N \<Longrightarrow> Red_I N \<subseteq> Red_I (N - N')" sorry
next
  show "\<And>\<iota> N. \<iota> \<in> Inf \<Longrightarrow> concl_of \<iota> \<in> N \<Longrightarrow> \<iota> \<in> Red_I N"
    unfolding Red_I_def Inf_def
    apply (simp del: subst_cl.simps)
    apply (auto simp del: subst_cl.simps)
    subgoal premises prems for N P S C \<sigma> k C'
      apply (rule exI[where x = \<sigma>])
      unfolding SuperCalc.redundant_inference_def
      proof (intro exI conjI ballI)
        show "SuperCalc.instances {Ecl (subst_cl C' \<sigma>) {}} \<subseteq> SuperCalc.instances (formula_to_eclause ` N)"
          apply (rule SuperCalc.instances_subset_eqI)
          using prems(1)[THEN eclause_mem_conv]
          by simp
      next
        show "set_entails_clause
          (SuperCalc.clset_instances (SuperCalc.instances {Ecl (subst_cl C' \<sigma>) {}}))
          (cl_ecl (formula_to_eclause (eclause_to_formula (Ecl (subst_cl C' \<sigma>) {}))))"
          unfolding cl_formula_eclause_conv
          unfolding cl_ecl.simps
          apply (rule set_entails_clause_member)
          unfolding SuperCalc.instances_def
          apply (simp del: subst_cl.simps ground_clause.simps add: composition_of_substs_cl)
          unfolding SuperCalc.clset_instances_def
          apply (simp del: subst_cl.simps ground_clause.simps)
          sorry
      next
        show "\<And>x. x \<in> SuperCalc.instances {Ecl (subst_cl C' \<sigma>) {}} \<Longrightarrow>
          SuperCalc.subterms_inclusion
            (subst_set (trms_ecl (fst x)) (snd x))
            (trms_ecl (formula_to_eclause (eclause_to_formula (Ecl (subst_cl C' \<sigma>) {}))))"
          sorry
      next
        show "\<And>x. x \<in> SuperCalc.instances {Ecl (subst_cl C' \<sigma>) {}} \<Longrightarrow>
          \<exists>D'\<in>formula_to_eclause ` set P. ((fst x, snd x), D', \<sigma>) \<in> SuperCalc.ecl_ord "
          sorry
      qed
      done
qed

lemma empty_trms: "\<forall>x. x \<in> formula_to_eclause ` N \<longrightarrow> trms_ecl x = {}"
  using formula_has_empty_trms by blast

lemma finite_cl: "\<forall>x\<in>formula_to_eclause ` N. finite (cl_ecl x)"
    using formula_has_finite_cl by blast

lemma ball_well_constrained: "\<forall>C \<in> formula_to_eclause ` N. SuperCalc.well_constrained C"
  by (auto simp add: SuperCalc.well_constrained_def formula_has_empty_trms)

sublocale statically_complete_calculus Bot Inf entails Red_I Red_F
proof unfold_locales
  fix B N
  assume "B \<in> Bot" and "saturated N" and "entails N {B}"

  have unsat_N: "\<not> satisfiable_clause_set (cl_ecl ` formula_to_eclause ` N)"
    by (rule entails_bottom_imp_unsatisfiable[OF \<open>B \<in> Bot\<close> \<open>entails N {B}\<close>])

  have gr_inf_satur_N: "SuperCalc.ground_inference_saturated (formula_to_eclause ` N)"
    using \<open>saturated N\<close>
    sorry

  obtain C where
    derivable_C: "SuperCalc.derivable_ecl C (formula_to_eclause ` N)" and
    empty_cl_C: "cl_ecl C = {}"
    using SuperCalc.COMPLETENESS[of "formula_to_eclause ` N", OF empty_trms finite_cl unsat_N]
    thm SuperCalc.int_clset_is_a_model[of "formula_to_eclause ` N",
            OF gr_inf_satur_N finite_cl ball_well_constrained]
    by blast

  show "\<exists>B'\<in>Bot. B' \<in> N"
  proof (rule bexI)
    show "eclause_to_formula C \<in> N"
      using \<open>saturated N\<close>
      unfolding saturated_def
      unfolding Inf_from_def
      unfolding Red_I_def Let_def
      unfolding Collect_mono_iff
      using derivable_C
      using Inf_def
      using SuperCalc.derivable_ecl.induct
      sorry
  next
    show "eclause_to_formula C \<in> Bot"
      by (rule empty_cl_imp_formula_in_Bot[OF empty_cl_C])
  qed
qed

end


subsection \<open>Generic lemmas about SuperCalc without constraints\<close>

abbreviation ecl where
  "ecl C \<equiv> Ecl C {}"

lemma redundant_inference_member:
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
  ultimately have "X' = Ecl C {}" and ground: "ground_clause (subst_cl C \<sigma>\<^sub>X)"
    unfolding instances_def by force+
  show "\<exists>D'\<in>prems. ((fst X, snd X), D', \<sigma>) \<in> ecl_ord"
    unfolding X_def fst_conv snd_conv
    (* using deriv conclusion_is_smaller_than_premisses *)
    using deriv[unfolded derivable_def]
    apply (elim disjE exE conjE)
    (* Search in SuperCalc for occurences of "\<in> ecl_ord" or "effective".
       Maybe (probably?) Nicolas already proved something similar. *)
    sorry
qed


subsection \<open>Finite clauses\<close>

(* First try to refactor the Framework extension locale and see if this is still needed afterward. *)
(* redefine 'b equation as unordered pair (using uprod from HOL-Library), same thing with literal *)
(* define mapping between these and SuperCalc's ones *)

(* if < on terms is total, use canonical representation instead of SOME *)
term "SOME x. P x"
term "\<exists>x. P x"

type_synonym 'b fclause = "'b literal fset"

(* We need an injective mapping clause to clause, where all variables have been replaced by fresh
constants. *)

definition ground_inj where
  "ground_inj \<equiv> id" (* FIXME: obviously not id *)

print_locale preorder

(* definition fcl_of_cl where
  "fcl_of_cl C = Abs_fset (image flit_of_lit C)" *)

definition fcl_ord where
  "fcl_ord R \<equiv> {(Abs_fset C, Abs_fset D) | C D.
    ((ground_inj C, []), (ground_inj D, [])) \<in> R \<and> finite C \<and> finite D}"

lemma fcl_ord_refl:
  assumes "refl R"
  shows "refl (fcl_ord R)"
proof (rule refl_onI)
  fix x
  have "((fset x, []), (fset x, [])) \<in> R"
    by (rule refl_onD[OF \<open>refl R\<close>, simplified])
  then show "(x, x) \<in> fcl_ord R"
    unfolding fcl_ord_def ground_inj_def id_def
    using finite_fset fset_inverse
    by fastforce
qed simp

lemma fcl_ord_trans:
  assumes "trans R"
  shows "trans (fcl_ord R)"
proof (rule transI)
  fix X Y Z
  assume "(X, Y) \<in> fcl_ord R" and "(Y, Z) \<in> fcl_ord R"
  hence X_Y: "((fset X, []), (fset Y, [])) \<in> R" and Y_Z: "((fset Y, []), (fset Z, [])) \<in> R"
    unfolding fcl_ord_def ground_inj_def id_def
    by (smt (verit, best) fset_cases fset_inverse mem_Collect_eq prod.inject)+
  show "(X, Z) \<in> fcl_ord R"
    unfolding fcl_ord_def ground_inj_def id_def
    using \<open>trans R\<close>[THEN transD, OF X_Y Y_Z]
    by (metis (mono_tags, lifting) finite_fset fset_inverse mem_Collect_eq)
qed

lemma fcl_ord_antisym:
  assumes "antisym R"
  shows "antisym (fcl_ord R)"
proof (rule antisymI)
  fix X Y
  assume "(X, Y) \<in> fcl_ord R" and "(Y, X) \<in> fcl_ord R"
  hence X_Y: "((fset X, []), (fset Y, [])) \<in> R" and Y_X: "((fset Y, []), (fset X, [])) \<in> R"
    unfolding fcl_ord_def ground_inj_def id_def
    by (smt (verit, best) fset_cases fset_inverse mem_Collect_eq prod.inject)+
  show "X = Y"
    using antisymD[OF \<open>antisym R\<close> X_Y Y_X]
    by (simp add: fset_cong)
qed

lemma fcl_ord_wf:
  assumes "wf R"
  shows "wf (fcl_ord R)"
proof (rule wfUNIVI)
  fix P :: "'b fset \<Rightarrow> bool" and X :: "'b fset"
  assume "\<forall>x. (\<forall>y. (y, x) \<in> fcl_ord R \<longrightarrow> P y) \<longrightarrow> P x"
  hence IH: "\<And>X. (\<And>Y. ((fset Y, []), (fset X, [])) \<in> R \<Longrightarrow> P Y) \<Longrightarrow> P X"
    unfolding fcl_ord_def ground_inj_def id_def
    by (smt (verit) Abs_fset_inverse mem_Collect_eq prod.inject)

  show "P X"
    apply (induction rule: IH)
    apply (induction rule: wf_induct[OF \<open>wf R\<close>, rule_format])
    using IH by blast
qed

definition fclause_less where
  "fclause_less A B \<equiv> (A, B) \<in> fcl_ord cl_ord"

definition fclause_less_eq where
  "fclause_less_eq A B \<equiv> (A, B) \<in> fcl_ord (cl_ord\<^sup>=)"

interpretation fclause_preorder: preorder fclause_less_eq fclause_less
proof (unfold_locales)
  show "\<And>x y. fclause_less x y = (fclause_less_eq x y \<and> \<not> fclause_less_eq y x)"
    unfolding fclause_less_def fclause_less_eq_def
    unfolding fcl_ord_def
    unfolding cl_ord_iff_reflcl_cl_ord_and_not
    using Abs_fset_inject by fastforce
next
  show "\<And>X. fclause_less_eq X X"
    unfolding fclause_less_eq_def
    by (auto intro: fcl_ord_refl[THEN refl_onD, simplified])
next
  have "trans (cl_ord\<^sup>=)"
    using cl_ord_trans by simp
  then show "\<And>X Y Z. fclause_less_eq X Y \<Longrightarrow> fclause_less_eq Y Z \<Longrightarrow> fclause_less_eq X Z"
    unfolding fclause_less_eq_def
    by (auto elim: fcl_ord_trans[THEN transD])
qed

lemma wfP_fclause_less: "wfP fclause_less"
  apply (rule wfPUNIVI[rule_format])
  unfolding fclause_less_def
  using fcl_ord_wf[OF wf_cl_ord]
  by (metis wf_induct)

subsection \<open>Massaging of SuperCalc\<close>

definition Bot :: "'a fclause set" where
  "Bot \<equiv> {{||}}"

definition set_entails_set where
  "set_entails_set S C \<longleftrightarrow>
    (\<forall>I. fo_interpretation I \<longrightarrow> validate_clause_set I S \<longrightarrow> validate_clause_set I C)"

definition cl_fclause :: "'a fclause \<Rightarrow> 'a clause" where
  "cl_fclause \<equiv> fset"

abbreviation ecl_fclause :: "'a fclause \<Rightarrow> 'a eclause"  where
  "ecl_fclause C \<equiv> ecl (cl_fclause C)"

lemma cl_fclause_empty[simp]: "cl_fclause {||} = {}"
  by (simp add: cl_fclause_def)

definition entails :: "'a fclause set \<Rightarrow> 'a fclause set \<Rightarrow> bool" where
  "entails X Y \<equiv> set_entails_set (image cl_fclause X) (image cl_fclause Y)"

interpretation conseq_rel_super: consequence_relation Bot entails
proof (unfold_locales)
  show "Bot \<noteq> {}"
    using Bot_def
    by force
next
  fix B N1
  assume "B \<in> Bot"
  hence B_def: "B = {||}"
    unfolding Bot_def by blast
  show "entails {B} N1"
    unfolding entails_def set_entails_set_def
    unfolding B_def image_insert cl_fclause_empty image_empty
    by simp
next
  fix N2 N1
  show "N2 \<subseteq> N1 \<Longrightarrow> entails N1 N2"
    unfolding entails_def set_entails_set_def
    by force
next
  fix N2 N1
  show "\<forall>C \<in> N2. entails N1 {C} \<Longrightarrow> entails N1 N2"
    unfolding entails_def set_entails_set_def
    by force
next
  fix N1 N2 N3
  show "entails N1 N2 \<Longrightarrow> entails N2 N3 \<Longrightarrow> entails N1 N3"
    unfolding entails_def set_entails_set_def
    by blast
qed

definition restriction where
  "restriction I S x y \<equiv> x \<in> S \<and> y \<in> S \<and> I x y"

definition Inf :: "'a fclause inference set" where
  "Inf \<equiv> {Infer P C | P S C \<sigma> k C'. derivable (ecl_fclause C) (image ecl_fclause (set P)) S \<sigma> k C'}"

interpretation inf_sys_super: inference_system Inf
  done

instantiation fclause :: (preorder) preorder begin

print_locale calculus_with_finitary_standard_redundancy
(* interpretation calc_standard_red: calculus_with_finitary_standard_redundancy Inf Bot entails *)


term redundant_inference
term prems_of
term concl_of
term "redundant_inference (concl_of \<iota>) (image ecl N) (set (prems_of \<iota>)) \<sigma>"

definition Red_I :: "'a fclause set \<Rightarrow> 'a fclause inference set" where
  "Red_I N \<equiv> {\<iota> \<in> Inf.
    (let prems = image ecl_fclause (set (prems_of \<iota>)) in
     let concl = ecl_fclause (concl_of \<iota>) in
     \<exists>\<sigma>. redundant_inference concl (image ecl_fclause N) prems \<sigma>)}"

text \<open>
I first tried with the following definition.

definition Red_F where
  "Red_F N \<equiv>
    {cl_ecl C | C \<sigma> C'. redundant_clause C (image ecl N) \<sigma> C' \<and> (\<forall>n \<in> N. \<not> renaming_cl C (ecl n))}"

But I could not prove the lemma @{term "N \<subseteq> N' \<Longrightarrow> Red_F N \<subseteq> Red_F N'"}.
\<close>

term entails
term cl_ord

text \<open>So we let's now try the standard redundancy criterion for formulas.\<close>

definition Red_F :: "'a fclause set \<Rightarrow> 'a fclause set" where
  "Red_F N \<equiv> {}"

lemma lt_set_entails_clause_imp_validate_clause:
  assumes
    fo_I: "fo_interpretation I" and
    validate_I_N: "validate_clause_set I N" and
    entails_lt_C: "set_entails_set {D \<in> N. \<exists>\<sigma>\<^sub>1 \<sigma>\<^sub>2. ((C, \<sigma>\<^sub>1), D, \<sigma>\<^sub>2) \<in> cl_ord} {C}"
  shows "validate_clause I C"
  using assms
  by (simp add: Red_F_def set_entails_set_def)

(* lemma validate_clause_set_imp_validate_Red_F:
  assumes inter_I: "fo_interpretation I" and validate_N: "validate_clause_set I (image fset N)"
  shows "validate_clause_set I (image fset (Red_F N))"
  unfolding validate_clause_set.simps
proof (intro allI impI)
  fix C
  assume "C \<in> Red_F N"
  hence "set_entails_set {D \<in> N. \<exists>\<sigma>\<^sub>1 \<sigma>\<^sub>2. ((C, \<sigma>\<^sub>1), D, \<sigma>\<^sub>2) \<in> cl_ord} {C}"
    unfolding Red_F_def entails_def by simp
  moreover have "validate_clause_set I {D \<in> N. \<exists>\<sigma>\<^sub>1 \<sigma>\<^sub>2. ((C, \<sigma>\<^sub>1), D, \<sigma>\<^sub>2) \<in> cl_ord}"
    using validate_N
    by (simp add: validate_clause_subset_eq)
  ultimately show "validate_clause I C"
    using inter_I
    unfolding set_entails_set_def
    by simp
qed *)


sublocale calc_super: calculus Bot Inf entails Red_I Red_F
proof (unfold_locales)
  fix N
  show "Red_I N \<subseteq> Inf"
    unfolding Red_I_def by simp
next
  fix B N
  assume "B \<in> Bot" and "entails N {B}"
  then show "entails (N - Red_F N) {B}"
    sorry
next
  fix N N' :: "'a fclause set"
  assume "N \<subseteq> N'"
  show "Red_F N \<subseteq> Red_F N'"
    sorry
next
  fix N N' :: "'a fclause set"
  assume "N \<subseteq> N'"
  show "Red_I N \<subseteq> Red_I N'"
  proof (rule subsetI)
    fix \<iota> :: "'a fclause inference"
    define prems where "prems = image ecl_fclause (set (prems_of \<iota>))"
    define concl where "concl = ecl_fclause (concl_of \<iota>)"
    assume "\<iota> \<in> Red_I N"
    then obtain \<sigma> where
      "\<iota> \<in> Inf" and
      red_N: "redundant_inference concl (image ecl_fclause N) prems \<sigma>"
      unfolding Red_I_def by (auto simp: prems_def concl_def)
    have "redundant_inference concl (image ecl_fclause N') prems \<sigma>"
      using \<open>N \<subseteq> N'\<close> red_N redundant_inference_subset_eqI[of "image ecl_fclause N" "image ecl_fclause N'"]
      by blast
    thus "\<iota> \<in> Red_I N'"
      using \<open>\<iota> \<in> Inf\<close>
      by (auto simp: Red_I_def prems_def concl_def)
  qed
next
  fix N' N
  show "N' \<subseteq> Red_F N \<Longrightarrow> Red_F N \<subseteq> Red_F (N - N')"
    unfolding Red_F_def
    sorry
next
  fix N' N
  show "N' \<subseteq> Red_F N \<Longrightarrow> Red_I N \<subseteq> Red_I (N - N')"
    unfolding Red_I_def Red_F_def 
    sorry
next
  fix \<iota> :: "'a fclause inference" and N :: "'a fclause set"
  define prems where "prems = image ecl_fclause (set (prems_of \<iota>))"
  define concl where "concl = ecl_fclause (concl_of \<iota>)"
  assume "\<iota> \<in> Inf" and "concl_of \<iota> \<in> N"

  obtain \<sigma> where red_N': "redundant_inference concl (image ecl_fclause N) prems \<sigma>"
    (* using redundant_inference_member[of "concl_of \<iota>" "image ecl_fclause N"]
    using \<open>concl_of \<iota> \<in> N\<close>
    by (auto simp: concl_def) *)
    sorry

  thus "\<iota> \<in> Red_I N"
    using \<open>\<iota> \<in> Inf\<close>
    by (auto simp add: Red_I_def prems_def concl_def)
qed

(* lemma entails_Bot_to_not_sat:
  assumes "B \<in> Bot" "entails N {B}"
  shows "\<not> (satisfiable_clause_set N)"
  unfolding satisfiable_clause_set_def
proof (rule notI, elim exE conjE)
  fix I
  assume "fo_interpretation I" and "validate_clause_set I N"
  hence "validate_clause_set I {B}"
    using \<open>entails N {B}\<close>
    unfolding entails_def set_entails_set_def by fast
  moreover have "{B} = {{}}"
    using \<open>B \<in> Bot\<close>[unfolded Bot_def] by force
  ultimately show False
    by simp
qed *)

lemma Ball_subset_BallD:
  assumes "{s \<in> S. P s} \<subseteq> {t \<in> T. Q t}" and "S \<subseteq> T" and "s \<in> S"
  shows "P s \<Longrightarrow> Q s"
  using assms by blast

lemmas Ball_subset_BallD' = Ball_subset_BallD[of S _ S for S, simplified]

lemma finite_set_SOME_set[simp]: "finite M \<Longrightarrow> set (SOME xs. set xs = M) = M"
  by (meson finite_list someI)
thm finite_list

sublocale stat_complete_calc_super: statically_complete_calculus Bot Inf entails Red_I Red_F
proof (unfold_locales)
  fix B N
  assume satur_N: "calc_super.saturated N" and unsat_N: "B \<in> Bot" "entails N {B}"
(* 
  from satur_N have satur_N': "\<And>\<iota>. \<iota> \<in> local.Inf \<Longrightarrow> set (prems_of \<iota>) \<subseteq> N \<Longrightarrow> concl_of \<iota> \<in> N"
    unfolding calc_super.saturated_def  inf_sys_super.Inf_from_def Red_I_def
    by (auto dest: Ball_subset_BallD')
  obtain S \<sigma> k C' where
    satur_N'': "derivable ecl ((\<lambda>s. Ecl s {}) ` set (SOME xs. set xs = M)) S \<sigma> k C' \<Longrightarrow>
      finite M \<Longrightarrow> M \<subseteq> N \<Longrightarrow> cl_ecl ecl \<in> N"
    for ecl M
    using satur_N' derivable_def by blast

  have unsat_N': "\<not> satisfiable_clause_set N"
    by (rule entails_Bot_to_not_sat[OF unsat_N])

  have "\<exists>ecl. derivable_ecl ecl ((\<lambda>cl. Ecl cl {}) ` N) \<and> cl_ecl ecl = {}"
  proof (rule COMPLETENESS)
    show "\<forall>ecl\<in>(\<lambda>cl. Ecl cl {}) ` N. trms_ecl ecl = {}"
      by simp
  next
    show "\<forall>ecl\<in>(\<lambda>cl. Ecl cl {}) ` N. finite (cl_ecl ecl)"
      sorry
  next
    show "\<not> satisfiable_clause_set (cl_ecl ` (\<lambda>cl. Ecl cl {}) ` N)"
      using unsat_N'
      by (simp add: image_image)
  qed
  then obtain ecl where "derivable_ecl ecl ((\<lambda>cl. Ecl cl {}) ` N)" "cl_ecl ecl = {}"
    (* by blast *)
    sorry

  then show "\<exists>B'\<in>Bot. B' \<in> N"
    using satur_N''
  proof (induction ecl "((\<lambda>cl. Ecl cl {}) ` N)" arbitrary: N rule: derivable_ecl.induct)
    case (init C)
    then show ?case
      by (auto simp add: Bot_def)
  next
    case (rn C D)
    have "cl_ecl C \<in> N"
    have ?case if "finite N"
      using that rn.prems(2)[OF rn.hyps(1)]
      sorry
  next
    case (deriv P C \<sigma> C')
    then show ?case
      unfolding Inf_def
      sorry
  qed *)
  oops
    
end

end