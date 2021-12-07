theory Prover
  imports
    Ordered_Resolution_Prover.Abstract_Substitution
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

lemma asympD: "asymp R \<Longrightarrow> R x y \<Longrightarrow> \<not> R y x"
  by (rule asymD[to_pred])

lemma inj_imp_inj_on[simp]: "inj f \<Longrightarrow> inj_on f S"
  by (simp add: inj_def inj_onI)


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
    sorry
qed

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

lemma "to_SuperCalc_cl (subst_cls C \<sigma>) = subst_cl (to_SuperCalc_cl C) \<sigma>"
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
    by (auto simp add: setcompr_eq_image)
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
    by (simp add: SuperCalc.set_entails_set_def to_SuperCalc_cl_def)
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
  assume "\<iota> \<in> F_Inf" and "concl_of \<iota> \<in> N"

  from \<open>\<iota> \<in> F_Inf\<close> obtain P S C \<sigma> k C' where
    \<iota>_def: "\<iota> = Infer P (from_SuperCalc_cl (subst_cl C' \<sigma>))" and
    deriv: "derivable_list C (map to_SuperCalc_ecl (map2 subst_cls P (renamings_apart P))) S \<sigma> k C'"
    unfolding F_Inf_def by blast

  from \<open>concl_of \<iota> \<in> N\<close> have "from_SuperCalc_cl (subst_cl C' \<sigma>) \<in> N"
    unfolding \<iota>_def by simp

  have "finite C'"
    by (rule SuperCalc.derivable_finite_conclusion[OF _ derivable_list_imp_derivable[OF deriv],
          simplified])
  hence to_from_subst_C': "to_SuperCalc_cl (from_SuperCalc_cl (subst_cl C' \<sigma>)) = subst_cl C' \<sigma>"
    using to_from_SuperCalc_cl
    by simp

  have "SuperCalc.redundant_inference
    (to_SuperCalc_ecl (from_SuperCalc_cl (subst_cl C' \<sigma>)))
    (to_SuperCalc_ecl ` N)
    (set (map to_SuperCalc_ecl P)) \<sigma>"
    unfolding to_from_subst_C'
    unfolding SuperCalc.redundant_inference_def
    using derivable_list_imp_derivable[OF deriv]
    using SuperCalc.redundant_inference_clause
    sorry

  then show "\<iota> \<in> Red_I N"
    using \<open>\<iota> \<in> F_Inf\<close>
    unfolding \<iota>_def Red_I_def Let_def inference.sel
    by auto
qed

sublocale statically_complete_calculus "{{#}}" F_Inf entails Red_I Red_F
proof unfold_locales
  fix B N
  assume "B \<in> {{#}}" and "saturated N" and "N \<TTurnstile>e {B}"
  hence B_def: "B = {#}" by simp
  show "\<exists>B'\<in>{{#}}. B' \<in> N"
    using \<open>saturated N\<close>
    using \<open>N \<TTurnstile>e {B}\<close>[unfolded B_def entails_def, simplified]
    using SuperCalc.int_clset_is_a_model
    sorry
qed

end


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