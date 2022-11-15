theory Prover
  imports
    (* Ordered_Resolution_Prover.Abstract_Substitution *)
    SuperCalc.superposition
    Saturation_Framework.Calculus
    Saturation_Framework.Lifting_to_Non_Ground_Calculi
    Saturation_Framework_Extensions.Standard_Redundancy_Criterion
    Saturation_Framework_Extensions.Soundness
    "HOL-Library.Multiset_Order"
    "HOL-Library.FSet"
begin

term fset

(* sledgehammer_params [verbose, slices = 24] *)


subsection \<open>Generic lemmas about HOL definitions\<close>

lemma Abs_fset_empty[simp]: "Abs_fset {} = {||}"
  by (simp add: bot_fset.abs_eq)

lemma list_all2_zip_map_right:
  assumes "length xs = length ys"
  shows "list_all2 P xs (zip (map f xs) ys) = list_all2 (\<lambda>x y. P x (f x, y)) xs ys"
  using assms by (induction xs ys rule: list_induct2) simp_all

lemma set_eq_unionI:
  assumes "\<And>x. x \<in> A \<longleftrightarrow> x \<in> B \<or> x \<in> C"
  shows "A = (B \<union> C)"
  using assms by blast

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

primrec canonical_map0 where
  "canonical_map0 xs [] = xs" |
  "canonical_map0 xs (y # ys) =
    canonical_map0 ((case map_of xs (fst y) of None \<Rightarrow> [y] | Some _ \<Rightarrow> []) @ xs) ys"

abbreviation canonical_map where
  "canonical_map \<equiv> canonical_map0 []"

lemma map_of_canonical_map0_correct: "map_of (canonical_map0 xs ys) = map_of (xs @ ys)"
proof (rule ext, induction ys arbitrary: xs)
  case Nil
  show ?case by simp
next
  case (Cons y ys z)
  show ?case
  proof (cases "map_of xs (fst y)")
    case None
    then show ?thesis
      by (simp add: domIff Cons map_add_upd_left)
  next
    case (Some a)
    then show ?thesis
      apply simp
      by (metis (no_types, lifting) domIff fun_upd_apply local.Cons map_add_def
          map_add_dom_app_simps(1) map_of_append option.simps(3))
  qed
qed

lemma map_of_canonical_map_correct: "map_of (canonical_map xs) = map_of xs"
  by (rule map_of_canonical_map0_correct[of "[]", simplified])

lemma distinct_map_fst_canonical_map0:
  "distinct (map fst xs) \<Longrightarrow> distinct (map fst (canonical_map0 xs ys))"
proof (induction ys arbitrary: xs)
  case Nil
  thus ?case by simp
next
  case (Cons y ys)
  show ?case
    by (cases "map_of xs (fst y)") (auto intro!: Cons.prems Cons.IH map_of_eq_None_iff[THEN iffD1])
qed

lemma distinct_map_fst_canonical_map: "distinct (map fst (canonical_map xs))"
  by (rule distinct_map_fst_canonical_map0[of "[]", simplified])

lemma map_of_filter_comp_fst:
  "map_of (filter (P \<circ> fst) xs) = (\<lambda>x. if P x then map_of xs x else None)"
  by (induction xs) auto


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
    using Bex_x_less fin_T
    by simp
qed

lemma Multiset_equalityI: "A \<subseteq># B \<Longrightarrow> B \<subseteq># A \<Longrightarrow> A = B"
  by (rule subset_mset.antisym)

lemma monotone_list_all2_list_all2_map:
  assumes "monotone R S f"
  shows "monotone (list_all2 R) (list_all2 S) (map f)"
proof (rule monotoneI)
  fix xs ys assume "list_all2 R xs ys"
  thus "list_all2 S (map f xs) (map f ys)"
    unfolding list.rel_map
  proof (rule list.rel_mono_strong)
    fix x y assume "x \<in> set xs" and "y \<in> set ys" and "R x y"
    from \<open>R x y\<close> show "S (f x) (f y)"
      by (rule \<open>monotone R S f\<close>[THEN monotoneD])
  qed
qed

lemma monotone_rel_mset_rel_mset_image_mset:
  assumes "monotone R S f"
  shows "monotone (rel_mset R) (rel_mset S) (image_mset f)"
proof (rule monotoneI)
  fix A B assume "rel_mset R A B"
  thus "rel_mset S (image_mset f A) (image_mset f B)"
    unfolding multiset.rel_map
  proof (rule multiset.rel_mono_strong)
    fix a b assume "a \<in># A" and "b \<in># B" and "R a b"
    from \<open>R a b\<close> show "S (f a) (f b)"
      by (rule \<open>monotone R S f\<close>[THEN monotoneD])
  qed
qed

lemma multp_image_msetD1:
  assumes "multp R (image_mset f A) B" and "transp R" and "Relation.reflp_on (set_mset B) R"
  shows "multp (\<lambda>x. R (f x)) A B"
proof -
  obtain I J K where
    B_def: "B = I + J" and "image_mset f A = I + K" and "J \<noteq> {#}" and "\<forall>k\<in>#K. \<exists>x\<in>#J. R k x"
    using multp_implies_one_step[OF \<open>transp R\<close> \<open>multp R (image_mset f A) B\<close>] by metis
  then obtain I' K' where
    A_def: "A = I' + K'" and I_def: "I = image_mset f I'" and K_def: "K = image_mset f K'"
    using image_mset_eq_plusD by metis

  show "multp (\<lambda>x. R (f x)) A B"
  proof (rule one_step_implies_multp[of _ _ _ "{#}", simplified])
    show "B \<noteq> {#}"
      using \<open>J \<noteq> {#}\<close> by (simp add: B_def)
  next
    show "\<forall>k\<in>#A. \<exists>j\<in>#B. R (f k) j"
    proof (rule ballI)
      fix a assume "a \<in># A"
      hence "a \<in># I' \<or> a \<in># K'"
        by (simp add: A_def)
      thus "\<exists>j\<in>#B. R (f a) j"
      proof (rule disjE)
        assume "a \<in># I'"
        have "f a \<in># B"
          using \<open>a \<in># I'\<close> by (simp add: B_def I_def)
        show ?thesis
        proof (rule bexI)
          show "R (f a) (f a)"
            using \<open>f a \<in># B\<close>
            by (rule \<open>Relation.reflp_on (set_mset B) R\<close>[THEN reflp_onD])
        next
          show "f a \<in># B"
            by (rule \<open>f a \<in># B\<close>)
        qed
      next
        assume "a \<in># K'"
        thus ?thesis
          using B_def K_def \<open>\<forall>k\<in>#K. \<exists>x\<in>#J. R k x\<close> by auto
      qed
    qed
  qed
qed

lemma multp_image_msetD2:
  assumes "multp R A (image_mset f B)" and "transp R" and "Relation.reflp_on (set_mset A) R"
  shows "multp (\<lambda>x y. R x (f y)) A B"
proof -
  obtain I J K where
    A_def: "A = I + K" and "image_mset f B = I + J" and "J \<noteq> {#}" and "\<forall>k\<in>#K. \<exists>x\<in>#J. R k x"
    using multp_implies_one_step[OF \<open>transp R\<close> \<open>multp R A (image_mset f B)\<close>] by metis
  then obtain I' J' where
    B_def: "B = I' + J'" and I_def: "I = image_mset f I'" and J_def: "J = image_mset f J'"
    using image_mset_eq_plusD by metis

  show "multp (\<lambda>x y. R x (f y)) A B"
  proof (rule one_step_implies_multp[of _ _ _ "{#}", simplified])
    show "B \<noteq> {#}"
      using \<open>J \<noteq> {#}\<close> by (simp add: B_def J_def)
  next
    show "\<forall>k\<in>#A. \<exists>j\<in>#B. R k (f j)"
    proof (rule ballI)
      fix a assume "a \<in># A"
      hence "a \<in># I \<or> a \<in># K"
        by (simp add: A_def)
      thus "\<exists>j\<in>#B. R a (f j)"
      proof (rule disjE)
        assume "a \<in># I"
        then obtain a' where "a' \<in># I'" and "a = f a'"
          unfolding I_def by force
        hence "a' \<in># B"
          by (simp add: B_def)
        show ?thesis
        proof (rule bexI)
          show "a' \<in># B"
            using \<open>a' \<in># I'\<close> by (simp add: B_def)
        next
          from assms(3) show "R a (f a')"
            using \<open>a = f a'\<close> \<open>a \<in># A\<close> reflp_onD by fastforce
        qed
      next
        assume "a \<in># K"
        thus ?thesis
          by (metis \<open>\<forall>k\<in>#K. \<exists>x\<in>#J. R k x\<close> \<open>image_mset f B = I + J\<close> image_mset_thm union_iff)
      qed
    qed
  qed
qed

lemma multp_image_mset_image_msetD_strong:
  assumes
    transp_R: "transp R" and
    converse_mono_wrt_f_R:
      "\<forall>t \<in> set_mset M1. \<forall>u \<in> set_mset M2. R (f t) (f u) \<longrightarrow> S t u" and
    inj_on_f: "inj_on f (set_mset M1 \<union> set_mset M2)" and
    multp_f_M1_f_M2: "multp R (image_mset f M1) (image_mset f M2)"
  shows "multp S M1 M2"
proof -
  from multp_implies_one_step[OF transp_R multp_f_M1_f_M2] obtain I J K where
    f_M2_eq: "image_mset f M2 = I + J" and
    f_M1_eq: "image_mset f M1 = I + K" and
    J_neq_mempty: "J \<noteq> {#}" and
    ball_K_less: "\<forall>k\<in>#K. \<exists>x\<in>#J. R k x"
    by auto

  from f_M2_eq obtain I' J' where
    M2_def: "M2 = I' + J'" and I_def: "I = image_mset f I'" and J_def: "J = image_mset f J'"
    using image_mset_eq_plusD by blast

  from inj_on_f have inj_on_f': "inj_on f (set_mset M1 \<union> set_mset I')"
    by (rule inj_on_subset) (auto simp add: M2_def)

  from f_M1_eq obtain K' where
    M1_def: "M1 = I' + K'" and K_def: "K = image_mset f K'"
    by (auto simp: I_def dest: image_mset_eq_image_mset_plusD[OF _ inj_on_f'])

  show ?thesis
    unfolding M1_def M2_def
  proof (intro one_step_implies_multp ballI)
    from J_neq_mempty show "J' \<noteq> {#}"
      by (simp add: J_def)
  next
    fix k assume "k \<in># K'"
    with ball_K_less obtain j' where "j' \<in># J" and "R (f k) j'"
      using K_def by auto
    then obtain j where "j \<in># J'" and "f j = j'"
      using J_def by auto
    show "\<exists>j\<in>#J'. S k j"
    proof (rule bexI)
      show "j \<in># J'"
        by (rule \<open>j \<in># J'\<close>)
    next
      show "S k j"
        using converse_mono_wrt_f_R[rule_format, of k j]
        by (simp add: M1_def M2_def \<open>R (f k) j'\<close> \<open>f j = j'\<close> \<open>j \<in># J'\<close> \<open>k \<in># K'\<close>)
    qed
  qed
qed

lemma multp_iff_mult: "multp (\<lambda>x y. (x, y) \<in> r) x y \<longleftrightarrow> (x, y) \<in> mult r"
  by (simp add: multp_def)

lemma mult_iff_multp: "(x, y) \<in> mult {(x, y). R x y} \<longleftrightarrow> multp R x y"
  by (simp add: multp_def)

lemma image_mset_image_mset_mem_multD:
  assumes
    "trans r" and
    "\<forall>t \<in> set_mset M1. \<forall>u \<in> set_mset M2. (f t, f u) \<in> r \<longrightarrow> (t, u) \<in> s" and
    "inj_on f (set_mset M1 \<union> set_mset M2)" and
    "(image_mset f M1, image_mset f M2) \<in> mult r"
  shows "(M1, M2) \<in> mult s"
proof (rule multp_image_mset_image_msetD_strong[of _ _ _ _ "\<lambda>x y. (x, y) \<in> s",
        unfolded multp_iff_mult])
  from assms(1) show "transp (\<lambda>x y. (x, y) \<in> r)"
    by (simp add: transp_trans_eq)
next
  from assms(2) show "\<forall>t\<in>#M1. \<forall>u\<in>#M2. (f t, f u) \<in> r \<longrightarrow> (t, u) \<in> s"
    by simp
next
  from assms(3) show "inj_on f (set_mset M1 \<union> set_mset M2)"
    by assumption
next
  from assms(4) show "multp (\<lambda>x y. (x, y) \<in> r) (image_mset f M1) (image_mset f M2)"
    by (simp add: multp_iff_mult)
qed


subsection \<open>Generic lemmas about HOL-ex\<close>

lemma assoc_ident_if_not_in_dom: "x \<notin> fst ` set \<sigma> \<Longrightarrow> assoc x t \<sigma> = t"
  by (induction \<sigma>) auto

lemma subst_ident_if_vars_distinct_dom: "vars_of t \<inter> fst ` set \<sigma> = {} \<Longrightarrow> subst t \<sigma> = t"
  by (induction t) (auto simp add: assoc_ident_if_not_in_dom)

lemma subst_ident_if_vars_empty: "vars_of t = {} \<Longrightarrow> subst t \<sigma> = t"
  by (rule subst_ident_if_vars_distinct_dom) simp


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

lemma subst_append_remove_left: "vars_of t \<inter> fst `set \<sigma>\<^sub>1 = {} \<Longrightarrow> t \<lhd> \<sigma>\<^sub>1 @ \<sigma>\<^sub>2 = t \<lhd> \<sigma>\<^sub>2"
  apply (induction \<sigma>\<^sub>1)
   apply simp
  by (smt (verit, best) agreement append_Cons assoc.elims fst_conv image_insert inf_commute
      insert_disjoint(1) list.discI list.inject list.simps(15) subst.simps(1))

lemma subst_append_remove_right: "vars_of t \<inter> fst `set \<sigma>\<^sub>2 = {} \<Longrightarrow> t \<lhd> \<sigma>\<^sub>1 @ \<sigma>\<^sub>2 = t \<lhd> \<sigma>\<^sub>1"
  apply (induction \<sigma>\<^sub>1)
  using subst_append_remove_left[of t \<sigma>\<^sub>2 "[]", simplified]
   apply simp
  using agreement list.discI by fastforce

lemma assoc_eq_map_of_or_default: "assoc x y xs = (case map_of xs x of None \<Rightarrow> y | Some z \<Rightarrow> z)"
  by (induction xs) auto

lemma subst_Var_ident_if_not_in_dom: "x \<notin> fst ` set \<sigma> \<Longrightarrow> Var x \<lhd> \<sigma> = Var x"
  by (metis assoc.simps(1) assoc_eq_map_of_or_default empty_iff image_empty list.set(1)
      map_of_eq_None_iff subst.simps(1))

lemma subst_if_in_dom: "x \<in> fst ` set \<sigma> \<Longrightarrow> \<exists>p \<in> set \<sigma>. Var x \<lhd> \<sigma> = snd p"
  apply (induction \<sigma>)
   apply simp
  apply simp
  by force

lemma subst_append_swap: "fst `set \<sigma>\<^sub>1 \<inter> fst `set \<sigma>\<^sub>2 = {} \<Longrightarrow> t \<lhd> \<sigma>\<^sub>1 @ \<sigma>\<^sub>2 = t \<lhd> \<sigma>\<^sub>2 @ \<sigma>\<^sub>1"
proof (induction t)
  case (Var x)
  then show ?case
    apply (cases "vars_of (Var x) \<inter> fst ` set \<sigma>\<^sub>1 = {}")
    unfolding subst_append_remove_left subst_append_remove_right
     apply (simp add: subst_append_remove_left subst_append_remove_right)
    by (metis (no_types, opaque_lifting) inf_bot_left insert_absorb insert_disjoint(1)
        subst_append_remove_left subst_append_remove_right vars_of.simps(1))
next
  case (Const x)
  show ?case by simp
next
  case (Comb t1 t2)
  thus ?case
    by simp
qed

lemma renaming_subst_compI:
  assumes "renaming \<rho>\<^sub>1 V" and "renaming \<rho>\<^sub>2 (subst_codomain \<rho>\<^sub>1 V)"
  shows "renaming (\<rho>\<^sub>1 \<lozenge> \<rho>\<^sub>2) V"
  using assms
  unfolding renaming_def Unification.subst_comp
  by (smt (verit, ccfv_SIG) is_a_variable.elims(2) mem_Collect_eq subst_codomain_def)

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

lemma subst_Var_eq_map_of_or_default: "Var x \<lhd> \<sigma> = (case map_of \<sigma> x of None \<Rightarrow> Var x | Some z \<Rightarrow> z)"
  by (induction \<sigma>) auto

lemma canonical_map_subst_eq: "canonical_map \<sigma> \<doteq> \<sigma>"
  unfolding subst_eq_def
proof (rule allI)
  fix t
  show "t \<lhd> canonical_map \<sigma> = t \<lhd> \<sigma>"
    by (induction t) (simp_all add: assoc_eq_map_of_or_default map_of_canonical_map_correct)
qed

lemma subst_filter_comp_fst:
  assumes "\<forall>x \<in> vars_of t. P x"
  shows "t \<lhd> filter (P \<circ> fst) \<sigma> = t \<lhd> \<sigma>"
  using assms
  by (induction t) (simp_all add: assoc_eq_map_of_or_default map_of_filter_comp_fst)

lemma subst_MGU_is_var_if_not_in:
  assumes MGU_\<mu>: "MGU \<mu> t u" and
    z_not_in: "x \<notin> vars_of t \<union> vars_of u"
  shows "is_a_variable (Var x \<lhd> \<mu>)"
proof (rule ccontr)
  assume "\<not> is_a_variable (Var x \<lhd> \<mu>)"

  from MGU_\<mu> have "t \<lhd> \<mu> = u \<lhd> \<mu>" and "\<And>\<theta>. t \<lhd> \<theta> = u \<lhd> \<theta> \<Longrightarrow> \<exists>\<gamma>. \<theta> \<doteq> \<mu> \<lozenge> \<gamma>"
    by (simp_all add: MGU_def Unifier_def)

  define \<theta> where
    "\<theta> = filter (\<lambda>e. fst e \<in> vars_of t \<union> vars_of u) \<mu>"
  
  from \<open>t \<lhd> \<mu> = u \<lhd> \<mu>\<close> have "t \<lhd> \<theta> = u \<lhd> \<theta>"
    using subst_filter_comp_fst[unfolded comp_def, of _ "\<lambda>x. x \<in> vars_of t \<union> vars_of u"]
    by (simp add: \<theta>_def)
  with \<open>\<And>\<theta>. t \<lhd> \<theta> = u \<lhd> \<theta> \<Longrightarrow> \<exists>\<gamma>. \<theta> \<doteq> \<mu> \<lozenge> \<gamma>\<close> obtain \<gamma> where "\<theta> \<doteq> \<mu> \<lozenge> \<gamma>" by auto
  hence "\<forall>t. t \<lhd> \<theta> = t \<lhd> \<mu> \<lhd> \<gamma>" by (simp add: subst_eq_def)
  hence "Var x \<lhd> \<theta> = Var x \<lhd> \<mu> \<lhd> \<gamma>" by simp
  with z_not_in have "Var x = Var x \<lhd> \<mu> \<lhd> \<gamma>"
    using map_of_filter_comp_fst[unfolded comp_def, of "\<lambda>x. x \<in> vars_of t \<union> vars_of u" \<mu>]
    by (simp add: \<theta>_def assoc_eq_map_of_or_default)
  with \<open>\<not> is_a_variable (Var x \<lhd> \<mu>)\<close> show False
    by (metis subst_trm_ident is_a_variable.simps(1) occs.simps(1) subst_mono vars_iff_occseq)
qed

lemma subst_MGU_inj_on_comp_vars:
  assumes MGU_\<mu>: "MGU \<mu> t u"
  shows "inj_on (\<lambda>x. Var x \<lhd> \<mu>) (- (vars_of t \<union> vars_of u))"
proof (rule inj_onI)
  fix x y
  assume
    x_in: "x \<in> - (vars_of t \<union> vars_of u)" and
    y_in: "y \<in> - (vars_of t \<union> vars_of u)" and
    x_\<mu>_eq_y_\<mu>: "Var x \<lhd> \<mu> = Var y \<lhd> \<mu>"

  from MGU_\<mu> have "t \<lhd> \<mu> = u \<lhd> \<mu>" and "\<And>\<theta>. t \<lhd> \<theta> = u \<lhd> \<theta> \<Longrightarrow> \<exists>\<gamma>. \<theta> \<doteq> \<mu> \<lozenge> \<gamma>"
    by (simp_all add: MGU_def Unifier_def)

  define \<theta> where
    "\<theta> = filter (\<lambda>e. fst e \<in> vars_of t \<union> vars_of u) \<mu>"

  from \<open>t \<lhd> \<mu> = u \<lhd> \<mu>\<close> have "t \<lhd> \<theta> = u \<lhd> \<theta>"
    using subst_filter_comp_fst[unfolded comp_def, of _ "\<lambda>x. x \<in> vars_of t \<union> vars_of u" \<mu>]
    by (simp add: \<theta>_def)
  with \<open>\<And>\<theta>. t \<lhd> \<theta> = u \<lhd> \<theta> \<Longrightarrow> \<exists>\<gamma>. \<theta> \<doteq> \<mu> \<lozenge> \<gamma>\<close> obtain \<gamma> where "\<theta> \<doteq> \<mu> \<lozenge> \<gamma>" by auto
  hence "\<forall>t. t \<lhd> \<theta> = t \<lhd> \<mu> \<lhd> \<gamma>" by (simp add: subst_eq_def)
  hence "Var x \<lhd> \<theta> = Var x \<lhd> \<mu> \<lhd> \<gamma>" and "Var y \<lhd> \<theta> = Var y \<lhd> \<mu> \<lhd> \<gamma>" by simp_all
  with x_in y_in have "Var x = Var x \<lhd> \<mu> \<lhd> \<gamma>" and "Var y = Var y \<lhd> \<mu> \<lhd> \<gamma>"
    using map_of_filter_comp_fst[unfolded comp_def, of "\<lambda>x. x \<in> vars_of t \<union> vars_of u" \<mu>]
    by (simp_all add: \<theta>_def assoc_eq_map_of_or_default)
  thus "x = y"
    using x_\<mu>_eq_y_\<mu> by force
qed

lemma Unifier_subst_inv_ident: "Unifier \<upsilon> t u \<Longrightarrow> Unifier (\<rho>_inv \<lozenge> \<upsilon>) (t \<lhd> \<rho>) (u \<lhd> \<rho>)"
  if "t \<lhd> \<rho> \<lhd> \<rho>_inv = t" and "u \<lhd> \<rho> \<lhd> \<rho>_inv = u"
  for \<upsilon> t u \<rho>_inv \<rho>
  by (simp add: Unifier_def that)

lemma subst_cl_conv: "subst_cl C \<sigma> = (\<lambda>L. equational_clausal_logic.subst_lit L \<sigma>) ` C"
  unfolding subst_cl.simps
  by auto

lemma subst_identI:
  assumes
    ball_subst_ident: "\<forall>x \<in> V. Var x \<lhd> \<sigma> \<lhd> \<sigma>_inv = Var x" and
    vars_subset: "vars_of t \<subseteq> V"
  shows "t \<lhd> \<sigma> \<lhd> \<sigma>_inv = t"
  using assms by (induction t) simp_all

lemma subst_equation_identI:
  assumes
    ball_subst_ident: "\<forall>x \<in> V. Var x \<lhd> \<sigma> \<lhd> \<sigma>_inv = Var x" and
    vars_subset: "vars_of_eq e \<subseteq> V"
  shows "subst_equation (subst_equation e \<sigma>) \<sigma>_inv = e"
  using subst_identI[OF ball_subst_ident] vars_subset
  by (cases e) simp_all

lemma subst_lit_identI:
  assumes
    ball_subst_ident: "\<forall>x \<in> V. Var x \<lhd> \<sigma> \<lhd> \<sigma>_inv = Var x" and
    vars_subset: "vars_of_lit L \<subseteq> V"
  shows "equational_clausal_logic.subst_lit (equational_clausal_logic.subst_lit L \<sigma>) \<sigma>_inv = L"
  using subst_equation_identI[OF ball_subst_ident] vars_subset
  by (cases L) simp_all

lemma subst_cl_identI:
  assumes
    ball_subst_ident: "\<forall>x \<in> V. Var x \<lhd> \<sigma> \<lhd> \<sigma>_inv = Var x" and
    vars_subset: "vars_of_cl C \<subseteq> V"
  shows "subst_cl (subst_cl C \<sigma>) \<sigma>_inv = C"
  unfolding subst_cl_conv image_comp comp_def
  using subst_lit_identI[OF ball_subst_ident] vars_subset
  by (smt (verit, best) dual_order.trans image_cong image_ident vars_of_cl_lem)

lemma subst_set_conv: "subst_set S \<sigma> = (\<lambda>t. t \<lhd> \<sigma>) ` S" for S \<sigma>
  apply (simp add: subst_set.simps)
  by blast

lemma subst_set_identI:
  assumes
    ball_subst_ident: "\<forall>x \<in> V. Var x \<lhd> \<sigma> \<lhd> \<sigma>_inv = Var x" and
    vars_subset: "(\<Union>t \<in> N. vars_of t) \<subseteq> V"
  shows "subst_set (subst_set N \<sigma>) \<sigma>_inv = N"
  unfolding subst_set_conv image_image
  using subst_identI[OF ball_subst_ident] vars_subset
  by (simp add: UN_subset_iff)

lemma cl_ecl_subst_ecl_distrib: "cl_ecl (subst_ecl C \<sigma>) = subst_cl (cl_ecl C) \<sigma>"
  by (cases C) simp

lemma singleton_subst_lit_conv: "{equational_clausal_logic.subst_lit L1 \<sigma>} = subst_cl {L1} \<sigma>"
  unfolding subst_cl.simps
  by simp

lemma minus_subst_cl_subst_cl:
  assumes "renaming \<rho> (vars_of_cl C \<union> vars_of_cl D)"
  shows "subst_cl C \<rho> - subst_cl D \<rho> = subst_cl (C - D) \<rho>"
    (is "?lhs = ?rhs")
proof (rule Set.equalityI; rule subsetI)
  fix L
  assume "L \<in> ?lhs"
  thus "L \<in> ?rhs" by auto
next
  fix L
  assume "L \<in> ?rhs"
  thus "L \<in> ?lhs"
    unfolding subst_cl_conv
    apply simp
    apply (rule conjI)
     apply force
    unfolding image_iff
    using assms[unfolded renaming_def, rule_format, THEN conjunct1]
    using assms[unfolded renaming_def, rule_format, THEN conjunct2, rule_format, of x x for x]
    oops

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

lemma subst_cl_empty[simp]: "subst_cl {} \<sigma> = {}"
  by simp

lemma ground_clause_empty[simp]: "ground_clause {}"
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

lemma vars_of_eq_subst_equation_conv:
  fixes e and \<sigma>
  shows "vars_of_eq (subst_equation e \<sigma>) = \<Union>((\<lambda>v. vars_of (assoc v (Var v) \<sigma>)) ` vars_of_eq e)"
  by (cases e) (auto simp: vars_of_subst_conv)

lemma vars_of_lit_subst_lit_conv:
  fixes L and \<sigma>
  shows "vars_of_lit (equational_clausal_logic.subst_lit L \<sigma>) =
    \<Union>((\<lambda>v. vars_of (assoc v (Var v) \<sigma>)) ` vars_of_lit L)"
  by (cases L) (auto simp: vars_of_eq_subst_equation_conv)

lemma ex_subst_var_in_vars_if_in_vars_subst_cl:
  assumes x_in: "x \<in> vars_of_cl (subst_cl C \<rho>)" and
     ball_subst_\<rho>_var: "\<forall>x \<in> vars_of_cl C. is_a_variable (subst (Var x) \<rho>)"
  shows "\<exists>x' \<in> vars_of_cl C. Var x = subst (Var x') \<rho>"
proof -
  from x_in obtain L where x_in: "x \<in> vars_of_lit L" and L_in: "L \<in> subst_cl C \<rho>"
    by auto

  from L_in obtain L' where L'_in: "L' \<in> C" and
    L_def: "L = equational_clausal_logic.subst_lit L' \<rho>"
    by (smt (verit, best) cl_ecl_subst_ecl_distrib mem_Collect_eq subst_cl.simps)

  from x_in L_def L'_in have "\<exists>x'. x' \<in> vars_of_lit L' \<and> Var x = Var x' \<lhd> \<rho>"
    using ball_subst_\<rho>_var
    by (smt (verit, best) UN_iff is_a_variable.elims(2) occs.simps(1) subsetD subst.simps(1)
        vars_iff_occseq vars_of_cl_lem vars_of_lit_subst_lit_conv)
  then show ?thesis
    using L'_in by auto
qed

lemma renaming_imp_ball_var: "\<And>\<sigma> S. renaming \<sigma> S \<Longrightarrow> \<forall>x\<in>S. is_a_variable (Var x \<lhd> \<sigma>)"
  unfolding renaming_def by simp

lemma renaming_imp_ball_neq_imp_neq_subst:
  "\<And>\<sigma> S. renaming \<sigma> S \<Longrightarrow> \<forall>x\<in>S. \<forall>y\<in>S. x \<noteq> y \<longrightarrow> Var x \<lhd> \<sigma> \<noteq> Var y \<lhd> \<sigma>"
  unfolding renaming_def by simp

lemma ex_renaming_swap:
  assumes fin_C: "finite C" and ren_\<rho>: "renaming \<rho> (vars_of_cl C)" and "D = subst_cl C \<rho>"
  shows "\<exists>\<rho>'. renaming \<rho>' (vars_of_cl D) \<and> C = subst_cl D \<rho>'"
proof -
  from fin_C have fin_vars_C: "finite (vars_of_cl C)"
    using set_of_variables_is_finite_cl by blast

  from ren_\<rho> have ball_is_vars_subst_\<rho>: "\<forall>x\<in>vars_of_cl C. is_a_variable (Var x \<lhd> \<rho>)"
    using renaming_imp_ball_var by blast

  obtain \<rho>_inv where
    \<rho>_\<rho>_inv_ident: "\<forall>x\<in>vars_of_cl C. Var x \<lhd> \<rho> \<lhd> \<rho>_inv = Var x" and
    \<rho>_inv_ident_if: "\<forall>x. x \<notin> subst_codomain \<rho> (vars_of_cl C) \<longrightarrow>
            Var x \<lhd> \<rho>_inv = Var x" and
    \<rho>_inv_vars: "\<forall>x. is_a_variable (subst (Var x) \<rho>_inv)"
    using renamings_admit_inverse[OF fin_vars_C ren_\<rho>] by auto

  show ?thesis
  proof (intro exI conjI)
    show "renaming \<rho>_inv (vars_of_cl D)"
      unfolding renaming_def
    proof (intro ballI conjI allI impI)
      show "\<And>x. x \<in> vars_of_cl D \<Longrightarrow> is_a_variable (Var x \<lhd> \<rho>_inv)"
        by (rule \<rho>_inv_vars[rule_format])
    next
      fix x y
      assume x_in: "x \<in> vars_of_cl D" and "y \<in> vars_of_cl D"
      then obtain x' y' where
        "x' \<in> vars_of_cl C" and "Var x = Var x' \<lhd> \<rho>" and
        "y' \<in> vars_of_cl C" and "Var y = Var y' \<lhd> \<rho>"
        unfolding \<open>D = subst_cl C \<rho>\<close>
        using ex_subst_var_in_vars_if_in_vars_subst_cl[OF _ ball_is_vars_subst_\<rho>]
        by blast
      then show "x \<noteq> y \<Longrightarrow> Var x \<lhd> \<rho>_inv \<noteq> Var y \<lhd> \<rho>_inv"
        using \<rho>_\<rho>_inv_ident[rule_format]
        by (metis trm.inject(1))
    qed
  next
    show "C = subst_cl D \<rho>_inv"
      unfolding \<open>D = subst_cl C \<rho>\<close>
      using \<rho>_\<rho>_inv_ident
      by (metis order_refl subst_cl_identI)
  qed
qed

lemma renaming_cl_commutative: "renaming_cl D C"
  if fin_C: "finite (cl_ecl C)" and trms_C: "trms_ecl C = {}" and ren_C_D: "renaming_cl C D"
  for C D
proof -
  from fin_C have fin_vars_C: "finite (vars_of_cl (cl_ecl C))"
    using set_of_variables_is_finite_cl by blast

  from ren_C_D obtain \<rho> where
    ren_\<rho>: "renaming \<rho> (vars_of_cl (cl_ecl C))" and D_def: "D = subst_ecl C \<rho>"
    unfolding renaming_cl_def by auto

  have cl_ecl_D_conv: "cl_ecl D = subst_cl (cl_ecl C) \<rho>"
    using D_def cl_ecl_subst_ecl_distrib by blast

  from ren_\<rho> have ball_is_vars_subst_\<rho>: "\<forall>x\<in>vars_of_cl (cl_ecl C). is_a_variable (Var x \<lhd> \<rho>)"
    using renaming_imp_ball_var by blast

  obtain \<rho>_inv where
    \<rho>_\<rho>_inv_ident: "\<forall>x\<in>vars_of_cl (cl_ecl C). Var x \<lhd> \<rho> \<lhd> \<rho>_inv = Var x" and
    \<rho>_inv_ident_if: "\<forall>x. x \<notin> subst_codomain \<rho> (vars_of_cl (cl_ecl C)) \<longrightarrow>
            Var x \<lhd> \<rho>_inv = Var x" and
    \<rho>_inv_vars: "\<forall>x. is_a_variable (subst (Var x) \<rho>_inv)"
    using renamings_admit_inverse[OF fin_vars_C ren_\<rho>] by auto

  obtain C' T where C_def: "C = Ecl C' T"
    using trms_ecl.cases by blast

  show ?thesis
    unfolding renaming_cl_def
  proof (intro exI conjI)
    show "C = subst_ecl D \<rho>_inv"
      unfolding D_def C_def
      apply (simp del: subst_cl.simps)
      apply (rule conjI)
      using \<rho>_\<rho>_inv_ident[unfolded C_def cl_ecl.simps]
      apply (metis order_refl subst_cl_identI)
      using trms_C[unfolded C_def trms_ecl.simps] by simp
  next
    show "renaming \<rho>_inv (vars_of_cl (cl_ecl D))"
      unfolding renaming_def
    proof (intro ballI conjI allI impI)
      show "\<And>x. x \<in> vars_of_cl (cl_ecl D) \<Longrightarrow> is_a_variable (Var x \<lhd> \<rho>_inv)"
        by (rule \<rho>_inv_vars[rule_format])
    next
      fix x y
      assume x_in: "x \<in> vars_of_cl (cl_ecl D)" and "y \<in> vars_of_cl (cl_ecl D)"
      then obtain x' y' where
        "x' \<in> vars_of_cl (cl_ecl C)" and "Var x = Var x' \<lhd> \<rho>" and
        "y' \<in> vars_of_cl (cl_ecl C)" and "Var y = Var y' \<lhd> \<rho>"
        unfolding cl_ecl_D_conv
        using ex_subst_var_in_vars_if_in_vars_subst_cl[OF _ ball_is_vars_subst_\<rho>]
        by blast
      then show "x \<noteq> y \<Longrightarrow> Var x \<lhd> \<rho>_inv \<noteq> Var y \<lhd> \<rho>_inv"
        using \<rho>_\<rho>_inv_ident[rule_format]
        by (metis trm.inject(1))
    qed
  qed
qed

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
      (\<Union>(case_equation (\<lambda>t1 t2. {t1, t2}) ` atom ` subst_cl (cl_ecl P1) \<sigma>)) trm_ord"
  shows "((C', \<sigma>), (cl_ecl P1, \<sigma>)) \<in> cl_ord"
proof -
  from fact_C' obtain L1 L2 t s u v where
    "eligible_literal L1 P1 \<sigma>" and
    L1_in_P1: "L1 \<in> cl_ecl P1" and
    L2_in_P1: "L2 \<in> cl_ecl P1 - {L1}" and
    orient_L1: "orient_lit_inst L1 t s pos \<sigma>" and
    orient_L2: "orient_lit_inst L2 u v pos \<sigma>" and
    t_\<sigma>_neq_s_\<sigma>: "t \<lhd> \<sigma> \<noteq> s \<lhd> \<sigma>" and
    t_\<sigma>_neq_v_\<sigma>: "t \<lhd> \<sigma> \<noteq> v \<lhd> \<sigma>" and
    unif_t_u: "ck_unifier t u \<sigma> k" and
    C'_def: "C' = cl_ecl P1 - {L2} \<union> {equational_clausal_logic.literal.Neg (Eq s v)}"
    by (auto simp: factorization_def)

  have "(t \<lhd> \<sigma>, s \<lhd> \<sigma>) \<in> trm_ord \<or> (s \<lhd> \<sigma>, t \<lhd> \<sigma>) \<in> trm_ord"
  proof (rule total_trm_ord[unfolded Relation.total_on_def, rule_format])
    have "t \<lhd> \<sigma> \<in> case_equation (\<lambda>t1 t2. {t1, t2}) (atom (subst_lit L1 \<sigma>))"
      using orient_L1 by (auto simp: orient_lit_inst_def)
    thus "t \<lhd> \<sigma> \<in> \<Union> (case_equation (\<lambda>t1 t2. {t1, t2}) ` atom ` subst_cl (cl_ecl P1) \<sigma>)"
      using L1_in_P1 by auto
  next
    have "s \<lhd> \<sigma> \<in> case_equation (\<lambda>t1 t2. {t1, t2}) (atom (subst_lit L1 \<sigma>))"
      using orient_L1 by (auto simp: orient_lit_inst_def)
    thus "s \<lhd> \<sigma> \<in> \<Union> (case_equation (\<lambda>t1 t2. {t1, t2}) ` atom ` subst_cl (cl_ecl P1) \<sigma>)"
      using L1_in_P1 by auto
  next
    show "t \<lhd> \<sigma> \<noteq> s \<lhd> \<sigma>"
      by (rule t_\<sigma>_neq_s_\<sigma>)
  qed

  moreover have "(t \<lhd> \<sigma>, s \<lhd> \<sigma>) \<notin> trm_ord"
    using orient_L1 by (simp add: orient_lit_inst_def)
  ultimately have "(s \<lhd> \<sigma>, t \<lhd> \<sigma>) \<in> trm_ord"
    by simp
  moreover have "t \<lhd> \<sigma> = u \<lhd> \<sigma>"
    by (rule unif_t_u[THEN ck_unifier_thm])
  moreover have "(u \<lhd> \<sigma>, v \<lhd> \<sigma>) \<in> trm_ord \<or> (v \<lhd> \<sigma>, u \<lhd> \<sigma>) \<in> trm_ord"
  proof (rule total_trm_ord[unfolded Relation.total_on_def, rule_format])
    have "u \<lhd> \<sigma> \<in> case_equation (\<lambda>t1 t2. {t1, t2}) (atom (subst_lit L2 \<sigma>))"
      using orient_L2 by (auto simp: orient_lit_inst_def)
    thus "u \<lhd> \<sigma> \<in> \<Union> (case_equation (\<lambda>t1 t2. {t1, t2}) ` atom ` subst_cl (cl_ecl P1) \<sigma>)"
      using L2_in_P1 by auto
  next
    have "v \<lhd> \<sigma> \<in> case_equation (\<lambda>t1 t2. {t1, t2}) (atom (subst_lit L2 \<sigma>))"
      using orient_L2 by (auto simp: orient_lit_inst_def)
    thus "v \<lhd> \<sigma> \<in> \<Union> (case_equation (\<lambda>t1 t2. {t1, t2}) ` atom ` subst_cl (cl_ecl P1) \<sigma>)"
      using L2_in_P1 by auto
  next
    show "u \<lhd> \<sigma> \<noteq> v \<lhd> \<sigma>"
      using t_\<sigma>_neq_v_\<sigma> \<open>t \<lhd> \<sigma> = u \<lhd> \<sigma>\<close> by simp
  qed
  ultimately have "(mset_lit (subst_lit (equational_clausal_logic.literal.Neg (Eq s v)) \<sigma>),
    mset_lit (subst_lit L2 \<sigma>)) \<in> mult trm_ord"
    using orient_L2 unfolding orient_lit_inst_def
    apply -
    apply (rule one_step_implies_mult[of _ _ _ "{#}", simplified])
    by auto

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
    total_trm_ord': "Relation.total_on
      (\<Union>(case_equation (\<lambda>t1 t2. {t1, t2}) ` atom ` subst_cl (cl_ecl P2) \<sigma>)) trm_ord"
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
    u_\<sigma>_neq_v_\<sigma>: "u \<lhd> \<sigma> \<noteq> v \<lhd> \<sigma>" and
    subterm_t_p: "subterm t p u'" and
    ck_unif_u'_u: "ck_unifier u' u \<sigma> Ground" and
    replace_t_v: "replace_subterm t p v t'" and
    L2_lt_L1: "(subst_lit L2 \<sigma>, subst_lit L1 \<sigma>) \<in> lit_ord" and
    L2_max_P2: "strictly_maximal_literal P2 L2 \<sigma>" and
    C'_def: "C' = cl_ecl P1 - {L1} \<union> (cl_ecl P2 - {L2} \<union> {mk_lit polarity (Eq t' s)})"
    unfolding superposition_def
    by blast

  have "(u \<lhd> \<sigma>, v \<lhd> \<sigma>) \<in> trm_ord \<or> (v \<lhd> \<sigma>, u \<lhd> \<sigma>) \<in> trm_ord"
  proof (rule total_trm_ord'[unfolded Relation.total_on_def, rule_format])
    have "u \<lhd> \<sigma> \<in> case_equation (\<lambda>t1 t2. {t1, t2}) (atom (subst_lit L2 \<sigma>))"
      using orient_L2 by (auto simp: orient_lit_inst_def)
    thus "u \<lhd> \<sigma> \<in> \<Union> (case_equation (\<lambda>t1 t2. {t1, t2}) ` atom ` subst_cl (cl_ecl P2) \<sigma>)"
      using L2_in_P2 by auto
  next
    have "v \<lhd> \<sigma> \<in> case_equation (\<lambda>t1 t2. {t1, t2}) (atom (subst_lit L2 \<sigma>))"
      using orient_L2 by (auto simp: orient_lit_inst_def)
    thus "v \<lhd> \<sigma> \<in> \<Union> (case_equation (\<lambda>t1 t2. {t1, t2}) ` atom ` subst_cl (cl_ecl P2) \<sigma>)"
      using L2_in_P2 by auto
  next
    show "u \<lhd> \<sigma> \<noteq> v \<lhd> \<sigma>"
      by (rule u_\<sigma>_neq_v_\<sigma>)
  qed
  hence trm_ord_v_u: "(v \<lhd> \<sigma>, u \<lhd> \<sigma>) \<in> trm_ord"
    using orient_L2[unfolded orient_lit_inst_def] by auto

  have u_eq_u': "u \<lhd> \<sigma> = u' \<lhd> \<sigma>"
    using ck_unif_u'_u by (simp add: ck_unifier_thm)

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

lemma trm_ord_subst_renaming:
  assumes
    ren_\<rho>: "renaming \<rho> (vars_of t \<union> vars_of u)" and
    subst_ren_mem_trm_ord: "(t \<lhd> \<rho>, u \<lhd> \<rho>) \<in> trm_ord"
  shows "(t, u) \<in> trm_ord"
proof -
  from ren_\<rho> obtain \<rho>_inv where
    \<rho>_\<rho>_inv_ident: "\<forall>x \<in> vars_of t \<union> vars_of u. Var x \<lhd> \<rho> \<lhd> \<rho>_inv = Var x"
    using renamings_admit_inverse by blast
  hence "t \<lhd> \<rho> \<lhd> \<rho>_inv = t" and "u \<lhd> \<rho> \<lhd> \<rho>_inv = u"
    by (simp_all add: subst_identI[of "vars_of t \<union> vars_of u" \<rho> \<rho>_inv])
  moreover have "(t \<lhd> \<rho> \<lhd> \<rho>_inv, u \<lhd> \<rho> \<lhd> \<rho>_inv) \<in> trm_ord"
    by (rule trm_ord_subst[rule_format, OF subst_ren_mem_trm_ord, of \<rho>_inv])
  ultimately show ?thesis
    by simp
qed

lemma ground_superposition_main_premise_greater:
  assumes super: "superposition P1 P2 C \<sigma> Ground C'" and
    fin_P1: "finite (cl_ecl P1)" and fin_P2: "finite (cl_ecl P2)"
  shows "((cl_ecl P2, \<sigma>), (cl_ecl P1, \<sigma>)) \<in> cl_ord"
proof -
  from super obtain L M where
    L_in: "L \<in> cl_ecl P1" and
    M_in: "M \<in> cl_ecl P2" and
    M_\<sigma>_lt_L_\<sigma>: "(subst_lit M \<sigma>, subst_lit L \<sigma>) \<in> lit_ord" and
    max_P2_M_\<sigma>: "strictly_maximal_literal P2 M \<sigma>"
    unfolding superposition_def by auto

  show ?thesis
    unfolding cl_ord_def mem_Collect_eq prod.case
  proof (intro one_step_implies_mult[of _ _ _ "{#}", unfolded Multiset.empty_neutral] ballI)
    from L_in have "cl_ecl P1 \<noteq> {}"
      by blast
    with fin_P1 have "mset_set (cl_ecl P1) \<noteq> {#}"
      by (simp add: mset_set_empty_iff)
    then show "mset_cl (cl_ecl P1, \<sigma>) \<noteq> {#}"
      by simp
  next
    fix k assume "k \<in># mset_cl (cl_ecl P2, \<sigma>)"
    then obtain k' where
      k'_in: "k' \<in># mset_set (cl_ecl P2)" and k_def: "k = mset_lit (subst_lit k' \<sigma>)"
      unfolding mset_cl.simps
      by auto

    have M_\<sigma>_lt_L_\<sigma>': "(mset_lit (subst_lit M \<sigma>), mset_lit (subst_lit L \<sigma>)) \<in> mult trm_ord"
      using M_\<sigma>_lt_L_\<sigma>
      unfolding lit_ord_def mem_Collect_eq prod.case
      by argo

    have "(k, mset_lit (subst_lit L \<sigma>)) \<in> mult trm_ord"
    proof (cases "k' = M")
      case True
      thus ?thesis
        using M_\<sigma>_lt_L_\<sigma>' k_def by argo
    next
      case False
      show ?thesis
      proof (rule trans_mult[OF trm_ord_trans, THEN transD, OF _ M_\<sigma>_lt_L_\<sigma>'])
        have "(subst_lit k' \<sigma>, subst_lit M \<sigma>) \<in> lit_ord"
          using False k'_in max_P2_M_\<sigma>[unfolded strictly_maximal_literal_def]
          using fin_P2 finite_set_mset_mset_set by blast
        then show "(k, mset_lit (subst_lit M \<sigma>)) \<in> mult trm_ord"
          unfolding k_def
          using lit_ord_def by blast
      qed
    qed

    moreover have "mset_lit (subst_lit L \<sigma>) \<in># mset_cl (cl_ecl P1, \<sigma>)"
      using L_in
      by (simp add: fin_P1)

    ultimately show "\<exists>j\<in>#mset_cl (cl_ecl P1, \<sigma>). (k, j) \<in> mult trm_ord"
      by metis
  qed
qed

end


subsection \<open>Prover\<close>

type_synonym 'a fclause = "'a literal fset"

locale renamings =
  fixes renamings_apart :: "'a fclause list \<Rightarrow> 'a subst list"
  assumes
    renamings_apart_length: "length (renamings_apart Cs) = length Cs" and
    renamings_apart_renaming:
      "list_all2 (\<lambda>C \<rho>. renaming \<rho> (vars_of_cl (fset C))) Cs (renamings_apart Cs)" and
    renamings_apart_var_disjoint: "\<forall>i < length Cs. \<forall>j < length Cs. i \<noteq> i \<longrightarrow>
      range_vars (renamings_apart Cs ! i) \<inter> range_vars (renamings_apart Cs ! j) = {}"

locale superposition_prover = renamings renamings_apart
  for
    renamings_apart :: "'a fclause list \<Rightarrow> 'a subst list" +
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
    select_subset: "\<forall>C. select C \<subseteq> C" and
    select_neg: "\<forall>C. \<forall>L \<in> select C. negative_literal L" and
    select_renaming_strong:
      "\<forall>\<eta> C. renaming \<eta> (vars_of_cl C) \<longrightarrow> select (subst_cl C \<eta>) = subst_cl (select C) \<eta>" and
    select_stable_under_grounding:
      "\<forall>C \<gamma>. ground_clause (subst_cl C \<gamma>) \<longrightarrow> select (subst_cl C \<gamma>) = subst_cl (select C) \<gamma>" and
    infinite_vars: "infinite (UNIV :: 'a set)"
begin

lemma select_renaming: "\<forall>\<eta> C. renaming \<eta> (vars_of_cl C) \<longrightarrow> select C = {} \<longrightarrow> select (subst_cl C \<eta>) = {}"
  using select_renaming_strong by simp

text \<open>
These simplification rules often hurt more than they help.
Better to remove it and selectively add them tho @{method simp} when necessary.
\<close>

lemmas [simp del] = equational_clausal_logic.ground_clause.simps
lemmas [simp del] = equational_clausal_logic.subst_cl.simps
lemmas [simp del] = equational_clausal_logic.validate_ground_clause.simps
lemmas [simp del] = equational_clausal_logic.vars_of_cl.simps
lemmas [simp del] = terms.subst_set.simps

lemma subst_set_empty[simp]: "subst_set {} \<sigma> = {}"
  by (simp add: subst_set.simps)


subsubsection \<open>Ground Selection at an Arbitrary Limit\<close>

definition ground_select :: "'a clause set \<Rightarrow> 'a clause \<Rightarrow> 'a clause" where
  "ground_select M C =
    (if C \<in> (\<Union>D \<in> M. {subst_cl D \<sigma> | \<sigma>. ground_clause (subst_cl D \<sigma>)}) then
      (SOME C'. \<exists>D \<in> M. \<exists>\<sigma>. C = subst_cl D \<sigma> \<and> ground_clause (subst_cl D \<sigma>) \<and>
        C' = subst_cl (select D) \<sigma>)
    else
      select C)"

lemma ground_select_at_limit_grounding:
  assumes "C \<in> (\<Union>D \<in> M. {subst_cl D \<gamma> | \<gamma>. ground_clause (subst_cl D \<gamma>)})"
  shows "\<exists>D \<in> M. \<exists>\<gamma>. C = subst_cl D \<gamma> \<and> ground_clause (subst_cl D \<gamma>) \<and>
    ground_select M C = subst_cl (select D) \<gamma>"
  unfolding ground_select_def eqTrueI[OF assms] if_True
proof (rule someI_ex)
  from assms show "\<exists>D'. \<exists>D\<in>M. \<exists>\<gamma>. C = subst_cl D \<gamma> \<and> ground_clause (subst_cl D \<gamma>) \<and>
    D' = subst_cl (select D) \<gamma>"
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
      using select_subset
      by (smt (verit) Collect_mono_iff subsetD subst_cl.simps)
  next
    case False
    then show ?thesis
      using L_in select_subset
      by (metis (no_types, lifting) ground_select_def subsetD)
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


lemma derivable_imp_G_derivable_list:
  assumes "G_SuperCalc.derivable M C P N \<sigma> k C'"
  shows "\<exists>Ps. P = set Ps \<and> G_derivable_list M C Ps \<sigma> k C'"
  using assms
  unfolding G_SuperCalc.derivable_def G_derivable_list_def
  by (metis doubleton_eq_iff list.simps(15) set_empty2)

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

lemma ball_side_prems_less_than_main_prem_if_G_derivable_list:
  assumes
    deriv: "G_derivable_list M C Ps \<sigma> G_SuperCalc.Ground C'" and
    ball_Ps_finite: "\<forall>C\<in>set Ps. finite (cl_ecl C)"
  shows "\<forall>D \<in> set (butlast Ps). ((cl_ecl D, \<sigma>), cl_ecl (last Ps), \<sigma>) \<in> G_SuperCalc.cl_ord"
  using deriv
  unfolding G_derivable_list_def
proof (elim disjE exE conjE)
  fix P1 P2
  assume
    Ps_def: "Ps = [P2, P1]" and
    super: "G_SuperCalc.superposition M P1 P2 C \<sigma> G_SuperCalc.Ground C'"
  then show "\<forall>D\<in>set (butlast Ps).
          ((cl_ecl D, \<sigma>), cl_ecl (last Ps), \<sigma>) \<in> G_SuperCalc.cl_ord"
    using G_SuperCalc.ground_superposition_main_premise_greater
    by (simp add: ball_Ps_finite)
next
  show "\<And>P1. Ps = [P1] \<Longrightarrow> G_SuperCalc.factorization M P1 C \<sigma> G_SuperCalc.Ground C' \<Longrightarrow> ?thesis"
    by simp
next
  show "\<And>P1. Ps = [P1] \<Longrightarrow> G_SuperCalc.reflexion M P1 C \<sigma> G_SuperCalc.Ground C' \<Longrightarrow> ?thesis"
    by simp
qed


subsubsection \<open>Ground calculus\<close>

definition G_Inf :: "'a clause set \<Rightarrow> 'a fclause inference set" where
  "G_Inf M \<equiv> {Infer Ps (Abs_fset C') | Ps C \<sigma> C'.
    (\<forall>D \<in> set Ps. ground_clause (fset D)) \<and>
    G_derivable_list M C (map (\<lambda>D. Ecl (fset D) {}) Ps) \<sigma> G_SuperCalc.Ground C'}"

lemma G_Inf_have_prems: "\<iota> \<in> G_Inf M \<Longrightarrow> prems_of \<iota> \<noteq> []"
  by (auto simp: G_Inf_def G_derivable_list_def)

lemma G_Inf_ground_concl: "\<iota> \<in> G_Inf M \<Longrightarrow> ground_clause (fset (concl_of \<iota>))"
  unfolding G_Inf_def mem_Collect_eq
  apply safe
  apply simp
  apply (frule G_derivable_list_ground_premises[rotated])
   apply simp
  unfolding substs_preserve_ground_clause
  using G_derivable_list_finite_conclusion[THEN Abs_fset_inverse[simplified]]
  by (smt (verit, best) cl_ecl.simps ex_map_conv finite_fset)

definition fclause_ord :: "'a fclause \<Rightarrow> 'a fclause \<Rightarrow> bool" where
  "fclause_ord C D \<equiv> ((fset C, []), (fset D, [])) \<in> G_SuperCalc.cl_ord"

lemma transp_fclause_ord: "transp fclause_ord"
  unfolding fclause_ord_def
  by (auto intro: transpI G_SuperCalc.cl_ord_trans[THEN transD])

lemma wfP_fclause_ord: "wfP fclause_ord"
  unfolding fclause_ord_def wfP_def
  by (rule compat_wf[of _ _ "\<lambda>C. (fset C, [])", OF _ G_SuperCalc.wf_cl_ord])
    (simp add: compat_def)

lemma G_Inf_reductive:
  assumes \<iota>_in: "\<iota> \<in> G_Inf M"
  shows "fclause_ord (concl_of \<iota>) (main_prem_of \<iota>)"
proof -
  from \<iota>_in[unfolded G_Inf_def mem_Collect_eq] obtain Ps C \<sigma> C' where
    \<iota>_def: "\<iota> = Infer Ps (Abs_fset C')" and
    Ps_ground: "\<forall>C \<in> set Ps. ground_clause (fset C)" and
    deriv_Ps: "G_derivable_list M C (map (\<lambda>C. Ecl (fset C) {}) Ps) \<sigma> G_SuperCalc.Ground C'"
    by blast

  have ground_C': "ground_clause C'"
    using Ps_ground
    by (auto intro!: G_derivable_list_ground_premises[OF _ deriv_Ps])

  have "fclause_ord (Abs_fset C') (last Ps)"
    using deriv_Ps[unfolded G_derivable_list_def]
  proof (elim disjE exE conjE)
    fix P1
    assume map_Ps_conv: "map (\<lambda>C. Ecl (fset C) {}) Ps = [P1]" and
      refl_P1: "G_SuperCalc.reflexion M P1 C \<sigma> G_SuperCalc.Ground C'"
    with Ps_ground have fin_P1: "finite (cl_ecl P1)" and ground_P1: "ground_clause (cl_ecl P1)"
      by auto

    from map_Ps_conv have last_Ps_conv: "last Ps = Abs_fset (cl_ecl P1)"
      by (metis cl_ecl.simps fset_inverse last_ConsL last_map list.distinct(1) list.simps(8))

    from fin_P1 refl_P1 have fin_C': "finite C'"
      using G_SuperCalc.reflexion_preserves_finiteness by blast

    show ?thesis
      unfolding fclause_ord_def last_Ps_conv
      unfolding Abs_fset_inverse[simplified, OF fin_C']
      unfolding Abs_fset_inverse[simplified, OF fin_P1]
      using G_SuperCalc.reflexion_conclusion_smaller[OF refl_P1 fin_P1]
      using ground_C' ground_P1
      by (metis G_SuperCalc.cl_ord_ground_subst)
  next
    fix P1
    assume
      map_Ps_conv: "map (\<lambda>C. Ecl (fset C) {}) Ps = [P1]" and
      fact_P1: "G_SuperCalc.factorization M P1 C \<sigma> G_SuperCalc.Ground C'"
    with Ps_ground have fin_P1: "finite (cl_ecl P1)" and ground_P1: "ground_clause (cl_ecl P1)"
      by auto

    from map_Ps_conv have last_Ps_conv: "last Ps = Abs_fset (cl_ecl P1)"
      by (metis cl_ecl.simps fset_inverse last_ConsL last_map list.distinct(1) list.simps(8))

    from fin_P1 fact_P1 have fin_C': "finite C'"
      using G_SuperCalc.factorization_preserves_finiteness by blast

    show ?thesis
      unfolding fclause_ord_def last_Ps_conv
      unfolding Abs_fset_inverse[simplified, OF fin_C']
      unfolding Abs_fset_inverse[simplified, OF fin_P1]
      using G_SuperCalc.factorization_conclusion_smaller[OF fact_P1 fin_P1]
      using G_SuperCalc.trm_ord_total_on_ground_clause
      using ground_C' ground_P1
      by (metis G_SuperCalc.cl_ord_ground_subst substs_preserve_ground_clause)
  next
    fix P1 P2
    assume
      map_Ps_conv: "map (\<lambda>C. Ecl (fset C) {}) Ps = [P2, P1]" and
      super_P1_P2: "G_SuperCalc.superposition M P1 P2 C \<sigma> G_SuperCalc.Ground C'"
    with Ps_ground have
      fin_P1: "finite (cl_ecl P1)" and ground_P1: "ground_clause (cl_ecl P1)" and
      fin_P2: "finite (cl_ecl P2)" and ground_P2: "ground_clause (cl_ecl P2)"
      by auto

    from fin_P1 fin_P2 super_P1_P2 have fin_C': "finite C'"
      using G_SuperCalc.superposition_preserves_finiteness by blast

    from map_Ps_conv have last_Ps_conv: "last Ps = Abs_fset (cl_ecl P1)"
      by (metis cl_ecl.simps fset_inverse last.simps last_map list.discI list.map_disc_iff)

    have "((C', \<sigma>), cl_ecl P1, \<sigma>) \<in> G_SuperCalc.cl_ord"
    proof (rule G_SuperCalc.superposition_conclusion_smaller[OF super_P1_P2 fin_P1 fin_P2])
      show "Relation.total_on
        (\<Union> (case_equation (\<lambda>t1 t2. {t1, t2}) ` atom ` subst_cl (cl_ecl P2) \<sigma>)) trm_ord"
        using G_SuperCalc.trm_ord_total_on_ground_clause ground_P2
        by (simp add: substs_preserve_ground_clause)
    qed
    thus ?thesis
      unfolding fclause_ord_def last_Ps_conv
      unfolding Abs_fset_inverse[simplified, OF fin_C']
      unfolding Abs_fset_inverse[simplified, OF fin_P1]
      by (rule G_SuperCalc.cl_ord_ground_subst[OF _ ground_C' ground_P1])
  qed
  thus ?thesis
    unfolding \<iota>_def inference.sel
    unfolding substs_preserve_ground_clause[OF ground_C']
    using G_derivable_list_non_empty_premises[OF deriv_Ps, simplified]
    by (simp add: last_map)
qed


definition entails :: "'a fclause set \<Rightarrow> 'a fclause set \<Rightarrow> bool" (infix "\<TTurnstile>e" 50) where
  "N1 \<TTurnstile>e N2 \<equiv> set_entails_set (fset ` N1) (fset ` N2)"


interpretation G: consequence_relation "{{||}}" entails
proof unfold_locales
  show "{{||}} \<noteq> {}"
    by simp
next
  show "\<And>B N1. B \<in> {{||}} \<Longrightarrow> {B} \<TTurnstile>e N1"
    unfolding entails_def
    by (simp add: set_entails_set_def subst_cl.simps ground_clause.simps
        validate_ground_clause.simps vars_of_cl.simps)
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

interpretation G: sound_inference_system "G_Inf M" "{{||}}" entails
proof unfold_locales
  fix \<iota> :: "'a fclause inference"
  assume "\<iota> \<in> G_Inf M"
  then obtain Ps C \<sigma> C' where
    \<iota>_def: "\<iota> = Infer Ps (Abs_fset C')" and
    ball_Ps_ground: "\<forall>C \<in> set Ps. ground_clause (fset C)" and
    deriv_Ps: "G_derivable_list M C (map (\<lambda>C. Ecl (fset C) {}) Ps) \<sigma> G_SuperCalc.Ground C'"
    unfolding G_Inf_def mem_Collect_eq by blast

  from deriv_Ps have cl_ecl_C_conv: "cl_ecl C = subst_cl C' \<sigma>"
    by (simp add: G_derivable_list_concl_conv)

  have ground_C': "ground_clause C'"
    using ball_Ps_ground G_derivable_list_ground_premises[OF _ deriv_Ps] by simp

  have fin_C': "finite C'"
    using ball_Ps_ground G_derivable_list_finite_conclusion[OF _ deriv_Ps] by simp
    

  have concl_\<iota>_conv: "fset (concl_of \<iota>) = cl_ecl C"
    unfolding \<iota>_def inference.sel
    unfolding Abs_fset_inverse[simplified, OF fin_C']
    unfolding cl_ecl_C_conv
    unfolding substs_preserve_ground_clause[OF ground_C']
    by (rule refl)

  from deriv_Ps show "set (prems_of \<iota>) \<TTurnstile>e {concl_of \<iota>}"
    unfolding G_derivable_list_def
  proof (elim disjE exE conjE)
    fix P1 P2
    assume
      map_P_conv: "map (\<lambda>C. Ecl (fset C) {}) Ps = [P2, P1]" and
      super_P1_P2: "G_SuperCalc.superposition M P1 P2 C \<sigma> G_SuperCalc.Ground C'"
    hence "set_entails_clause {cl_ecl P1, cl_ecl P2} (cl_ecl C)"
      using ball_Ps_ground by (auto intro: G_SuperCalc.superposition_is_sound)
    moreover have "fset ` set (prems_of \<iota>) = {cl_ecl P1, cl_ecl P2}"
      unfolding \<iota>_def inference.sel using map_P_conv by force
    ultimately show "set (prems_of \<iota>) \<TTurnstile>e {concl_of \<iota>}"
      unfolding entails_def by (simp add: concl_\<iota>_conv)
  next
    fix P1
    assume
      map_P_conv: "map (\<lambda>C. Ecl (fset C) {}) Ps = [P1]" and
      fact_P1: "G_SuperCalc.factorization M P1 C \<sigma> G_SuperCalc.Ground C'"
    hence "clause_entails_clause (cl_ecl P1) (cl_ecl C)"
      using ball_Ps_ground by (auto intro: G_SuperCalc.factorization_is_sound)
    moreover have "fset ` set (prems_of \<iota>) = {cl_ecl P1}"
      unfolding \<iota>_def inference.sel using map_P_conv by force
    ultimately show "set (prems_of \<iota>) \<TTurnstile>e {concl_of \<iota>}"
      unfolding entails_def by (simp add: concl_\<iota>_conv)
  next
    fix P1
    assume
      map_P_conv: "map (\<lambda>C. Ecl (fset C) {}) Ps = [P1]" and
      refl_P1: "G_SuperCalc.reflexion M P1 C \<sigma> G_SuperCalc.Ground C'"
    hence "clause_entails_clause (cl_ecl P1) (cl_ecl C)"
      using ball_Ps_ground by (auto intro: G_SuperCalc.reflexion_is_sound)
    moreover have "fset ` set (prems_of \<iota>) = {cl_ecl P1}"
      unfolding \<iota>_def inference.sel using map_P_conv by force
    ultimately show "set (prems_of \<iota>) \<TTurnstile>e {concl_of \<iota>}"
      unfolding entails_def by (simp add: concl_\<iota>_conv)
  qed
qed

interpretation G: calculus_with_finitary_standard_redundancy "G_Inf M" "{{||}}" "(\<TTurnstile>e)" fclause_ord
  using wfP_fclause_ord transp_fclause_ord G_Inf_have_prems G_Inf_reductive
  by (unfold_locales)

sublocale statically_complete_calculus "{{||}}" "G_Inf M" "(\<TTurnstile>e)" "G.Red_I M" G.Red_F
proof unfold_locales
  fix B :: "'a fclause" and N :: "'a fclause set"
  assume B_in: "B \<in> {{||}}" and satur_N: "G.saturated M N" and N_entails_B: "N \<TTurnstile>e {B}"

  have ground_fclause: "ground_clause (fset C)" for C :: "'a fclause"
    sorry

  have gr_inf_satur_N: "G_SuperCalc.ground_inference_saturated M ((\<lambda>C. Ecl (fset C) {}) ` N)"
    unfolding G_SuperCalc.ground_inference_saturated_def
  proof (intro allI impI)
    fix C P \<sigma> C'
    assume
      deriv_C_P: "G_SuperCalc.derivable M C P ((\<lambda>C. Ecl (fset C) {}) ` N) \<sigma> G_SuperCalc.Ground C'" and
      ground_C: "ground_clause (cl_ecl C)" and
      grounding_P: "G_SuperCalc.grounding_set P \<sigma>"

    from deriv_C_P have P_subset: "P \<subseteq> ((\<lambda>C. Ecl (fset C) {}) ` N)"
      by (simp add: G_SuperCalc.derivable_premisses)
    hence ball_P_fin: "\<forall>C \<in> P. finite (cl_ecl C)"
      by auto
    with deriv_C_P have fin_cl_C: "finite (cl_ecl C)"
      using G_SuperCalc.derivable_clauses_are_finite by metis

    from deriv_C_P obtain Ps
      where P_eq: "P = set Ps" and deriv_C_Ps: "G_derivable_list M C Ps \<sigma> G_SuperCalc.Ground C'"
      by (auto dest: derivable_imp_G_derivable_list)

    from deriv_C_Ps obtain P1 Ps' where Ps_eq: "Ps = Ps' @ [P1]"
      unfolding G_derivable_list_def by auto

    from P_eq have ball_Ps_finite: "\<forall>C\<in>set Ps. finite (cl_ecl C)"
      using ball_P_fin by fastforce
      
    define \<iota> :: "'a fclause inference" where
      "\<iota> = Infer (map (Abs_fset \<circ> cl_ecl) Ps) (Abs_fset (cl_ecl C))"

    have foo: "\<exists>D. G_derivable_list M D (map (\<lambda>D. Ecl (fset D) {}) (map (Abs_fset \<circ> cl_ecl) Ps)) \<sigma>
        G_SuperCalc.Ground (cl_ecl C)"
      using deriv_C_Ps
      unfolding G_derivable_list_def
      (* by (smt (verit, del_insts) Abs_fset_inverse G_SuperCalc.derivable_clauses_lemma G_SuperCalc.derivable_finite_conclusion P_eq P_subset ball_P_fin cl_ecl.simps comp_apply deriv_C_P fset_inverse ground_fclause image_iff insert_subset list.simps(15) list.simps(8) list.simps(9) mem_Collect_eq substs_preserve_ground_clause) *)
      apply (elim disjE exE conjE)
        apply (smt (verit) Abs_fset_inverse G_SuperCalc.derivable_clauses_lemma
          G_SuperCalc.derivable_finite_conclusion P_eq P_subset ball_P_fin cl_ecl.simps deriv_C_P
          fset_inverse ground_fclause image_iff insert_subset list.map_comp list.simps(15)
          list.simps(8) list.simps(9) mem_Collect_eq substs_preserve_ground_clause)
       apply (smt (verit, ccfv_threshold) Abs_fset_inverse G_SuperCalc.derivable_clauses_lemma
          G_SuperCalc.derivable_finite_conclusion P_eq P_subset ball_P_fin cl_ecl.simps comp_apply
          deriv_C_P fset_inverse ground_fclause image_iff insert_subset list.simps(15) list.simps(8)
          list.simps(9) mem_Collect_eq substs_preserve_ground_clause)
      by (smt (verit, ccfv_threshold) G_SuperCalc.derivable_clauses_lemma
          G_SuperCalc.ground_clause_reflexion P_eq P_subset cl_ecl.simps deriv_C_P fset_inverse
          ground_fclause image_iff insert_subset list.map_comp list.simps(15) list.simps(8)
          list.simps(9) substs_preserve_ground_clause)
    then have "\<iota> \<in> G_Inf M"
      unfolding G_Inf_def mem_Collect_eq
      using \<iota>_def ground_fclause by blast

    moreover from P_subset have prems_\<iota>_subset: "set (prems_of \<iota>) \<subseteq> N"
      by (auto simp: \<iota>_def P_eq[symmetric] subset_image_iff image_subset_iff image_iff subset_iff
          fset_inverse)

    ultimately have "G.redundant_infer N \<iota>"
      using satur_N[unfolded G.saturated_def G.Inf_from_def G.Red_I_def G.Red_I_def] by blast
    then obtain DD :: "'a fclause set" where
      "DD \<subseteq> N" and "finite DD" and "DD \<union> set (side_prems_of \<iota>) \<TTurnstile>e {concl_of \<iota>}" and
      ball_D_less: "\<forall>D\<in>DD. fclause_ord D (main_prem_of \<iota>)"
      unfolding G.redundant_infer_def by metis

    define S  :: "('a eclause \<times> 'a subst) set" where
      "S = (\<lambda>D. (Ecl (fset D) {}, [])) ` (DD \<union> set (side_prems_of \<iota>))"

    show "G_SuperCalc.redundant_inference C ((\<lambda>C. Ecl (fset C) {}) ` N) P \<sigma>"
      unfolding G_SuperCalc.redundant_inference_def
    proof (intro exI conjI)
      show "S \<subseteq> G_SuperCalc.instances ((\<lambda>C. Ecl (fset C) {}) ` N)"
      proof (rule Set.subsetI)
        have inj_mk_instance: "inj (\<lambda>D. (Ecl (fset D) {}, []))"
          by (rule injI) (simp add: fset_inject)

        fix x assume "x \<in> S"
        then obtain D where
          "D \<in> DD \<or> D \<in> set (side_prems_of \<iota>)" and x_def: "x = (Ecl (fset D) {}, [])"
          by (auto simp add: S_def image_Un image_iff)
        thus "x \<in> G_SuperCalc.instances ((\<lambda>C. Ecl (fset C) {}) ` N)"
        proof (elim disjE)
          assume "D \<in> DD"
          thus ?thesis
            using \<open>DD \<subseteq> N\<close>
            by (auto simp add: x_def G_SuperCalc.instances_def ground_fclause)
        next
          assume "D \<in> set (side_prems_of \<iota>)"
          hence "D \<in> N"
            using prems_\<iota>_subset
            by (meson in_set_butlastD subsetD)
          thus ?thesis
            by (auto simp add: x_def G_SuperCalc.instances_def ground_fclause)
        qed
      qed
    next
      have "set_entails_clause (fset ` (DD \<union> set (side_prems_of \<iota>))) (fset (concl_of \<iota>))"
        using \<open>DD \<union> set (side_prems_of \<iota>) \<TTurnstile>e {concl_of \<iota>}\<close>
        by (simp add: entails_def image_Un)

      moreover have "(fset (concl_of \<iota>)) = cl_ecl C"
        using fin_cl_C
        by (simp add: \<iota>_def Abs_fset_inverse)

      moreover have "fset ` (DD \<union> set (side_prems_of \<iota>)) = G_SuperCalc.clset_instances S"
        unfolding S_def \<iota>_def inference.sel
        unfolding Ps_eq map_append list.map butlast_snoc
        by (auto simp: G_SuperCalc.clset_instances_def)

      ultimately show "set_entails_clause (G_SuperCalc.clset_instances S) (cl_ecl C)"
        by simp
    next
      show "\<forall>x \<in> S. G_SuperCalc.subterms_inclusion (subst_set (trms_ecl (fst x)) (snd x))
        (trms_ecl C)"
        by (simp add: S_def)
    next
      show "\<forall>x \<in> S. \<exists>D' \<in> cl_ecl ` P. ((cl_ecl (fst x), snd x), D', \<sigma>) \<in> G_SuperCalc.cl_ord"
      proof (intro ballI bexI)
        from ball_P_fin show "fset (main_prem_of \<iota>) \<in> cl_ecl ` P"
          unfolding \<iota>_def inference.sel P_eq
          unfolding Ps_eq map_append list.map last_snoc
          by (simp add: Abs_fset_inverse)
      next
        fix x assume "x \<in> S"
        then obtain D where
          "D \<in> DD \<or> D \<in> set (side_prems_of \<iota>)" and x_def: "x = (Ecl (fset D) {}, [])"
          by (auto simp add: S_def image_Un image_iff)
        thus "((cl_ecl (fst x), snd x), fset (main_prem_of \<iota>), \<sigma>) \<in> G_SuperCalc.cl_ord"
        proof (elim disjE)
          assume "D \<in> DD"
          hence "fclause_ord D (main_prem_of \<iota>)"
            using ball_D_less by simp
          thus ?thesis
            by (smt (verit, ccfv_threshold) CollectD CollectI G_SuperCalc.cl_ord_def
                G_SuperCalc.mset_cl.simps case_prodD case_prodI cl_ecl.simps equal_image_mset
                fclause_ord_def fst_conv ground_fclause substs_preserve_ground_lit x_def)
        next
          have fin_P1: "finite (cl_ecl P1)"
            by (simp add: Ps_eq ball_Ps_finite)

          assume "D \<in> set (side_prems_of \<iota>)"
          hence "D \<in> set (map (Abs_fset \<circ> cl_ecl) Ps')"
            unfolding \<iota>_def inference.sel Ps_eq map_append list.map butlast_snoc .
          then obtain D' where "D' \<in> set Ps'" and D_def: "D = Abs_fset (cl_ecl D')"
            by auto
          hence "((cl_ecl D', \<sigma>), cl_ecl P1, \<sigma>) \<in> G_SuperCalc.cl_ord"
            using ball_side_prems_less_than_main_prem_if_G_derivable_list[OF deriv_C_Ps
                ball_Ps_finite]
            by (simp add: Ps_eq)
          hence "((cl_ecl D', []), (cl_ecl P1, \<sigma>)) \<in> G_SuperCalc.cl_ord"
            by (smt (verit, best) Abs_fset_inverse CollectD CollectI G_SuperCalc.cl_ord_def
                G_SuperCalc.mset_cl.simps Ps_eq \<open>D' \<in> set Ps'\<close> append.assoc append_Cons
                ball_Ps_finite case_prodD case_prodI equal_image_mset ground_fclause
                in_set_conv_decomp substs_preserve_ground_lit)
          moreover have "(cl_ecl (fst x), snd x) = (cl_ecl D', [])"
            by (simp add: x_def D_def Abs_fset_inverse P_eq Ps_eq \<open>D' \<in> set Ps'\<close> ball_P_fin)
          moreover have "fset (main_prem_of \<iota>) = cl_ecl P1"
            using fin_P1
            by (simp add: \<iota>_def Ps_eq Abs_fset_inverse)
          ultimately show ?thesis
            by simp
        qed
      qed
    qed
  qed

  have ball_N_finite: "\<forall>x\<in>(\<lambda>C. Ecl (fset C) {}) ` N. finite (cl_ecl x)"
    by simp

  have ball_N_well_const: "\<forall>x \<in> ((\<lambda>C. Ecl (fset C) {}) ` N). G_SuperCalc.well_constrained x"
    by (simp add: G_SuperCalc.well_constrained_def)

  have closed_under_ren_N: "closed_under_renaming ((\<lambda>C. Ecl (fset C) {}) ` N)"
    unfolding closed_under_renaming_def
    using ground_fclause
    by (metis (no_types, lifting) image_iff renaming_cl_def subst_ecl.simps subst_set.simps
        subst_set_empty substs_preserve_ground_clause)

  define I where
    "I = G_SuperCalc.same_values (\<lambda>t. G_SuperCalc.trm_rep M t ((\<lambda>C. Ecl (fset C) {}) ` N))"

  have int_clset_is_a_model': "(\<And>x. x \<in> N \<Longrightarrow> fset x \<noteq> {}) \<Longrightarrow> C \<in> (\<lambda>C. Ecl (fset C) {}) ` N \<Longrightarrow>
    ground_clause (subst_cl (cl_ecl C) \<sigma>) \<Longrightarrow>
    G_SuperCalc.all_trms_irreducible (subst_set (trms_ecl C) \<sigma>)
      (\<lambda>t. G_SuperCalc.trm_rep M t ((\<lambda>C. Ecl (fset C) {}) ` N)) \<Longrightarrow>
    validate_ground_clause I (subst_cl (cl_ecl C) \<sigma>)"
    for C \<sigma>
    using G_SuperCalc.int_clset_is_a_model[OF gr_inf_satur_N ball_N_finite ball_N_well_const _
      closed_under_ren_N, folded I_def, of "(_, _)"]
    by simp

  have fo_int_I: "fo_interpretation I"
    unfolding I_def
    using G_SuperCalc.same_values_fo_int G_SuperCalc.trm_rep_compatible_with_structure by blast

  from B_in N_entails_B have "set_entails_clause (fset ` N) {}"
    by (simp add: entails_def)
  hence "{||} \<in> N"
  proof (rule contrapos_pp)
    assume "{||} \<notin> N"
    hence ball_N_not_empty: "\<forall>C \<in> N. C \<noteq> {||}"
      by auto
  
    have validate_I_N: "validate_clause_set I (fset ` N)"
      unfolding validate_clause_set.simps validate_clause.simps
    proof (intro allI impI)
      fix C \<sigma>
      assume C_in: "C \<in> fset ` N" and gr_cl_C_\<sigma>: "ground_clause (subst_cl C \<sigma>)"
      show "validate_ground_clause I (subst_cl C \<sigma>)"
      proof (rule int_clset_is_a_model'[of "Ecl C {}" \<sigma>, unfolded cl_ecl.simps])
        show "\<And>x. x \<in> N \<Longrightarrow> fset x \<noteq> {}"
          using \<open>{||} \<notin> N\<close>
          by (metis bot_fset.rep_eq fset_cong)
      next
        show "Ecl C {} \<in> (\<lambda>C. Ecl (fset C) {}) ` N"
          using C_in by auto
      next
        show "ground_clause (subst_cl C \<sigma>)"
          by (rule gr_cl_C_\<sigma>)
      next
        show "G_SuperCalc.all_trms_irreducible (subst_set (trms_ecl (Ecl C {})) \<sigma>)
     (\<lambda>t. G_SuperCalc.trm_rep M t ((\<lambda>C. Ecl (fset C) {}) ` N))"
          by simp
      qed
    qed
  
    show "\<not> set_entails_clause (fset ` N) {}"
    proof (rule notI)
      assume "set_entails_clause (fset ` N) {}"
      hence "validate_ground_clause I {}"
        using fo_int_I validate_I_N
        by (simp add: set_entails_clause_def)
      thus False
        by (simp add: validate_ground_clause.simps)
    qed
  qed
  thus "\<exists>B'\<in>{{||}}. B' \<in> N"
    by simp
qed


subsubsection \<open>First-Order SuperCalc\<close>

interpretation SuperCalc: basic_superposition trm_ord select pos_ord "UNIV :: 'a set" "\<lambda>_ _. {}"
  using trm_ord_wf trm_ord_trans trm_ord_irrefl trm_ord_reduction_left trm_ord_reduction_right
    trm_ord_subterm trm_ord_subst pos_ord_irrefl pos_ord_prefix pos_ord_nil infinite_vars
    select_subset select_neg select_renaming G_SuperCalc.trm_ord_ground_total
    G_SuperCalc.pos_ord_trans
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
      apply (rule subst_ecl_ident[symmetric])
      unfolding Un_iff
      apply (erule disjE)
      subgoal for x t
        apply (drule \<rho>_\<rho>_inv_ident[rule_format])
        oops

lemma eligible_literal_renaming:
  assumes eligible: "SuperCalc.eligible_literal L1 P1 \<sigma>\<^sub>C" and "L1 \<in> cl_ecl P1" and
    ren_\<rho>: "renaming \<rho> (vars_of_cl (cl_ecl P1))" and
    "\<forall>x\<in>vars_of_cl (cl_ecl P1). Var x \<lhd> \<rho> \<lhd> \<rho>_inv = Var x" and
    "\<forall>x. x \<notin> subst_codomain \<rho> (vars_of_cl (cl_ecl P1)) \<longrightarrow> Var x \<lhd> \<rho>_inv = Var x"
  shows "SuperCalc.eligible_literal (equational_clausal_logic.subst_lit L1 \<rho>) (subst_ecl P1 \<rho>)
    (\<rho>_inv \<lozenge> \<sigma>\<^sub>C)"
  using eligible[unfolded SuperCalc.eligible_literal_def]
proof (elim disjE conjE)
  assume "L1 \<in> select (cl_ecl P1)"
  then show ?thesis
    unfolding SuperCalc.eligible_literal_def cl_ecl_subst_ecl_distrib
    using select_renaming_strong[rule_format, of \<rho> "cl_ecl P1", OF ren_\<rho>]
    by (simp add: subst_cl_conv)
next
  have subst_P1_\<rho>_\<rho>_inv: "subst_cl (subst_cl (cl_ecl P1) \<rho>) \<rho>_inv = cl_ecl P1"
    using subst_cl_identI[OF \<open>\<forall>x\<in>vars_of_cl (cl_ecl P1). Var x \<lhd> \<rho> \<lhd> \<rho>_inv = Var x\<close>]
    by simp

  assume "select (cl_ecl P1) = {}" and
    "SuperCalc.maximal_literal (equational_clausal_logic.subst_lit L1 \<sigma>\<^sub>C) (subst_cl (cl_ecl P1) \<sigma>\<^sub>C)"
  thus ?thesis
    unfolding SuperCalc.eligible_literal_def cl_ecl_subst_ecl_distrib
    unfolding select_renaming_strong[rule_format, of \<rho> "cl_ecl P1", OF ren_\<rho>]
    apply simp
    unfolding SuperCalc.maximal_literal_def
    unfolding composition_of_substs_cl[symmetric]
    unfolding subst_P1_\<rho>_\<rho>_inv
    by (metis \<open>L1 \<in> cl_ecl P1\<close> \<open>\<forall>x\<in>vars_of_cl (cl_ecl P1). Var x \<lhd> \<rho> \<lhd> \<rho>_inv = Var x\<close>
        composition_of_substs_lit subst_lit_identI vars_of_cl_lem)
qed

lemma renaming_var_to_var: "renaming \<rho> V \<Longrightarrow> x \<in> V \<Longrightarrow> \<exists>y. Var x \<lhd> \<rho> = Var y"
  unfolding renaming_def
  by (meson is_a_variable.elims(2))

lemma
  assumes
    H: "\<And>\<rho> \<rho>_inv \<mu> :: 'a subst. \<And> (V :: 'a set). \<And> t u :: 'a trm.
      renaming \<rho> V \<Longrightarrow>
      vars_of t \<union> vars_of u \<subseteq> V \<Longrightarrow>
      \<forall>x \<in> V. Var x \<lhd> \<rho> \<lhd> \<rho>_inv = Var x \<Longrightarrow>
      \<forall>x. x \<notin> subst_codomain \<rho> V \<longrightarrow> Var x \<lhd> \<rho>_inv = Var x \<Longrightarrow>
      MGU \<mu> t u \<Longrightarrow>
      MGU (\<rho>_inv \<lozenge> \<mu>) (t \<lhd> \<rho>) (u \<lhd> \<rho>)" and
      "distinct [x :: 'a, x', y, y']"
  shows False
proof -
  define \<rho> where
    "\<rho> = [(x, Var x'), (y, Var y')]"

  have "renaming \<rho> {x, y}"
    unfolding renaming_def
    using assms(2) by (auto simp: \<rho>_def)

  have "vars_of (Var x) \<union> vars_of (Var y) \<subseteq> {x, y}"
    by simp

  obtain \<rho>_inv where
    "\<forall>x\<in>{x, y}. Var x \<lhd> \<rho> \<lhd> \<rho>_inv = Var x" and
    "\<forall>xa. xa \<notin> subst_codomain \<rho> {x, y} \<longrightarrow> Var xa \<lhd> \<rho>_inv = Var xa"
    using renamings_admit_inverse[OF _ \<open>renaming \<rho> {x, y}\<close>]
    by auto

  define \<mu> where
    "\<mu> = [(x, Var y)]"

  have "MGU \<mu> (Var x) (Var y)"
    by (simp add: MGU_Var \<mu>_def)

  have "MGU (\<rho>_inv \<lozenge> \<mu>) (Var x \<lhd> \<rho>) (Var y \<lhd> \<rho>)"
    using H[OF \<open>renaming \<rho> {x, y}\<close> \<open>vars_of (Var x) \<union> vars_of (Var y) \<subseteq> {x, y}\<close>
        \<open>\<forall>x\<in>{x, y}. Var x \<lhd> \<rho> \<lhd> \<rho>_inv = Var x\<close>
        \<open>\<forall>xa. xa \<notin> subst_codomain \<rho> {x, y} \<longrightarrow> Var xa \<lhd> \<rho>_inv = Var xa\<close>
        \<open>MGU \<mu> (Var x) (Var y)\<close>]
    by assumption

  hence "Unifier (\<rho>_inv \<lozenge> \<mu>) (Var x \<lhd> \<rho>) (Var y \<lhd> \<rho>)" and
    most_general: "\<forall>\<theta>. Unifier \<theta> (Var x \<lhd> \<rho>) (Var y \<lhd> \<rho>) \<longrightarrow> (\<exists>\<gamma>. \<theta> \<doteq> (\<rho>_inv \<lozenge> \<mu>) \<lozenge> \<gamma>)"
    unfolding MGU_def
    by auto

  define \<theta> where
    "\<theta> = [(x', Var y')]"

  have "Unifier \<theta> (Var x \<lhd> \<rho>) (Var y \<lhd> \<rho>)"
    by (metis MGU_Var MGU_is_Unifier \<rho>_def \<theta>_def assms(2) assoc.simps(2) distinct_length_2_or_more
        occs.simps(1) subst.simps(1))

  then obtain \<gamma> where "\<theta> \<doteq> (\<rho>_inv \<lozenge> \<mu>) \<lozenge> \<gamma>"
    using most_general by auto

  hence "\<forall>t. t \<lhd> \<theta> = t \<lhd> \<rho>_inv \<lhd> \<mu> \<lhd> \<gamma>"
    by (simp add: comp_subst_terms)

  have "Var x = Var y \<lhd> \<gamma>"
  proof -
    have "Var x \<lhd> \<theta> = Var x \<lhd> \<rho>_inv \<lhd> \<mu> \<lhd> \<gamma>"
      using \<open>\<forall>t. t \<lhd> \<theta> = t \<lhd> \<rho>_inv \<lhd> \<mu> \<lhd> \<gamma>\<close> by simp

    hence "Var x = Var x \<lhd> \<rho>_inv \<lhd> \<mu> \<lhd> \<gamma>"
      using \<theta>_def assms(2) by force
  
    moreover have "Var x \<lhd> \<rho>_inv = Var x"
      apply (rule \<open>\<forall>xa. xa \<notin> subst_codomain \<rho> {x, y} \<longrightarrow> Var xa \<lhd> \<rho>_inv = Var xa\<close>[rule_format])
      unfolding \<rho>_def subst_codomain_def
      using assms(2) by auto

    ultimately have "Var x = Var x \<lhd> \<mu> \<lhd> \<gamma>"
      by simp

    thus "Var x = Var y \<lhd> \<gamma>"
      unfolding \<mu>_def by simp
  qed

  moreover have "Var y' = Var y \<lhd> \<gamma>"
  proof -
    have "Var x' \<lhd> \<theta> = Var x' \<lhd> \<rho>_inv \<lhd> \<mu> \<lhd> \<gamma>"
      using \<open>\<forall>t. t \<lhd> \<theta> = t \<lhd> \<rho>_inv \<lhd> \<mu> \<lhd> \<gamma>\<close> by simp

    hence "Var y' = Var x' \<lhd> \<rho>_inv \<lhd> \<mu> \<lhd> \<gamma>"
      using \<theta>_def assms(2) by force
  
    moreover have "Var x' \<lhd> \<rho>_inv = Var x"
      using \<open>\<forall>x\<in>{x, y}. Var x \<lhd> \<rho> \<lhd> \<rho>_inv = Var x\<close> \<rho>_def by fastforce

    ultimately have "Var y' = Var x \<lhd> \<mu> \<lhd> \<gamma>"
      by simp

    thus "Var y' = Var y \<lhd> \<gamma>"
      unfolding \<mu>_def by simp
  qed

  moreover have "x \<noteq> y'"
    using assms(2) by force

  ultimately show False
    by (metis trm.inject(1))
qed

primrec the_Var where
  "the_Var (Var x) = x"

definition subst_domain where
  "subst_domain \<sigma> = {x. Var x \<lhd> \<sigma> \<noteq> Var x}"

lemma assoc_ident_if_not_in_dom': "x \<notin> subst_domain \<sigma> \<Longrightarrow> Var x \<lhd> \<sigma> = Var x"
  by (simp add: subst_domain_def)

lemma map_of_map_map_prod_eq_SomeD:
  assumes "map_of (map (map_prod f g) xs) k = Some v"
  shows "\<exists>k' v'. f k' = k \<and> g v' = v \<and> map_of xs k' = Some v'"
  using assms
proof (induction xs)
  case Nil
  thus ?case by simp
next
  case (Cons x xs)
  thus ?case
    by (cases "k = f (fst x)"; force)
qed

lemma map_of_map_map_prod_eq_Some_if:
  assumes inj_f: "inj_on f (dom (map_of xs))" and
    f_k'_eq: "f k' = k" and g_v'_eq: "g v' = v" and xs_k'_eq: "map_of xs k' = Some v'"
  shows "map_of (map (map_prod f g) xs) k = Some v"
  using inj_f xs_k'_eq
proof (induction xs)
  case Nil
  thus ?case by simp
next
  case (Cons x xs)

  have dom_xs_subset: "dom (map_of xs) \<subseteq> dom (map_of (x # xs))"
    by auto
  with Cons.prems(1) have "inj_on f (dom (map_of xs))"
    by (rule inj_on_subset)

  show ?case
  proof (cases "k = f (fst x)")
    case True
    with Cons.prems have "k' = fst x \<and> v' = snd x"
      unfolding f_k'_eq[symmetric]
      by (metis domI inj_onD map_of_Cons_code(2) option.inject prod.exhaust_sel)
    with True g_v'_eq show ?thesis
      by simp
  next
    case False
    with Cons.prems(2) f_k'_eq have "map_of xs k' = Some v'"
      by (metis map_of_Cons_code(2) prod.collapse)
    with \<open>inj_on f (dom (map_of xs))\<close> have "map_of (map (map_prod f g) xs) k = Some v"
      by (rule Cons.IH)
    with False show ?thesis
      by auto
  qed
qed

lemma map_of_map_map_prod_eq_None_if:
  assumes inj_f: "inj_on f V" and
    "dom (map_of xs) \<subseteq> V" and "k \<in> V"
    "map_of xs k = None"
  shows "map_of (map (map_prod f g) xs) (f k) = None"
  using assms(2-)
proof (induction xs)
  case Nil
  thus ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases "k = (fst x)")
    case True
    with Cons.prems have False by simp
    thus ?thesis ..
  next
    case False
    moreover have "f k \<noteq> f (fst x)"
      using inj_f \<open>k \<in> V\<close>
      by (metis Cons.prems(1) calculation domI fun_upd_same inj_onD map_of.simps(2) subset_iff)
    ultimately show ?thesis
      apply simp
      using Cons.IH
      using Cons.prems(1) Cons.prems(3) assms(3) by force
  qed
qed

lemma not_in_dom_map_map_prod_if:
  assumes inj_f: "inj_on f (insert x (fst ` set \<sigma>))"
  shows "x \<notin> fst ` set \<sigma> \<Longrightarrow> f x \<notin> fst ` set (map (map_prod f g) \<sigma>)"
  by (metis inj_f dom_map_of_conv_image_fst insertI1 map_of_eq_None_iff
      map_of_map_map_prod_eq_None_if subset_insertI)

lemma subst_Var_renaming_map_map_prod_eq:
  assumes
    all_vars_\<rho>: "\<forall>x \<in> insert x (fst ` set \<sigma>). is_a_variable (Var x \<lhd> \<rho>)" and
    inj_subst_\<rho>: "inj_on (\<lambda>x. Var x \<lhd> \<rho>) (insert x (fst ` set \<sigma>))"
  shows "Var x \<lhd> \<rho> \<lhd> map (map_prod (\<lambda>x. the_Var (Var x \<lhd> \<rho>)) (\<lambda>v. v \<lhd> \<rho>)) \<sigma> =
    Var x \<lhd> \<sigma> \<lhd> \<rho>"
proof (cases "x \<in> fst ` set \<sigma>")
  case True

  from inj_subst_\<rho> have inj_subst_\<rho>': "inj_on (\<lambda>x. the_Var (Var x \<lhd> \<rho>)) ((insert x (fst ` set \<sigma>)))"
    by (smt (verit, best) all_vars_\<rho> inj_onD inj_onI is_a_variable.elims(2) the_Var.simps)

  have dom_\<sigma>: "dom (map_of \<sigma>) \<subseteq> insert x (fst ` set \<sigma>)"
    by (simp add: dom_map_of_conv_image_fst subset_insertI)

  obtain x' where x_\<rho>: "Var x \<lhd> \<rho> = Var x'"
    using all_vars_\<rho> is_a_variable.elims(2) by blast
  hence x_\<rho>': "the_Var (Var x \<lhd> \<rho>) = x'"
    by simp

  from True obtain v' where "map_of \<sigma> x = Some v'"
    by (metis domD dom_map_of_conv_image_fst)

  have *: "map_of (map (map_prod (\<lambda>x. the_Var (Var x \<lhd> \<rho>)) (\<lambda>v. v \<lhd> \<rho>)) \<sigma>) x' = Some (v' \<lhd> \<rho>)"
  proof (rule map_of_map_map_prod_eq_Some_if)
    show "inj_on (\<lambda>x. the_Var (Var x \<lhd> \<rho>)) (dom (map_of \<sigma>))"
      by (metis True dom_map_of_conv_image_fst inj_subst_\<rho>' insert_absorb)
  next
    show "the_Var (Var x \<lhd> \<rho>) = x'"
      by (rule x_\<rho>')
  next
    show "v' \<lhd> \<rho> = v' \<lhd> \<rho>"
      by simp
  next
    show "map_of \<sigma> x = Some v'"
      by (rule \<open>map_of \<sigma> x = Some v'\<close>)
  qed

  have "Var x \<lhd> \<rho> \<lhd> map (map_prod (\<lambda>x. the_Var (Var x \<lhd> \<rho>)) (\<lambda>v. v \<lhd> \<rho>)) \<sigma> =
    Var x' \<lhd> map (map_prod (\<lambda>x. the_Var (Var x \<lhd> \<rho>)) (\<lambda>v. v \<lhd> \<rho>)) \<sigma>"
    unfolding x_\<rho> by simp
  also have "... = (case map_of (map (map_prod (\<lambda>x. the_Var (Var x \<lhd> \<rho>)) (\<lambda>v. v \<lhd> \<rho>)) \<sigma>) x' of
    None \<Rightarrow> Var x' | Some z \<Rightarrow> z)"
    unfolding subst_Var_eq_map_of_or_default[of x'] by simp
  also have "... = v' \<lhd> \<rho>"
    unfolding * by simp
  also have "... = Var x \<lhd> \<sigma> \<lhd> \<rho>"
    unfolding subst_Var_eq_map_of_or_default[of x] \<open>map_of \<sigma> x = Some v'\<close> option.case by simp
  finally show ?thesis
    by assumption
next
  case False

  from inj_subst_\<rho> have inj_subst_\<rho>': "inj_on (\<lambda>x. the_Var (Var x \<lhd> \<rho>)) ((insert x (fst ` set \<sigma>)))"
    by (smt (verit, best) all_vars_\<rho> inj_onD inj_onI is_a_variable.elims(2) the_Var.simps)

  obtain x' where x_\<rho>: "Var x \<lhd> \<rho> = Var x'"
    using all_vars_\<rho> is_a_variable.elims(2) by blast

  show ?thesis
    unfolding subst_Var_ident_if_not_in_dom[OF False]
    unfolding x_\<rho>
    unfolding not_in_dom_map_map_prod_if[OF inj_subst_\<rho>' False,
        THEN subst_Var_ident_if_not_in_dom, unfolded x_\<rho> the_Var.simps]
    by (rule refl)
qed

lemma subst_renaming_map_map_prod_eq:
  assumes
    all_vars_\<rho>: "\<forall>x \<in> vars_of t \<union> fst ` set \<sigma>. is_a_variable (Var x \<lhd> \<rho>)" and
    inj_subst_\<rho>: "inj_on (\<lambda>x. Var x \<lhd> \<rho>) (vars_of t \<union> fst ` set \<sigma>)"
  defines "\<sigma>' \<equiv> map (map_prod (\<lambda>x. the_Var (Var x \<lhd> \<rho>)) (\<lambda>v. v \<lhd> \<rho>)) \<sigma>"
  shows "t \<lhd> \<rho> \<lhd> \<sigma>' = t \<lhd> \<sigma> \<lhd> \<rho>"
  unfolding Unification.agreement[of t "_ \<lozenge> _" "_ \<lozenge> _", unfolded subst_comp]
proof (rule ballI)
  fix x assume x_in: "x \<in> vars_of t"
  show "Var x \<lhd> \<rho> \<lhd> \<sigma>' = Var x \<lhd> \<sigma> \<lhd> \<rho>"
  proof (rule subst_Var_renaming_map_map_prod_eq[of x \<sigma> \<rho>, folded \<sigma>'_def])
    show "\<forall>x\<in>insert x (fst ` set \<sigma>). is_a_variable (Var x \<lhd> \<rho>)"
      using all_vars_\<rho> x_in by auto
  next
    show "inj_on (\<lambda>x. Var x \<lhd> \<rho>) (insert x (fst ` set \<sigma>))"
      by (metis (no_types, lifting) UnI1 inj_subst_\<rho> insert_subset subset_inj_on sup_ge2 x_in)
  qed
qed

lemma subst_equation_renaming_map_map_prod_eq:
  assumes
    all_vars_\<rho>: "\<forall>x \<in> vars_of_eq e \<union> fst ` set \<sigma>. is_a_variable (Var x \<lhd> \<rho>)" and
    inj_subst_\<rho>: "inj_on (\<lambda>x. Var x \<lhd> \<rho>) (vars_of_eq e \<union> fst ` set \<sigma>)"
  defines "\<sigma>' \<equiv> map (map_prod (\<lambda>x. the_Var (Var x \<lhd> \<rho>)) (\<lambda>v. v \<lhd> \<rho>)) \<sigma>"
  shows "subst_equation (subst_equation e \<rho>) \<sigma>' = subst_equation (subst_equation e \<sigma>) \<rho>"
proof (cases e)
  case (Eq t u)
  
  moreover have "t \<lhd> \<rho> \<lhd> \<sigma>' = t \<lhd> \<sigma> \<lhd> \<rho>"
    apply (rule subst_renaming_map_map_prod_eq[of t \<sigma> \<rho>, folded \<sigma>'_def])
    using all_vars_\<rho> inj_subst_\<rho> by (auto simp: Eq intro: inj_on_subset)
  
  moreover have "u \<lhd> \<rho> \<lhd> \<sigma>' = u \<lhd> \<sigma> \<lhd> \<rho>"
    apply (rule subst_renaming_map_map_prod_eq[of u \<sigma> \<rho>, folded \<sigma>'_def])
    using all_vars_\<rho> inj_subst_\<rho> by (auto simp: Eq intro: inj_on_subset)

  ultimately show ?thesis
    by simp
qed


lemma subst_lit_renaming_map_map_prod_eq:
  assumes
    all_vars_\<rho>: "\<forall>x \<in> vars_of_lit L \<union> fst ` set \<sigma>. is_a_variable (Var x \<lhd> \<rho>)" and
    inj_subst_\<rho>: "inj_on (\<lambda>x. Var x \<lhd> \<rho>) (vars_of_lit L \<union> fst ` set \<sigma>)"
  defines "\<sigma>' \<equiv> map (map_prod (\<lambda>x. the_Var (Var x \<lhd> \<rho>)) (\<lambda>v. v \<lhd> \<rho>)) \<sigma>"
  shows "equational_clausal_logic.subst_lit (equational_clausal_logic.subst_lit L \<rho>) \<sigma>' =
         equational_clausal_logic.subst_lit (equational_clausal_logic.subst_lit L \<sigma>) \<rho>"
  apply (cases L)
  apply simp
  using subst_equation_renaming_map_map_prod_eq[of _ \<sigma> \<rho>, folded \<sigma>'_def]
  apply (metis all_vars_\<rho> inj_subst_\<rho> vars_of_lit.simps(1))
  using subst_equation_renaming_map_map_prod_eq[of _ \<sigma> \<rho>, folded \<sigma>'_def]
  by (metis all_vars_\<rho> inj_subst_\<rho> subst_lit.simps(2) vars_of_lit.simps(2))

lemma subst_cl_renaming_map_map_prod_eq:
  assumes
    all_vars_\<rho>: "\<forall>x \<in> vars_of_cl C \<union> fst ` set \<sigma>. is_a_variable (Var x \<lhd> \<rho>)" and
    inj_subst_\<rho>: "inj_on (\<lambda>x. Var x \<lhd> \<rho>) (vars_of_cl C \<union> fst ` set \<sigma>)"
  defines "\<sigma>' \<equiv> map (map_prod (\<lambda>x. the_Var (Var x \<lhd> \<rho>)) (\<lambda>v. v \<lhd> \<rho>)) \<sigma>"
  shows "subst_cl (subst_cl C \<rho>) \<sigma>' = subst_cl (subst_cl C \<sigma>) \<rho>"
proof (rule Set.equalityI; rule Set.subsetI)
  fix L assume "L \<in> subst_cl (subst_cl C \<rho>) \<sigma>'"
  then obtain L' where
    "L' \<in> C" and
    L_eq: "L = equational_clausal_logic.subst_lit (equational_clausal_logic.subst_lit L' \<rho>) \<sigma>'"
    by (metis (no_types, lifting) image_iff subst_cl_conv)
  hence "L = equational_clausal_logic.subst_lit (equational_clausal_logic.subst_lit L' \<sigma>) \<rho>"
    using all_vars_\<rho> inj_subst_\<rho> subst_lit_renaming_map_map_prod_eq[of L' \<sigma> \<rho>, folded \<sigma>'_def]
    by (smt (verit, best) Un_iff inj_on_subset subset_eq vars_of_cl_lem)
  then show "L \<in> subst_cl (subst_cl C \<sigma>) \<rho>"
    by (simp add: \<open>L' \<in> C\<close> subst_cl_conv)
next
  fix L assume "L \<in> subst_cl (subst_cl C \<sigma>) \<rho>"
  then obtain L' where
    "L' \<in> C" and
    L_eq: "L = equational_clausal_logic.subst_lit (equational_clausal_logic.subst_lit L' \<sigma>) \<rho>"
    by (metis (no_types, lifting) image_iff subst_cl_conv)
  hence "L = equational_clausal_logic.subst_lit (equational_clausal_logic.subst_lit L' \<rho>) \<sigma>'"
    using all_vars_\<rho> inj_subst_\<rho> subst_lit_renaming_map_map_prod_eq[of L' \<sigma> \<rho>, folded \<sigma>'_def]
    by (smt (verit, best) Un_iff inj_on_subset subset_eq vars_of_cl_lem)
  then show "L \<in> subst_cl (subst_cl C \<rho>) \<sigma>'"
    by (simp add: \<open>L' \<in> C\<close> subst_cl_conv)
qed

lemma inj_on_if_renaming: "renaming \<rho> V \<Longrightarrow> inj_on (\<lambda>x. Var x \<lhd> \<rho>)  V"
  unfolding renaming_def by (meson inj_onI)

lemma Unifier_of_renamed_if_Unifier:
  assumes
    ren_\<rho>: "renaming \<rho> V" and
    vars_t_u_subset: "vars_of t \<union> vars_of u \<subseteq> V" and
    dom_\<mu>: "fst `set \<mu> \<subseteq> V" and
    unif_\<mu>: "Unifier \<mu> t u"
  defines "\<mu>' \<equiv> map (map_prod (\<lambda>x. the_Var (Var x \<lhd> \<rho>)) (\<lambda>v. v \<lhd> \<rho>)) \<mu>"
  shows "Unifier \<mu>' (t \<lhd> \<rho>) (u \<lhd> \<rho>)"
proof -
  from ren_\<rho> have all_var_\<rho>: "\<forall>x \<in> V. is_a_variable (Var x \<lhd> \<rho>)"
    by (simp add: renaming_def)

  from ren_\<rho> have inj_\<rho>: "inj_on (\<lambda>x. Var x \<lhd> \<rho>) V"
    by (rule inj_on_if_renaming)
  hence inj_\<rho>': "inj_on (\<lambda>x. the_Var (Var x \<lhd> \<rho>)) V"
    by (smt (verit, best) inj_onI ren_\<rho> renaming_def renaming_var_to_var the_Var.simps)

  from dom_\<mu> have dom_\<mu>': "dom (map_of \<mu>) \<subseteq> V"
    by (metis dom_map_of_conv_image_fst)

  have *: "t \<lhd> \<rho> \<lhd> \<mu>' = t \<lhd> \<mu> \<lhd> \<rho>" if "vars_of t \<subseteq> V" for t
  proof (rule subst_renaming_map_map_prod_eq[of t \<mu> \<rho>, folded \<mu>'_def])
    show "\<forall>x\<in>vars_of t \<union> fst ` set \<mu>. is_a_variable (Var x \<lhd> \<rho>)"
      using all_var_\<rho> dom_\<mu> that by auto
  next
    show "inj_on (\<lambda>x. Var x \<lhd> \<rho>) (vars_of t \<union> fst ` set \<mu>)"
      by (metis dom_\<mu> inj_\<rho> subset_inj_on sup.bounded_iff that)
  qed

  show "Unifier \<mu>' (t \<lhd> \<rho>) (u \<lhd> \<rho>)"
    using unif_\<mu> vars_t_u_subset
    by (simp add: Unifier_def *)
qed

lemma dom_of_subst_adapted_to_renaming:
  assumes
    ren_\<rho>: "renaming \<rho> V" and
    dom_\<sigma>: "fst `set \<sigma> \<subseteq> V"
  defines "\<sigma>' \<equiv> map (map_prod (\<lambda>x. the_Var (Var x \<lhd> \<rho>)) (\<lambda>v. v \<lhd> \<rho>)) \<sigma>"
  shows "fst `set \<sigma>' \<subseteq> (\<lambda>x. the_Var (Var x \<lhd> \<rho>)) ` fst `set \<sigma>"
proof (rule Set.subsetI)
  fix x assume "x \<in> fst ` set \<sigma>'"
  then obtain prod where prod_in: "prod \<in> set \<sigma>" and x_def: "x = the_Var (Var (fst prod) \<lhd> \<rho>)"
    unfolding \<sigma>'_def list.set_map Set.image_iff Set.bex_simps fst_map_prod
    by auto
  thus "x \<in> (\<lambda>x. the_Var (Var x \<lhd> \<rho>)) ` fst ` set \<sigma>"
    using renaming_var_to_var[OF ren_\<rho>] by blast
qed

lemma vars_of_subst_subset_if_range_vars_subset:
  "range_vars \<sigma> \<subseteq> V \<Longrightarrow> Var y \<lhd> \<sigma> \<noteq> Var y \<Longrightarrow> vars_of (Var y \<lhd> \<sigma>) \<subseteq> V"
  using range_vars_def by fastforce

lemma range_vars_of_subst_adapted_to_renaming:
  assumes
    ren_\<rho>: "renaming \<rho> V" and
    dom_\<sigma>: "fst `set \<sigma> \<subseteq> V" and
    range_vars_\<sigma>: "range_vars \<sigma> \<subseteq> V"
  defines "\<sigma>' \<equiv> map (map_prod (\<lambda>x. the_Var (Var x \<lhd> \<rho>)) (\<lambda>v. v \<lhd> \<rho>)) \<sigma>"
  shows "range_vars \<sigma>' \<subseteq> (\<lambda>x. the_Var (Var x \<lhd> \<rho>)) ` range_vars \<sigma>"
proof (rule Set.subsetI)
  fix x assume "x \<in> range_vars \<sigma>'"
  then obtain y' where x_in: "x \<in> vars_of (Var y' \<lhd> \<sigma>')" and y'_\<sigma>': "Var y' \<lhd> \<sigma>' \<noteq> Var y'"
    by (auto simp: range_vars_def)

  from y'_\<sigma>' have x'_in: "y' \<in> fst `set \<sigma>'"
    by (meson subst_Var_ident_if_not_in_dom)
  with y'_\<sigma>' obtain y where y_\<rho>: "Var y \<lhd> \<rho> = Var y'" and y_in: "y \<in> V"
    unfolding \<sigma>'_def
    unfolding image_set
    apply simp
    using dom_\<sigma> ren_\<rho> renaming_var_to_var by fastforce

  have "Var y \<lhd> \<rho> \<lhd> \<sigma>' = Var y \<lhd> \<sigma> \<lhd> \<rho>"
  proof (rule subst_Var_renaming_map_map_prod_eq[of y \<sigma> \<rho>, folded \<sigma>'_def])
    from ren_\<rho> have "\<forall>x\<in>V. is_a_variable (Var x \<lhd> \<rho>)"
      using renaming_def by fast
    thus "\<forall>x\<in>insert y (fst ` set \<sigma>). is_a_variable (Var x \<lhd> \<rho>)"
      using dom_\<sigma> y_in by blast
  next
    from ren_\<rho> have "inj_on (\<lambda>x. Var x \<lhd> \<rho>) V"
      using inj_on_if_renaming by blast
    thus "inj_on (\<lambda>x. Var x \<lhd> \<rho>) (insert y (fst ` set \<sigma>))"
      by (meson dom_\<sigma> insert_subset subset_inj_on y_in)
  qed
  with y'_\<sigma>' y_\<rho> have y_\<sigma>_not_ident: "Var y \<lhd> \<sigma> \<noteq> Var y"
    by force
  hence vars_of_y_\<sigma>: "vars_of (Var y \<lhd> \<sigma>) \<subseteq> V"
    by (rule vars_of_subst_subset_if_range_vars_subset[OF range_vars_\<sigma>])

  from x_in y_\<rho> have "x \<in> vars_of (Var y \<lhd> \<sigma> \<lhd> \<rho>)"
    using \<open>Var y \<lhd> \<rho> \<lhd> \<sigma>' = Var y \<lhd> \<sigma> \<lhd> \<rho>\<close> by force
  hence "x \<in> (\<Union>x \<in> vars_of (Var y \<lhd> \<sigma>). vars_of (Var x \<lhd> \<rho>))"
    using vars_of_instances by fastforce
  hence "x \<in> (\<Union>x \<in> vars_of (Var y \<lhd> \<sigma>). {the_Var (Var x \<lhd> \<rho>)})"
    using range_vars_\<sigma>[unfolded range_vars_def]
    using y'_\<sigma>'[unfolded y_\<rho>[symmetric]]
    using vars_of_y_\<sigma> ren_\<rho>
    by (smt (verit, ccfv_SIG) UN_iff is_a_variable.elims(2) renaming_def subset_iff the_Var.simps
        vars_of.simps(1))
  hence "x \<in> (\<lambda>x. the_Var (Var x \<lhd> \<rho>)) ` vars_of (Var y \<lhd> \<sigma>)"
    by blast
  then show "x \<in> (\<lambda>x. the_Var (Var x \<lhd> \<rho>)) ` range_vars \<sigma>"
    unfolding range_vars_def
    using y_\<sigma>_not_ident by blast
qed


lemma IMGU_of_renamed_if_IMGU:
  assumes
    ren_\<rho>: "renaming \<rho> V" and
    \<rho>_\<rho>_inv_ident: "\<forall>x \<in> V. Var x \<lhd> \<rho> \<lhd> \<rho>_inv = Var x" and
    vars_t_u_subset: "vars_of t \<union> vars_of u \<subseteq> V" and
    dom_\<mu>: "fst `set \<mu> \<subseteq> V" and
    mgu_\<mu>: "IMGU \<mu> t u"
  defines "\<mu>' \<equiv> map (map_prod (\<lambda>x. the_Var (Var x \<lhd> \<rho>)) (\<lambda>v. v \<lhd> \<rho>)) \<mu>"
  shows "IMGU \<mu>' (t \<lhd> \<rho>) (u \<lhd> \<rho>)"
  unfolding IMGU_def
proof (intro conjI allI impI)
  from mgu_\<mu> show "Unifier \<mu>' (t \<lhd> \<rho>) (u \<lhd> \<rho>)"
    unfolding IMGU_def \<mu>'_def
    using Unifier_of_renamed_if_Unifier[OF ren_\<rho> vars_t_u_subset dom_\<mu>]
    by simp
next
  fix \<upsilon> assume "Unifier \<upsilon> (t \<lhd> \<rho>) (u \<lhd> \<rho>)"
  hence unif_\<rho>_\<upsilon>: "Unifier (\<rho> \<lozenge> \<upsilon>) t u"
    by (simp add: Unifier_def)
  then obtain \<gamma> where **: "\<rho> \<lozenge> \<upsilon> \<doteq> \<mu> \<lozenge> \<gamma>"
    using mgu_\<mu> by (auto simp: IMGU_def)
  hence *: "\<forall>v. Var v \<lhd> \<rho> \<lhd> \<upsilon> = Var v \<lhd> \<mu> \<lhd> \<gamma>"
    by (metis comp_subst_terms subst_comp)

  from mgu_\<mu> have BAR: "\<rho> \<lozenge> \<upsilon> \<doteq> \<mu> \<lozenge> \<rho> \<lozenge> \<upsilon>"
    using unif_\<rho>_\<upsilon> IMGU_def by fastforce
  hence FOO: "\<forall>v. Var v \<lhd> \<rho> \<lhd> \<upsilon> = Var v \<lhd> \<mu> \<lhd> \<rho> \<lhd> \<upsilon>"
    by (metis subst_comp subst_eq_dest)

  have "\<forall>v. Var v \<lhd> \<upsilon> = Var v \<lhd> \<mu>' \<lhd> \<upsilon>"
  proof (rule allI)
    fix x
    show "Var x \<lhd> \<upsilon> = Var x \<lhd> \<mu>' \<lhd> \<upsilon>"
    proof (cases "x \<in> subst_domain \<mu>'")
      case True
      then obtain v where "map_of \<mu>' x = Some v" and "v \<noteq> Var x"
        unfolding subst_domain_def mem_Collect_eq
        apply (simp add: assoc_eq_map_of_or_default)
        by (metis option.case_eq_if option.collapse)
      then obtain x' v' where
        the_Var_x'_\<rho>: "the_Var (Var x' \<lhd> \<rho>) = x" and "v' \<lhd> \<rho> = v" and "map_of \<mu> x' = Some v'"
        unfolding \<mu>'_def
        using map_of_map_map_prod_eq_SomeD
        by fastforce
      
      from \<open>map_of \<mu> x' = Some v'\<close> have "x' \<in> V"
        by (metis dom_\<mu> map_of_eq_None_iff option.simps(3) subset_iff)
      with ren_\<rho> the_Var_x'_\<rho> have x'_\<rho>: "Var x' \<lhd> \<rho> = Var x"
        using renaming_var_to_var by fastforce

      from \<open>x' \<in> V\<close> True have x_\<mu>': "Var x \<lhd> \<mu>' = Var x \<lhd> \<rho>_inv \<lhd> \<mu> \<lhd> \<rho>"
        by (metis \<open>map_of \<mu> x' = Some v'\<close> \<open>map_of \<mu>' x = Some v\<close> \<open>v' \<lhd> \<rho> = v\<close> \<rho>_\<rho>_inv_ident
            assoc.simps(2) assoc_eq_map_of_or_default map_of_Cons_code(2) subst.simps(1) x'_\<rho>)

      have "Var x \<lhd> \<mu>' \<lhd> \<upsilon> = Var x \<lhd> \<rho>_inv \<lhd> \<mu> \<lhd> \<rho> \<lhd> \<upsilon>" using x_\<mu>' by simp
      also have "... = Var x' \<lhd> \<rho> \<lhd> \<rho>_inv \<lhd> \<mu> \<lhd> \<rho> \<lhd> \<upsilon>" using x'_\<rho> by simp
      also have "... = Var x' \<lhd> \<mu> \<lhd> \<rho> \<lhd> \<upsilon>" using \<rho>_\<rho>_inv_ident \<open>x' \<in> V\<close> by simp
      also have "... = Var x' \<lhd> \<rho> \<lhd> \<upsilon>" using FOO by simp
      also have "... = Var x \<lhd> \<upsilon>" using x'_\<rho> by simp
      finally show ?thesis by simp
    next
      case False
      then show ?thesis
        using assoc_ident_if_not_in_dom' by metis
    qed
  qed
  thus "\<upsilon> \<doteq> \<mu>' \<lozenge> \<upsilon>"
    by (metis agreement subst_comp subst_eq_def)
qed

lemma ex_MGU_if_Unifier:
  assumes "Unifier \<upsilon> t u"
  shows "\<exists>\<mu>. MGU \<mu> t u"
proof -
  from \<open>Unifier \<upsilon> t u\<close> obtain \<mu> where "unify t u = Some \<mu>"
    using MGU_exists[rule_format, of t \<upsilon> u] Unifier_def by blast
  thus ?thesis
    using unify_computes_MGU by auto
qed

lemma Idem_of_subst_adapted_to_renaming:
  assumes
    ren_\<rho>: "renaming \<rho> V" and
    \<rho>_\<rho>_inv_ident: "\<forall>x\<in>V. Var x \<lhd> \<rho> \<lhd> \<rho>_inv = Var x" and
    dom_\<sigma>: "fst ` set \<sigma> \<subseteq> V" and
    range_vars_\<sigma>: "range_vars \<sigma> \<subseteq> V" and
    "Idem \<sigma>"
  defines "\<sigma>' \<equiv> map (map_prod (\<lambda>x. the_Var (Var x \<lhd> \<rho>)) (\<lambda>v. v \<lhd> \<rho>)) \<sigma>"
  shows "Idem \<sigma>'"
  unfolding Idem_def
proof (rule subst_eq_intro, rule Unification.agreement[THEN iffD2], rule ballI)
  fix x'
  show "Var x' \<lhd> \<sigma>' \<lozenge> \<sigma>' = Var x' \<lhd> \<sigma>'"
  proof (cases "x' \<in> fst ` set \<sigma>'")
    case True
    then obtain x where x_\<rho>: "Var x \<lhd> \<rho> = Var x'" and x_in: "x \<in> fst ` set \<sigma>"
      unfolding \<sigma>'_def
      using dom_\<sigma> renaming_var_to_var[OF ren_\<rho>]
      by (smt (verit, ccfv_SIG) fst_map_prod image_iff image_subset_iff list.set_map the_Var.simps)

    from ren_\<rho> dom_\<sigma> have inj_\<rho>: "inj_on (\<lambda>x. Var x \<lhd> \<rho>) (fst ` set \<sigma>)"
      by (meson inj_onI renaming_imp_ball_neq_imp_neq_subst subset_eq)
    with x_in have inj_\<rho>':  "inj_on (\<lambda>x. Var x \<lhd> \<rho>) (insert x (fst ` set \<sigma>))"
      by (metis insert_absorb)

    from ren_\<rho> dom_\<sigma> have ball_is_var_\<rho>: "\<forall>x\<in>fst ` set \<sigma>. is_a_variable (Var x \<lhd> \<rho>)"
      using renaming_imp_ball_var by auto
    with x_in have ball_is_var_\<rho>':"\<forall>x\<in>insert x (fst ` set \<sigma>). is_a_variable (Var x \<lhd> \<rho>)"
      by (metis insert_absorb)

    from x_\<rho> have "Var x' \<lhd> \<sigma>' \<lozenge> \<sigma>' = Var x \<lhd> \<rho> \<lhd> \<sigma>' \<lhd> \<sigma>'"
      by simp
    also have "... = Var x \<lhd> \<sigma> \<lhd> \<rho> \<lhd> \<sigma>'"
      using subst_Var_renaming_map_map_prod_eq[OF ball_is_var_\<rho>' inj_\<rho>', folded \<sigma>'_def] by simp
    also have "... = Var x \<lhd> \<sigma> \<lhd> \<sigma> \<lhd> \<rho>"
    proof (rule subst_renaming_map_map_prod_eq[of _ \<sigma> \<rho>, folded \<sigma>'_def])
      show "\<forall>x\<in>vars_of (Var x \<lhd> \<sigma>) \<union> fst ` set \<sigma>. is_a_variable (Var x \<lhd> \<rho>)"
        using ball_is_var_\<rho> x_in
        by (metis (no_types, lifting) Un_iff insert_absorb insert_is_Un range_vars_\<sigma> ren_\<rho>
            renaming_imp_ball_var subsetD vars_of.simps(1) vars_of_subst_subset_if_range_vars_subset)
    next
      show "inj_on (\<lambda>x. Var x \<lhd> \<rho>) (vars_of (Var x \<lhd> \<sigma>) \<union> fst ` set \<sigma>)"
        using inj_\<rho> dom_\<sigma> range_vars_\<sigma> x_in
        by (smt (verit, ccfv_SIG) \<rho>_\<rho>_inv_ident inj_on_def insert_absorb insert_def singleton_conv
            subsetD subset_eq sup.absorb_iff1 sup.order_iff sup_left_commute trm.inject(1)
            vars_of.simps(1) vars_of_subst_subset_if_range_vars_subset)
    qed
    also have "... = Var x \<lhd> \<sigma> \<lhd> \<rho>"
      using \<open>Idem \<sigma>\<close> by (smt (verit, best) Idem_def subst_comp subst_eq_dest)
    also have "... = Var x \<lhd> \<rho> \<lhd> \<sigma>'"
      using subst_Var_renaming_map_map_prod_eq[OF ball_is_var_\<rho>' inj_\<rho>', folded \<sigma>'_def] by simp
    also have "... = Var x' \<lhd> \<sigma>'"
      using x_\<rho> by simp
    finally show ?thesis
      by assumption
  next
    case False
    then show ?thesis
      by (metis subst_Var_ident_if_not_in_dom subst_comp)
  qed
qed

(* lemma "A \<subseteq> B \<Longrightarrow> f ` A \<subseteq> f ` B" *)

lemma ck_unifier_of_renamed_if_ck_unifier:
  assumes "SuperCalc.ck_unifier t u \<mu> k" and
    ren_\<rho>: "renaming \<rho> V" and
    \<rho>_\<rho>_inv_ident: "\<forall>x\<in>V. Var x \<lhd> \<rho> \<lhd> \<rho>_inv = Var x" and
    vars_t_u_subset: "vars_of t \<union> vars_of u \<subseteq> V" and
    dom_\<mu>: "fst ` set \<mu> \<subseteq> vars_of t \<union> vars_of u"
  defines "\<mu>' \<equiv> map (map_prod (\<lambda>x. the_Var (Var x \<lhd> \<rho>)) (\<lambda>v. v \<lhd> \<rho>)) \<mu>"
  shows "SuperCalc.ck_unifier (t \<lhd> \<rho>) (u \<lhd> \<rho>) \<mu>' k" (* \<and> Idem \<mu>'" *)
proof -
  show ?thesis
  proof (cases k)
    case Ground
    moreover with assms(1) have "Unifier \<mu> t u"
      by (simp add: SuperCalc.ck_unifier_def)
    ultimately show ?thesis
      using Unifier_of_renamed_if_Unifier[
          OF ren_\<rho> vars_t_u_subset subset_trans[OF dom_\<mu> vars_t_u_subset], folded \<mu>'_def]
      by (simp add: SuperCalc.ck_unifier_def)
  next
    case FirstOrder
    with assms(1) have "IMGU \<mu> t u" and "range_vars \<mu> \<subseteq> vars_of t \<union> vars_of u"
      by (simp_all add: SuperCalc.ck_unifier_def min_IMGU_def)

    have "fst ` set \<mu> \<subseteq> V"
      by (rule subset_trans[OF dom_\<mu> vars_t_u_subset])

    have "range_vars \<mu> \<subseteq> V"
      by (rule subset_trans[OF \<open>range_vars \<mu> \<subseteq> vars_of t \<union> vars_of u\<close> vars_t_u_subset])

    from \<open>IMGU \<mu> t u\<close> have "IMGU \<mu>' (t \<lhd> \<rho>) (u \<lhd> \<rho>)"
      using IMGU_of_renamed_if_IMGU[
          OF ren_\<rho> \<rho>_\<rho>_inv_ident vars_t_u_subset \<open>fst ` set \<mu> \<subseteq> V\<close>, folded \<mu>'_def]
      by simp
    moreover have "range_vars \<mu>' \<subseteq> vars_of (t \<lhd> \<rho>) \<union> vars_of (u \<lhd> \<rho>)"
    proof -
      have "range_vars \<mu>' \<subseteq> (\<lambda>x. the_Var (Var x \<lhd> \<rho>)) ` range_vars \<mu>"
        using range_vars_of_subst_adapted_to_renaming[
            OF ren_\<rho> \<open>fst ` set \<mu> \<subseteq> V\<close> \<open>range_vars \<mu> \<subseteq> V\<close>, folded \<mu>'_def]
        by simp
      also have "... \<subseteq> (\<lambda>x. the_Var (Var x \<lhd> \<rho>)) ` (vars_of t \<union> vars_of u)"
        using \<open>range_vars \<mu> \<subseteq> vars_of t \<union> vars_of u\<close> by auto
      also have "... \<subseteq> vars_of (t \<lhd> \<rho>) \<union> vars_of (u \<lhd> \<rho>)"
        by (smt (verit, ccfv_threshold) Un_iff image_subset_iff in_mono ren_\<rho> renaming_var_to_var
            subst_mono the_Var.simps vars_iff_occseq vars_t_u_subset)
      finally show ?thesis
        by assumption
    qed
    moreover have "fst ` set \<mu>' \<subseteq> vars_of (t \<lhd> \<rho>) \<union> vars_of (u \<lhd> \<rho>)"
    proof -
      have "fst ` set \<mu>' \<subseteq> (\<lambda>x. the_Var (Var x \<lhd> \<rho>)) ` fst ` set \<mu>"
        by (rule dom_of_subst_adapted_to_renaming[OF ren_\<rho> \<open>fst ` set \<mu> \<subseteq> V\<close>, folded \<mu>'_def])
      also have "... \<subseteq> (\<lambda>x. the_Var (Var x \<lhd> \<rho>)) ` (vars_of t \<union> vars_of u)"
        by (rule image_mono[OF dom_\<mu>])
      also have "... \<subseteq> vars_of (t \<lhd> \<rho>) \<union> vars_of (u \<lhd> \<rho>)"
        by (smt (verit, ccfv_threshold) Un_iff image_iff in_mono ren_\<rho> renaming_var_to_var subsetI
            subst_mono the_Var.simps vars_iff_occseq vars_t_u_subset)
      finally show ?thesis
        by assumption
    qed
    ultimately show ?thesis
      unfolding FirstOrder
      by (simp add: SuperCalc.ck_unifier_def min_IMGU_def)
  qed
qed

lemma renaming_subset: "V1 \<subseteq> V2 \<Longrightarrow> renaming \<rho> V2 \<Longrightarrow> renaming \<rho> V1"
  unfolding renaming_def by (meson subset_iff)

lemma inj_subst_if_renaming:
  assumes ren_\<rho>: "renaming \<rho> V"
  shows "inj_on (\<lambda>t. t \<lhd> \<rho>) {t. vars_of t \<subseteq> V}"
proof (rule inj_onI, unfold mem_Collect_eq)
  fix t u
  show "vars_of t \<subseteq> V \<Longrightarrow> vars_of u \<subseteq> V \<Longrightarrow> t \<lhd> \<rho> = u \<lhd> \<rho> \<Longrightarrow> t = u"
  proof (induction "t" arbitrary: u)
    case (Var x)
    from ren_\<rho> Var.prems obtain y where u_def: "u = Var y"
      by (metis occs.elims(1) renaming_subset renaming_var_to_var subst.simps(3) subst_trm_ident
          trm.distinct(3) vars_iff_occseq)
    with Var.prems(3) have "Var x \<lhd> \<rho> = Var y \<lhd> \<rho>"
      by simp
    with ren_\<rho> Var.prems(1,2) show ?case
      by (auto simp: u_def elim: inj_on_if_renaming[THEN inj_onD, of \<rho> _ x y])
  next
    case (Const x)
    from ren_\<rho> Const.prems obtain y where u_def: "u = Const y"
      by (metis is_a_variable.simps(2) occs.elims(1) renaming_def subsetD subst.simps(2,3)
          trm.distinct(5) vars_iff_occseq)
    with ren_\<rho> Const.prems(3) show ?case
      by simp
  next
    case (Comb t1 t2)
    from ren_\<rho> Comb.prems obtain u1 u2 where u_def: "u = u1 \<cdot> u2"
      by (metis is_a_variable.elims(1) renaming_def renaming_subset subst.simps(2,3) trm.simps(7)
          vars_iff_occseq)
    with Comb.prems(3) have "t1 \<lhd> \<rho> = u1 \<lhd> \<rho>" and "t2 \<lhd> \<rho> = u2 \<lhd> \<rho>"
      by simp_all

    moreover from Comb.prems(1) have "vars_of t1 \<subseteq> V" and "vars_of t2 \<subseteq> V"
      by simp_all

    moreover from Comb.prems(2) have "vars_of u1 \<subseteq> V" and "vars_of u2 \<subseteq> V"
      by (simp_all add: u_def)

    ultimately show ?case
      unfolding u_def trm.inject
      by (auto intro: Comb.IH)
  qed
qed

lemma inj_subst_equation_if_renaming:
  assumes ren_\<rho>: "renaming \<rho> V"
  shows "inj_on (\<lambda>e. subst_equation e \<rho>) {e. vars_of_eq e \<subseteq> V}"
proof (rule inj_onI, unfold mem_Collect_eq)
  fix e1 e2
  assume "vars_of_eq e1 \<subseteq> V" "vars_of_eq e2 \<subseteq> V" and
    "subst_equation e1 \<rho> = subst_equation e2 \<rho> "
  then show "e1 = e2"
    by (cases e1; cases e2) (auto elim: inj_subst_if_renaming[OF ren_\<rho>, THEN inj_onD])
qed

lemma inj_subst_lit_if_renaming:
  assumes ren_\<rho>: "renaming \<rho> V"
  shows "inj_on (\<lambda>L. equational_clausal_logic.subst_lit L \<rho>) {L. vars_of_lit L \<subseteq> V}"
proof (rule inj_onI, unfold mem_Collect_eq)
  fix L K
  assume "vars_of_lit L \<subseteq> V" "vars_of_lit K \<subseteq> V" and
    "equational_clausal_logic.subst_lit L \<rho> = equational_clausal_logic.subst_lit K \<rho>"
  then show "L = K"
    by (cases L; cases K) (auto elim: inj_subst_equation_if_renaming[OF ren_\<rho>, THEN inj_onD])
qed
    

lemma dom_trm_if_dom_trm_subst_renaming:
  assumes
    ren_\<rho>: "renaming \<rho> (vars_of t \<union> vars_of_cl C)" and
    dom_trm: "SuperCalc.dom_trm (t \<lhd> \<rho>) (subst_cl C \<rho>)"
  shows "SuperCalc.dom_trm t C"
proof -
  from dom_trm obtain L u v p where
    L_in: "L \<in> subst_cl C \<rho>" and
    decomp_L: "decompose_literal L u v p" and
    neg_or_less: "p = neg \<and> t \<lhd> \<rho> = u \<or> (t \<lhd> \<rho>, u) \<in> trm_ord"
    by (auto simp: SuperCalc.dom_trm_def)

  from L_in obtain L' where
    L'_in: "L' \<in> C" and
    L_def: "L = equational_clausal_logic.subst_lit L' \<rho>"
    by (auto simp: subst_cl.simps)

  hence "atom L = subst_equation (atom L') \<rho>"
    by (metis atom.simps(1) atom.simps(2) subst_lit.elims)

  moreover from decomp_L have decomp_atom_L: "decompose_equation (atom L) u v"
    by (auto simp add: decompose_literal_def)

  ultimately obtain u' v' where
    u_def: "u = u' \<lhd> \<rho>" and v_def: "v = v' \<lhd> \<rho>" and
    decomp_atom_L': "decompose_equation (atom L') u' v'"
    unfolding decompose_equation_def
    by (metis equation.inject subst_equation.simps subterms_of_eq.cases)

  show ?thesis
    unfolding SuperCalc.dom_trm_def
  proof (intro exI conjI)
    show "L' \<in> C"
      by (rule L'_in)
  next
    show "decompose_literal L' u' v' p"
      using decomp_atom_L'
      by (metis (full_types) L_def atom.elims decomp_L decompose_literal_def
          equational_clausal_logic.literal.simps(4) subst_lit.simps(1) subst_lit.simps(2))
  next
    from neg_or_less show "p = neg \<and> t = u' \<or> (t, u') \<in> trm_ord"
    proof (elim disjE conjE)
      assume p_def: "p = neg" and t_\<rho>: "t \<lhd> \<rho> = u"
      
      have ren_\<rho>': "renaming \<rho> (vars_of t \<union> vars_of u')"
      proof (rule renaming_subset[OF _ ren_\<rho>])
        have "vars_of u' \<subseteq> vars_of_cl C"
          by (metis L'_in atom.elims decomp_atom_L' decompose_equation_vars dual_order.trans
              vars_of_cl_lem vars_of_lit.simps(1) vars_of_lit.simps(2))
        then show "vars_of t \<union> vars_of u' \<subseteq> vars_of t \<union> vars_of_cl C"
          by blast
      qed

      from t_\<rho> have "t = u'"
        unfolding u_def
        by (rule ren_\<rho>'[THEN inj_subst_if_renaming, THEN inj_onD]) simp_all
      with p_def show ?thesis
        by simp
    next
      assume "(t \<lhd> \<rho>, u) \<in> trm_ord"
      hence "(t \<lhd> \<rho>, u' \<lhd> \<rho>) \<in> trm_ord"
        unfolding u_def by assumption

      moreover have "renaming \<rho> (vars_of t \<union> vars_of u')"
      proof (rule renaming_subset[OF _ ren_\<rho>])
        have "vars_of u' \<subseteq> vars_of_cl C"
          by (metis L'_in atom.elims decomp_atom_L' decompose_equation_vars dual_order.trans
              vars_of_cl_lem vars_of_lit.simps(1) vars_of_lit.simps(2))
        then show "vars_of t \<union> vars_of u' \<subseteq> vars_of t \<union> vars_of_cl C"
          by blast
      qed

      ultimately have "(t, u') \<in> trm_ord"
        using SuperCalc.trm_ord_subst_renaming by simp
      thus ?thesis ..
    qed
  qed
qed

lemma vars_of_subst_conv: "vars_of (t \<lhd> \<sigma>) = (\<Union>x \<in> vars_of t. vars_of (Var x \<lhd> \<sigma>))"
  by (metis UN_simps(10) vars_of_subst_conv_Union)

lemma vars_of_subst_equation_conv:
  "vars_of_eq (subst_equation e \<sigma>) = (\<Union>x \<in> vars_of_eq e. vars_of (Var x \<lhd> \<sigma>))"
  using vars_of_subst_conv by (simp add: vars_of_eq_subst_equation_conv)

lemma vars_of_subst_lit_conv:
  "vars_of_lit (equational_clausal_logic.subst_lit L \<sigma>) =
    (\<Union>x \<in> vars_of_lit L. vars_of (Var x \<lhd> \<sigma>))"
  using vars_of_subst_equation_conv by (simp add: vars_of_lit_subst_lit_conv)

lemma vars_of_subst_cl_conv:
  "vars_of_cl (subst_cl C \<sigma>) = (\<Union>x \<in> vars_of_cl C. vars_of (Var x \<lhd> \<sigma>))"
proof (rule Set.equalityI; rule Set.subsetI)
  show "\<And>x. x \<in> vars_of_cl (subst_cl C \<sigma>) \<Longrightarrow> x \<in> (\<Union>x\<in>vars_of_cl C. vars_of (Var x \<lhd> \<sigma>))"
    using vars_of_subst_lit_conv
    by (smt (z3) UN_iff mem_Collect_eq subst_cl.simps vars_of_cl.simps)
next
  show "\<And>x. x \<in> (\<Union>x\<in>vars_of_cl C. vars_of (Var x \<lhd> \<sigma>)) \<Longrightarrow> x \<in> vars_of_cl (subst_cl C \<sigma>)"
    by (smt (verit, ccfv_threshold) UN_iff image_iff mem_Collect_eq subst_cl_conv vars_of_cl.simps
        vars_of_subst_lit_conv)
qed

lemma vars_of_subst_eq_subset: "vars_of_eq (subst_equation e \<sigma>) \<subseteq> vars_of_eq e \<union> range_vars \<sigma>"
  apply (cases e)
  using vars_of_subst_subset by force

lemma vars_of_subst_lit_subset:
  "vars_of_lit (equational_clausal_logic.subst_lit L \<sigma>) \<subseteq> vars_of_lit L \<union> range_vars \<sigma>"
  by (cases L) (simp_all add: vars_of_subst_eq_subset)

lemma vars_of_subst_cl_subset:
  "vars_of_cl (subst_cl C \<sigma>) \<subseteq> vars_of_cl C \<union> range_vars \<sigma>"
  using vars_of_subst_lit_subset
  by (smt (verit, ccfv_threshold) Un_iff mem_Collect_eq subset_eq subst_cl.simps vars_of_cl.simps)

lemma vars_of_subst: "vars_of (t \<lhd> \<sigma>) =
  vars_of t - {x \<in> vars_of t. Var x \<lhd> \<sigma> \<noteq> Var x} \<union> (\<Union>x \<in> vars_of t. vars_of (Var x \<lhd> \<sigma>))"
  by (smt (z3) DiffE UN_iff UN_simps(10) UnE equalityI image_cong mem_Collect_eq subsetI sup_ge2
      vars_iff_occseq vars_of_subst_conv)

lemma vars_of_subst_lit: "vars_of_lit (equational_clausal_logic.subst_lit L \<sigma>) =
  vars_of_lit L - {x \<in> vars_of_lit L. Var x \<lhd> \<sigma> \<noteq> Var x} \<union> (\<Union>x \<in> vars_of_lit L. vars_of (Var x \<lhd> \<sigma>))"
proof (cases L)
  case (Pos e)
  thus ?thesis
    by (cases e) (auto simp add: vars_of_subst)
next
  case (Neg e)
  thus ?thesis
    by (cases e) (auto simp add: vars_of_subst)
qed

lemma vars_of_subst_cl: "vars_of_cl (subst_cl C \<sigma>) =
  vars_of_cl C - {x \<in> vars_of_cl C. Var x \<lhd> \<sigma> \<noteq> Var x} \<union> (\<Union>x \<in> vars_of_cl C. vars_of (Var x \<lhd> \<sigma>))"
  (is "?lhs = ?rhs")
proof (rule Set.equalityI; rule Set.subsetI)
  fix x assume "x \<in> ?lhs"
  thus "x \<in> ?rhs"
    apply simp
    using vars_of_subst_lit
    by (smt (verit, ccfv_threshold) DiffD1 DiffD2 UN_iff Un_iff mem_Collect_eq subst.simps(1)
        subst_cl.simps vars_of_cl.simps)
next
  fix x assume "x \<in> ?rhs"
  thus "x \<in> ?lhs"
    apply simp
    using vars_of_subst_lit
    by (smt (z3) DiffI UN_iff Un_iff mem_Collect_eq subst.simps(1) subst_cl.simps vars_of_cl.simps)
qed

lemma subst_lit_renaming_ord_iff:
  assumes ren_\<rho>: "renaming \<rho> (vars_of_lit L \<union> vars_of_lit K)"
  shows "(equational_clausal_logic.subst_lit L \<rho>, equational_clausal_logic.subst_lit K \<rho>) \<in>
      SuperCalc.lit_ord \<longleftrightarrow> (L, K) \<in> SuperCalc.lit_ord"
    (is "?lhs \<longleftrightarrow> ?rhs")
proof (rule iffI)
  obtain t\<^sub>L u\<^sub>L where decomp_L: "decompose_equation (atom L) t\<^sub>L u\<^sub>L"
    by (metis decompose_equation_def subterms_of_eq.cases)
  obtain t\<^sub>K u\<^sub>K where decomp_K: "decompose_equation (atom K) t\<^sub>K u\<^sub>K"
    by (metis decompose_equation_def subterms_of_eq.cases)

  have vars_of_lit_conv: "vars_of_lit L = vars_of_eq (atom L)" for L
    by (metis atom.elims vars_of_lit.simps)

  have vars_of_L_conv: "vars_of_lit L = vars_of t\<^sub>L \<union> vars_of u\<^sub>L"
    by (metis Un_commute \<open>decompose_equation (atom L) t\<^sub>L u\<^sub>L\<close> decompose_equation_def vars_of_eq.simps
        vars_of_lit_conv)
  
  have vars_of_K_conv: "vars_of_lit K = vars_of t\<^sub>K \<union> vars_of u\<^sub>K"
    by (metis \<open>decompose_equation (atom K) t\<^sub>K u\<^sub>K\<close> atom.elims decompose_equation_def sup_commute
        vars_of_eq.simps vars_of_lit.simps(1) vars_of_lit.simps(2))

  have 1: "\<forall>t \<in> {t\<^sub>L, u\<^sub>L, t\<^sub>K, u\<^sub>K}. \<forall>u \<in> {t\<^sub>L, u\<^sub>L, t\<^sub>K, u\<^sub>K}.
    (t \<lhd> \<rho>, u \<lhd> \<rho>) \<in> trm_ord \<longrightarrow> (t, u) \<in> trm_ord"
  proof (intro ballI impI, erule SuperCalc.trm_ord_subst_renaming[rule_format, rotated])
    show "\<And>t u. t \<in> {t\<^sub>L, u\<^sub>L, t\<^sub>K, u\<^sub>K} \<Longrightarrow> u \<in> {t\<^sub>L, u\<^sub>L, t\<^sub>K, u\<^sub>K} \<Longrightarrow>
      renaming \<rho> (vars_of t \<union> vars_of u)"
      using ren_\<rho>[unfolded vars_of_L_conv vars_of_K_conv]
      by (auto elim: renaming_subset[rotated])
  qed

  have 2: "inj_on (\<lambda>t. t \<lhd> \<rho>) {t\<^sub>L, u\<^sub>L, t\<^sub>K, u\<^sub>K}"
    using ren_\<rho>[THEN inj_subst_if_renaming]
  proof (rule inj_on_subset)
    show "{t\<^sub>L, u\<^sub>L, t\<^sub>K, u\<^sub>K} \<subseteq> {t. vars_of t \<subseteq> vars_of_lit L \<union> vars_of_lit K}"
      by (auto simp: vars_of_L_conv vars_of_K_conv)
  qed

  have mset_lit_Pos_conv: "decompose_equation e t u \<Longrightarrow>
    SuperCalc.mset_lit (equational_clausal_logic.Pos e) = {#t, u#}" for e t u
    by (auto simp add: decompose_equation_def)

  have mset_lit_Neg_conv: "decompose_equation e t u \<Longrightarrow>
    SuperCalc.mset_lit (equational_clausal_logic.Neg e) = {#t, t, u, u#}" for e t u
    by (auto simp add: decompose_equation_def)

  have mset_lit_Pos_subst_conv: "decompose_equation e t u \<Longrightarrow>
    SuperCalc.mset_lit (equational_clausal_logic.Pos (subst_equation e \<rho>)) = {#t \<lhd> \<rho>, u \<lhd> \<rho>#}" for e t u
    by (auto simp add: decompose_equation_def)

  have mset_lit_Neg_subst_conv: "decompose_equation e t u \<Longrightarrow>
    SuperCalc.mset_lit (equational_clausal_logic.Neg (subst_equation e \<rho>)) = {#t \<lhd> \<rho>, t \<lhd> \<rho>, u \<lhd> \<rho>, u \<lhd> \<rho>#}" for e t u
    by (auto simp add: decompose_equation_def)

  show "?lhs \<Longrightarrow> ?rhs"
    using decomp_L decomp_K
    apply (cases L; cases K)
       apply (simp_all add: SuperCalc.lit_ord_def mset_lit_Pos_conv mset_lit_Neg_conv
        mset_lit_Pos_subst_conv mset_lit_Neg_subst_conv)
    subgoal
      apply (rule image_mset_image_mset_mem_multD[OF trm_ord_trans, of _ _ "\<lambda>t. t \<lhd> \<rho>"])
      using 1 apply simp
      using 2 apply (metis Un_insert_left insert_is_Un set_mset_add_mset_insert set_mset_empty)
      by simp
    subgoal
      apply (rule image_mset_image_mset_mem_multD[OF trm_ord_trans, of _ _ "\<lambda>t. t \<lhd> \<rho>"])
      using 1 apply simp
      using 2
       apply (metis Un_insert_left insert_absorb insert_is_Un set_mset_add_mset_insert
          set_mset_empty union_single_eq_member)
      by simp
    subgoal
      apply (rule image_mset_image_mset_mem_multD[OF trm_ord_trans, of _ _ "\<lambda>t. t \<lhd> \<rho>"])
      using 1 apply simp
      using 2
       apply (metis Un_insert_left insert_absorb insert_is_Un set_mset_add_mset_insert set_mset_empty
          union_single_eq_member)
      by simp
    subgoal 
      apply (rule image_mset_image_mset_mem_multD[OF trm_ord_trans, of _ _ "\<lambda>t. t \<lhd> \<rho>"])
      using 1 apply simp
      using 2
       apply (metis Un_insert_left insert_absorb insert_is_Un set_mset_add_mset_insert set_mset_empty
          union_single_eq_member)
      by simp
    done
next
  show "?rhs \<Longrightarrow> ?lhs"
    using SuperCalc.lit_ord_subst by blast
qed

lemma subst_cl_minus_subst_cl_eq_subst_cl_minus:
  assumes inj_subst_\<rho>:
    "inj_on (\<lambda>L. equational_clausal_logic.subst_lit L \<rho>) (C \<union> D)"
  shows "subst_cl C \<rho> - subst_cl D \<rho> = subst_cl (C - D) \<rho>"
  unfolding cl_ecl_subst_ecl_distrib
proof (rule Set.equalityI; rule subsetI)
  fix K
  assume "K \<in> subst_cl C \<rho> - subst_cl D \<rho>"
  then show "K \<in> subst_cl (C - D) \<rho>"
    apply simp
    using inj_subst_\<rho>[THEN inj_onD]
    by (smt (verit, best) DiffI image_iff subst_cl_conv)
next
  fix K
  assume "K \<in> subst_cl (C - D) \<rho>"
  then show "K \<in> subst_cl C \<rho> - subst_cl D \<rho>"
    apply simp
    using inj_subst_\<rho>[THEN inj_onD]
    by (smt (verit, del_insts) DiffD1 DiffD2 Un_iff mem_Collect_eq subst_cl.simps)
qed

lemma eligible_literal_of_renaming:
  "SuperCalc.eligible_literal (equational_clausal_logic.subst_lit L1 \<rho>) (subst_ecl P1 \<rho>) \<sigma>\<^sub>D"
  if eli_L1: "SuperCalc.eligible_literal L1 P1 \<sigma>\<^sub>C" and
    ren_\<rho>: "renaming \<rho> (vars_of_cl (cl_ecl P1))" and
    \<sigma>\<^sub>D_def: "\<sigma>\<^sub>D = map (map_prod (\<lambda>x. the_Var (Var x \<lhd> \<rho>)) (\<lambda>v. v \<lhd> \<rho>)) \<sigma>\<^sub>C" and
    ball_is_Var: "\<forall>x\<in>vars_of_lit L1 \<union> vars_of_cl (cl_ecl P1) \<union> fst ` set \<sigma>\<^sub>C.
             is_a_variable (Var x \<lhd> \<rho>)" and
    inj_subst: "inj_on (\<lambda>x. Var x \<lhd> \<rho>)
             (vars_of_lit L1 \<union> vars_of_cl (cl_ecl P1) \<union> fst ` set \<sigma>\<^sub>C)" and
    range_\<sigma>\<^sub>C: "range_vars \<sigma>\<^sub>C \<subseteq> vars_of_cl (cl_ecl P1)" and
    L1_in: "L1 \<in> cl_ecl P1"
  for L1 \<rho> \<sigma>\<^sub>D P1 \<sigma>\<^sub>C
  using eli_L1[unfolded SuperCalc.eligible_literal_def]
proof (elim disjE conjE)
  assume "L1 \<in> select (cl_ecl P1)"
  hence "equational_clausal_logic.subst_lit L1 \<rho> \<in> select (subst_cl (cl_ecl P1) \<rho>)"
    unfolding select_renaming_strong[rule_format, of \<rho> "cl_ecl P1", OF ren_\<rho>]
    by (simp add: subst_cl_conv)
  thus ?thesis
    unfolding SuperCalc.eligible_literal_def cl_ecl_subst_ecl_distrib
    by blast
next
  assume
    1: "select (cl_ecl P1) = {}" and
    2: "SuperCalc.maximal_literal (equational_clausal_logic.subst_lit L1 \<sigma>\<^sub>C)
            (subst_cl (cl_ecl P1) \<sigma>\<^sub>C)"
  from 1 have "select (subst_cl (cl_ecl P1) \<rho>) = {}"
    unfolding select_renaming_strong[rule_format, of \<rho> "cl_ecl P1", OF ren_\<rho>]
    by simp
  moreover have "SuperCalc.maximal_literal
          (equational_clausal_logic.subst_lit (equational_clausal_logic.subst_lit L1 \<rho>) \<sigma>\<^sub>D)
          (subst_cl (subst_cl (cl_ecl P1) \<rho>) \<sigma>\<^sub>D)"
    unfolding SuperCalc.maximal_literal_def
  proof (intro allI impI)
    fix x assume x_in: "x \<in> subst_cl (subst_cl (cl_ecl P1) \<rho>) \<sigma>\<^sub>D"
    hence "x \<in> subst_cl (subst_cl (cl_ecl P1) \<sigma>\<^sub>C) \<rho>"
      using subst_cl_renaming_map_map_prod_eq[of _ \<sigma>\<^sub>C \<rho>, folded \<sigma>\<^sub>D_def] ball_is_Var inj_subst
      by (metis (no_types, lifting) Un_iff inf_sup_ord(4) inj_on_subset sup_assoc)
    then obtain x' where
      x'_in: "x' \<in> subst_cl (cl_ecl P1) \<sigma>\<^sub>C" and
      x_def: "x = equational_clausal_logic.subst_lit x' \<rho>"
      by (metis (mono_tags, lifting) image_iff subst_cl_conv)

    have "vars_of_cl (subst_cl (cl_ecl P1) \<sigma>\<^sub>C) \<subseteq> vars_of_cl (cl_ecl P1)"
      using range_\<sigma>\<^sub>C vars_of_subst_cl_subset by fast
    hence vars_of_x': "vars_of_lit x' \<subseteq> vars_of_cl (cl_ecl P1)"
      using x'_in vars_of_cl_lem by blast

    have vars_of_L_\<sigma>\<^sub>C: "vars_of_lit (equational_clausal_logic.subst_lit L1 \<sigma>\<^sub>C) \<subseteq>
            vars_of_cl (cl_ecl P1)"
      using range_\<sigma>\<^sub>C L1_in
      by (smt (verit, best) Un_iff subset_iff vars_of_cl_lem vars_of_subst_lit_subset)

    have
      "(equational_clausal_logic.subst_lit (equational_clausal_logic.subst_lit L1 \<sigma>\<^sub>C) \<rho>, x)
              \<notin> SuperCalc.lit_ord"
      unfolding x_def
      using 2[unfolded SuperCalc.maximal_literal_def, rule_format, OF x'_in]
      apply (rule contrapos_nn)
      apply (rule subst_lit_renaming_ord_iff[THEN iffD1])
      apply (rule renaming_subset[OF _ ren_\<rho>])
      using vars_of_x' vars_of_L_\<sigma>\<^sub>C
      by simp
    thus
      "(equational_clausal_logic.subst_lit (equational_clausal_logic.subst_lit L1 \<rho>) \<sigma>\<^sub>D, x)
              \<notin> SuperCalc.lit_ord"
      using subst_lit_renaming_map_map_prod_eq[of L1 \<sigma>\<^sub>C \<rho>, folded \<sigma>\<^sub>D_def] ball_is_Var inj_subst
      by (smt (verit, best) Un_iff inj_on_def)
  qed
  ultimately show ?thesis
    unfolding SuperCalc.eligible_literal_def cl_ecl_subst_ecl_distrib
    by simp
qed

lemma reflexion_if_renaming:
  fixes \<sigma>
  assumes
    refl: "SuperCalc.reflexion P1 C \<sigma>\<^sub>C SuperCalc.FirstOrder C'" and
    ren: "renaming_cl P1 P1'" and
    fin: "finite (cl_ecl P1)"
  shows "\<exists>D \<sigma>\<^sub>D D'. SuperCalc.reflexion P1' D \<sigma>\<^sub>D SuperCalc.FirstOrder D' \<and> renaming_cl C D"
proof -
  from refl obtain L1 t s Cl_P Cl_C trms_C where
    "SuperCalc.eligible_literal L1 P1 \<sigma>\<^sub>C" and
    "L1 \<in> cl_ecl P1" and
    "Cl_C = cl_ecl C" and
    Cl_P_def: "Cl_P = cl_ecl P1" and
    "SuperCalc.orient_lit_inst L1 t s neg \<sigma>\<^sub>C" and
    unif_t_s: "SuperCalc.ck_unifier t s \<sigma>\<^sub>C SuperCalc.FirstOrder" and
    C_def: "C = Ecl Cl_C trms_C" and
    trms_C_def: "trms_C = SuperCalc.get_trms Cl_C
      (SuperCalc.dom_trms Cl_C (subst_set (trms_ecl P1 \<union> {t}) \<sigma>\<^sub>C)) SuperCalc.FirstOrder" and
    Cl_C_def: "Cl_C = subst_cl C' \<sigma>\<^sub>C" and
    C'_def: "C' = Cl_P - {L1}"
    unfolding SuperCalc.reflexion_def by blast

  have vars_t_s_subset: "vars_of t \<union> vars_of s \<subseteq> vars_of_cl (cl_ecl P1)"
    using SuperCalc.orient_lit_inst_vars \<open>L1 \<in> cl_ecl P1\<close> \<open>SuperCalc.orient_lit_inst L1 t s neg \<sigma>\<^sub>C\<close>
    using vars_of_cl_lem by fastforce
  
  from unif_t_s have
    "fst ` set \<sigma>\<^sub>C \<subseteq> vars_of t \<union> vars_of s" and
    "range_vars \<sigma>\<^sub>C \<subseteq> vars_of t \<union> vars_of s"
    by (simp_all add: SuperCalc.ck_unifier_def min_IMGU_def)
  hence
    dom_vars_\<sigma>\<^sub>C: "fst ` set \<sigma>\<^sub>C \<subseteq> vars_of_cl (cl_ecl P1)" and
    range_vars_\<sigma>\<^sub>C: "range_vars \<sigma>\<^sub>C \<subseteq> vars_of_cl (cl_ecl P1)"
    using vars_t_s_subset by auto

  from ren obtain \<rho> where
    ren_\<rho>: "renaming \<rho> (vars_of_cl (cl_ecl P1))" and
    P1'_def: "P1' = subst_ecl P1 \<rho>"
    unfolding renaming_cl_def by blast

  from fin have fin_vars_P1: "finite (vars_of_cl (cl_ecl P1))"
    using set_of_variables_is_finite_cl by blast
  with ren_\<rho> obtain \<rho>_inv where
    \<rho>_\<rho>_inv_ident: "\<forall>x\<in>vars_of_cl (cl_ecl P1). Var x \<lhd> \<rho> \<lhd> \<rho>_inv = Var x" and
      "\<forall>x. x \<notin> subst_codomain \<rho> (vars_of_cl (cl_ecl P1)) \<longrightarrow> Var x \<lhd> \<rho>_inv = Var x" and
      "\<forall>x. is_a_variable (Var x \<lhd> \<rho>_inv)"
    using renamings_admit_inverse by blast

  have subst_P1_\<rho>_\<rho>_inv: "subst_cl (subst_cl (cl_ecl P1) \<rho>) \<rho>_inv = cl_ecl P1"
    using subst_cl_identI[OF \<open>\<forall>x\<in>vars_of_cl (cl_ecl P1). Var x \<lhd> \<rho> \<lhd> \<rho>_inv = Var x\<close>]
    by simp

  from \<open>L1 \<in> cl_ecl P1\<close> have L1_\<rho>_in_P1': "equational_clausal_logic.subst_lit L1 \<rho> \<in> cl_ecl P1'"
    by (simp add: P1'_def cl_ecl_subst_ecl_distrib subst_cl_conv)

  define D' where
    "D' = cl_ecl P1' - {equational_clausal_logic.subst_lit L1 \<rho>}"

  have vars_of_subst_var_in_P1: "vars_of (Var x \<lhd> \<sigma>\<^sub>C) \<subseteq> vars_of_cl (cl_ecl P1)"
    if x_in: "x \<in> vars_of_cl (cl_ecl P1)" for x
  proof (cases "Var x \<lhd> \<sigma>\<^sub>C = Var x")
    case True
    with x_in show ?thesis by simp
  next
    case False
    with x_in show ?thesis
      using range_vars_\<sigma>\<^sub>C unfolding range_vars_def by blast
  qed

  define \<sigma>\<^sub>D where
    "\<sigma>\<^sub>D = map (map_prod (\<lambda>x. the_Var (Var x \<lhd> \<rho>)) (\<lambda>v. v \<lhd> \<rho>)) \<sigma>\<^sub>C"

  have "SuperCalc.ck_unifier (t \<lhd> \<rho>) (s \<lhd> \<rho>) \<sigma>\<^sub>D SuperCalc.FirstOrder" (* and "Idem \<sigma>\<^sub>D" *)
    using ck_unifier_of_renamed_if_ck_unifier[
        OF \<open>SuperCalc.ck_unifier t s \<sigma>\<^sub>C SuperCalc.FirstOrder\<close> ren_\<rho> \<rho>_\<rho>_inv_ident vars_t_s_subset
        \<open>fst ` set \<sigma>\<^sub>C \<subseteq> vars_of t \<union> vars_of s\<close>, folded \<sigma>\<^sub>D_def]
    by simp_all
  hence "Unifier \<sigma>\<^sub>D (t \<lhd> \<rho>) (s \<lhd> \<rho>)"
    using SuperCalc.ck_unifier_thm Unifier_def by blast

  have subst_\<rho>_\<sigma>\<^sub>D_conv:
    "Var x \<lhd> \<rho> \<lhd> \<sigma>\<^sub>D = Var x \<lhd> \<sigma>\<^sub>C \<lhd> \<rho>" if x_in: "x \<in> vars_of_cl (cl_ecl P1)" for x
    (* using subst_renaming_map_map_prod_eq[of _ \<sigma>\<^sub>C \<rho>, folded \<sigma>\<^sub>D_def] *)
  proof -
    have x_dom_\<sigma>\<^sub>C_subset: "insert x (fst ` set \<sigma>\<^sub>C) \<subseteq> vars_of_cl (cl_ecl P1)"
      using x_in dom_vars_\<sigma>\<^sub>C vars_t_s_subset by blast

    from ren_\<rho> have "\<forall>x\<in>vars_of_cl (cl_ecl P1). is_a_variable (Var x \<lhd> \<rho>)"
      using renaming_def by fast
    hence all_vars: "\<forall>x\<in>insert x (fst ` set \<sigma>\<^sub>C). is_a_variable (Var x \<lhd> \<rho>)"
      using x_dom_\<sigma>\<^sub>C_subset by blast

    from ren_\<rho> have "inj_on (\<lambda>x. Var x \<lhd> \<rho>) (vars_of_cl (cl_ecl P1))"
      using inj_on_if_renaming by blast
    hence inj_\<rho>: "inj_on (\<lambda>x. Var x \<lhd> \<rho>) (insert x (fst ` set \<sigma>\<^sub>C))"
      using x_dom_\<sigma>\<^sub>C_subset by (meson inj_on_subset)

    show ?thesis
      unfolding \<sigma>\<^sub>D_def
      unfolding subst_Var_renaming_map_map_prod_eq[OF all_vars inj_\<rho>]
      by simp
  qed
  hence subst_lit_\<rho>_\<sigma>\<^sub>D_conv:
    "equational_clausal_logic.subst_lit (equational_clausal_logic.subst_lit L \<rho>) \<sigma>\<^sub>D =
     equational_clausal_logic.subst_lit (equational_clausal_logic.subst_lit L \<sigma>\<^sub>C) \<rho>"
    if L_in: "L \<in> cl_ecl P1"
    for L
    unfolding composition_of_substs_lit
    using L_in
    unfolding composition_of_substs
    by (meson coincide_on_def coincide_on_lit subset_iff vars_of_cl_lem)
  hence subst_cl_\<rho>_\<sigma>\<^sub>D_conv: "subst_cl (subst_cl (cl_ecl P1) \<rho>) \<sigma>\<^sub>D = subst_cl (subst_cl (cl_ecl P1) \<sigma>\<^sub>C) \<rho>"
    by (metis (mono_tags, lifting) composition_of_substs_cl composition_of_substs_lit image_cong subst_cl_conv)

  define D where
    "D = (let Cl_D = subst_cl D' \<sigma>\<^sub>D in
      Ecl Cl_D (SuperCalc.get_trms Cl_D
        (SuperCalc.dom_trms Cl_D (subst_set (trms_ecl P1' \<union> {t \<lhd> \<rho>}) \<sigma>\<^sub>D)) SuperCalc.FirstOrder))"

  have vars_of_L1_subset: "vars_of_lit L1 \<subseteq> vars_of_cl (cl_ecl P1)"
    using \<open>L1 \<in> cl_ecl P1\<close> vars_of_cl_lem by blast

  hence vars_of_t_s_subset:
    "vars_of t \<subseteq> vars_of_cl (cl_ecl P1)" "vars_of s \<subseteq> vars_of_cl (cl_ecl P1)"
    using \<open>SuperCalc.orient_lit_inst L1 t s neg \<sigma>\<^sub>C\<close>
    unfolding SuperCalc.orient_lit_inst_def
    by auto

  show ?thesis
  proof (intro exI conjI)
    show "SuperCalc.reflexion P1' D \<sigma>\<^sub>D SuperCalc.FirstOrder D'"
      unfolding SuperCalc.reflexion_def
    proof (intro exI conjI)
      show "equational_clausal_logic.subst_lit L1 \<rho> \<in> cl_ecl P1'"
        by (rule L1_\<rho>_in_P1')
    next
      show "SuperCalc.eligible_literal (equational_clausal_logic.subst_lit L1 \<rho>) P1' \<sigma>\<^sub>D"
        unfolding P1'_def
      proof (rule eligible_literal_of_renaming[OF \<open>SuperCalc.eligible_literal L1 P1 \<sigma>\<^sub>C\<close>,
              OF ren_\<rho> \<sigma>\<^sub>D_def _ _ range_vars_\<sigma>\<^sub>C \<open>L1 \<in> cl_ecl P1\<close>])
        show "\<forall>x\<in>vars_of_lit L1 \<union> vars_of_cl (cl_ecl P1) \<union> fst ` set \<sigma>\<^sub>C. is_a_variable (Var x \<lhd> \<rho>)"
          using renaming_imp_ball_var[OF ren_\<rho>]
          by (metis dom_vars_\<sigma>\<^sub>C subset_Un_eq sup.order_iff vars_of_L1_subset)
      next
        show "inj_on (\<lambda>x. Var x \<lhd> \<rho>) (vars_of_lit L1 \<union> vars_of_cl (cl_ecl P1) \<union> fst ` set \<sigma>\<^sub>C)"
          using inj_on_if_renaming[OF ren_\<rho>]
          by (metis Un_absorb1 Un_absorb2 dom_vars_\<sigma>\<^sub>C vars_of_L1_subset)
      qed
    next
      show "subst_cl D' \<sigma>\<^sub>D = cl_ecl D"
        unfolding D_def by (simp add: Let_def)
    next
      show "cl_ecl P1' = cl_ecl P1'"
        by simp
    next
      show "SuperCalc.orient_lit_inst (equational_clausal_logic.subst_lit L1 \<rho>) (t \<lhd> \<rho>) (s \<lhd> \<rho>)
        neg \<sigma>\<^sub>D"
        using \<open>SuperCalc.orient_lit_inst L1 t s neg \<sigma>\<^sub>C\<close>
        unfolding SuperCalc.orient_lit_inst_def
        apply (elim conjE disjE)
        apply simp_all
        by (metis Unifier_def \<open>Unifier \<sigma>\<^sub>D (t \<lhd> \<rho>) (s \<lhd> \<rho>)\<close> irrefl_def trm_ord_irrefl)+
    next
      show "SuperCalc.ck_unifier (t \<lhd> \<rho>) (s \<lhd> \<rho>) \<sigma>\<^sub>D SuperCalc.FirstOrder"
        by (rule \<open>SuperCalc.ck_unifier (t \<lhd> \<rho>) (s \<lhd> \<rho>) \<sigma>\<^sub>D SuperCalc.FirstOrder\<close>)
    qed (simp_all add: D_def D'_def Let_def)
  next
    have "renaming \<rho> (vars_of_cl C')"
      unfolding renaming_def
    proof (intro ballI conjI allI impI)
      fix x
      assume "x \<in> vars_of_cl C'"
      thus "is_a_variable (Var x \<lhd> \<rho>)"
        by (smt (verit, del_insts) Diff_iff \<open>C' = Cl_P - {L1}\<close> \<open>Cl_P = cl_ecl P1\<close>
            mem_Collect_eq ren_\<rho> renaming_def vars_of_cl.simps)
    next
      fix x y
      assume "x \<in> vars_of_cl C'" and "y \<in> vars_of_cl C'" and "x \<noteq> y"
      then show "Var x \<lhd> \<rho> \<noteq> Var y \<lhd> \<rho>"
        by (smt (verit, del_insts) Diff_iff \<open>C' = Cl_P - {L1}\<close> \<open>Cl_P = cl_ecl P1\<close>
            \<open>\<forall>x\<in>vars_of_cl (cl_ecl P1). Var x \<lhd> \<rho> \<lhd> \<rho>_inv = Var x\<close> mem_Collect_eq trm.inject(1)
            vars_of_cl.simps)
    qed

    have inj_subst_lit_\<rho>: "inj_on (\<lambda>L. equational_clausal_logic.subst_lit L \<rho>) (cl_ecl P1 \<union> {L1})"
      using inj_subst_lit_if_renaming[OF ren_\<rho>]
      by (rule inj_on_subset) (simp add: \<open>L1 \<in> cl_ecl P1\<close> subsetI vars_of_cl_lem)

    show "renaming_cl C D"
      unfolding renaming_cl_def
    proof (intro exI conjI)
      show "renaming \<rho> (vars_of_cl (cl_ecl C))"
      proof (rule renaming_subset[OF _ ren_\<rho>])
        have "(\<Union>x\<in>vars_of_cl (cl_ecl P1 - {L1}). vars_of (Var x \<lhd> \<sigma>\<^sub>C)) \<subseteq> vars_of_cl (cl_ecl P1)"
          unfolding UN_subset_iff using vars_of_subst_var_in_P1 by (auto simp: vars_of_cl.simps)
        thus "vars_of_cl (cl_ecl C) \<subseteq> vars_of_cl (cl_ecl P1)"
          unfolding C_def Cl_C_def C'_def Cl_P_def
          unfolding cl_ecl.simps
          unfolding vars_of_subst_cl
          by (auto simp: vars_of_cl.simps)
      qed
    next
      have "subst_cl D' \<sigma>\<^sub>D = subst_cl (cl_ecl P1' - {equational_clausal_logic.subst_lit L1 \<rho>}) \<sigma>\<^sub>D"
        by (simp add: D'_def)
      also have "... = subst_cl (cl_ecl P1' - subst_cl {L1} \<rho>) \<sigma>\<^sub>D"
        by (simp add: singleton_subst_lit_conv)
      also have "... = subst_cl (subst_cl (cl_ecl P1) \<rho> - subst_cl {L1} \<rho>) \<sigma>\<^sub>D"
        by (simp add: P1'_def cl_ecl_subst_ecl_distrib)
      also have "... = subst_cl (subst_cl (cl_ecl P1 - {L1}) \<rho>) \<sigma>\<^sub>D"
        using subst_cl_minus_subst_cl_eq_subst_cl_minus[OF inj_subst_lit_\<rho>] by simp
      also have "... = subst_cl (subst_cl (cl_ecl P1 - {L1}) \<sigma>\<^sub>C) \<rho>"
      proof (rule subst_cl_renaming_map_map_prod_eq[of _ \<sigma>\<^sub>C \<rho>, folded \<sigma>\<^sub>D_def])
        show "\<forall>x\<in>vars_of_cl (cl_ecl P1 - {L1}) \<union> fst ` set \<sigma>\<^sub>C. is_a_variable (Var x \<lhd> \<rho>)"
          by (metis C'_def Cl_P_def Un_absorb2 Un_iff \<open>renaming \<rho> (vars_of_cl C')\<close> dom_vars_\<sigma>\<^sub>C ren_\<rho>
              renaming_imp_ball_var)
      next
        show "inj_on (\<lambda>x. Var x \<lhd> \<rho>) (vars_of_cl (cl_ecl P1 - {L1}) \<union> fst ` set \<sigma>\<^sub>C)"
          by (rule inj_on_if_renaming[OF ren_\<rho>, THEN inj_on_subset])
            (smt (verit, del_insts) DiffD1 Un_iff dom_vars_\<sigma>\<^sub>C mem_Collect_eq subset_eq
              vars_of_cl.simps)
      qed
      also have "... = subst_cl (subst_cl C' \<sigma>\<^sub>C) \<rho>"
        by (simp add: C'_def Cl_P_def)
      also have "... = subst_cl Cl_C \<rho>"
        by (simp add: Cl_C_def)
      finally have D'_\<sigma>\<^sub>D: "subst_cl D' \<sigma>\<^sub>D = subst_cl Cl_C \<rho>"
        by assumption

      moreover have "SuperCalc.get_trms (subst_cl D' \<sigma>\<^sub>D)
        (SuperCalc.dom_trms (subst_cl D' \<sigma>\<^sub>D) (subst_set (trms_ecl P1' \<union> {t \<lhd> \<rho>}) \<sigma>\<^sub>D))
        SuperCalc.FirstOrder = {t \<lhd> \<rho> |t. t \<in> trms_C}"
        by (simp add: trms_C_def SuperCalc.get_trms_def)

      ultimately show "D = subst_ecl C \<rho>"
        by (simp add: \<open>C = Ecl Cl_C trms_C\<close> D_def)
    qed
  qed
qed

lemma subst_ecl_conv: "subst_ecl (Ecl C trms) \<sigma> = Ecl (subst_cl C \<sigma>) ((\<lambda>t. t \<lhd> \<sigma>) ` trms)"
  by auto

lemma subst_cl_union: "subst_cl (C \<union> D) \<sigma> = subst_cl C \<sigma> \<union> subst_cl D \<sigma>"
  by (simp add: image_Un subst_cl_conv)

lemma factorization_if_renaming:
  fixes \<sigma>
  assumes
    fact: "SuperCalc.factorization P1 C \<sigma>\<^sub>C SuperCalc.FirstOrder C'" and
    ren: "renaming_cl P1 P1'" and
    fin: "finite (cl_ecl P1)"
  shows "\<exists>D \<sigma>\<^sub>D D'. SuperCalc.factorization P1' D \<sigma>\<^sub>D SuperCalc.FirstOrder D' \<and> renaming_cl C D"
proof -
  from fact obtain L1 L2 L' t s u v where
    eligible_L1: "SuperCalc.eligible_literal L1 P1 \<sigma>\<^sub>C" and
    L1_in: "L1 \<in> cl_ecl P1" and
    L2_in: "L2 \<in> cl_ecl P1 - {L1}" and
    orient_L1: "SuperCalc.orient_lit_inst L1 t s pos \<sigma>\<^sub>C" and
    orient_L2: "SuperCalc.orient_lit_inst L2 u v pos \<sigma>\<^sub>C" and
    "t \<lhd> \<sigma>\<^sub>C \<noteq> s \<lhd> \<sigma>\<^sub>C" and
    "t \<lhd> \<sigma>\<^sub>C \<noteq> v \<lhd> \<sigma>\<^sub>C" and
    unif_t_u_\<sigma>\<^sub>C: "SuperCalc.ck_unifier t u \<sigma>\<^sub>C SuperCalc.FirstOrder" and
    L'_eq: "L' = equational_clausal_logic.literal.Neg (Eq s v)" and
    C_def: "C = Ecl (subst_cl C' \<sigma>\<^sub>C) (SuperCalc.get_trms (subst_cl C' \<sigma>\<^sub>C)
      (SuperCalc.dom_trms (subst_cl C' \<sigma>\<^sub>C) (subst_set (trms_ecl P1 \<union> proper_subterms_of t) \<sigma>\<^sub>C))
      SuperCalc.FirstOrder)" and
    C'_def: "C' = cl_ecl P1 - {L2} \<union> {L'}"
    unfolding SuperCalc.factorization_def by metis

  have
    vars_t_subset: "vars_of t \<subseteq> vars_of_cl (cl_ecl P1)" and
    vars_s_subset: "vars_of s \<subseteq> vars_of_cl (cl_ecl P1)"
    using SuperCalc.orient_lit_inst_vars[OF \<open>SuperCalc.orient_lit_inst L1 t s pos \<sigma>\<^sub>C\<close>]
    using \<open>L1 \<in> cl_ecl P1\<close> by (auto dest: vars_of_cl_lem)

  have
    vars_u_subset: "vars_of u \<subseteq> vars_of_cl (cl_ecl P1)" and
    vars_v_subset: "vars_of v \<subseteq> vars_of_cl (cl_ecl P1)"
    using SuperCalc.orient_lit_inst_vars[OF \<open>SuperCalc.orient_lit_inst L2 u v pos \<sigma>\<^sub>C\<close>]
    using \<open>L1 \<in> cl_ecl P1\<close> \<open>L2 \<in> cl_ecl P1 - {L1}\<close> by (auto dest: vars_of_cl_lem)

  have vars_L'_eq: "vars_of_lit L' = vars_of s \<union> vars_of v"
    by (simp add: L'_eq)
  hence vars_L'_subset: "vars_of_lit L' \<subseteq> vars_of_cl (cl_ecl P1)"
    using vars_s_subset vars_v_subset by simp

  from unif_t_u_\<sigma>\<^sub>C have min_IMGU_\<sigma>\<^sub>C: "min_IMGU \<sigma>\<^sub>C t u"
    by (simp add: SuperCalc.ck_unifier_def)
  hence dom_\<sigma>\<^sub>C_subset: "fst ` set \<sigma>\<^sub>C \<subseteq> vars_of t \<union> vars_of u"
    by (simp add: min_IMGU_def)
  hence dom_\<sigma>\<^sub>C_subset_weak: "fst ` set \<sigma>\<^sub>C \<subseteq> vars_of_cl (cl_ecl P1)"
    using vars_t_subset vars_u_subset by auto

  from min_IMGU_\<sigma>\<^sub>C have range_\<sigma>\<^sub>C: "range_vars \<sigma>\<^sub>C \<subseteq> vars_of t \<union> vars_of u"
    by (simp add: min_IMGU_def)
  hence range_\<sigma>\<^sub>C_weak: "range_vars \<sigma>\<^sub>C \<subseteq> vars_of_cl (cl_ecl P1)"
    using vars_t_subset vars_u_subset by auto

  from ren obtain \<rho> where
    ren_\<rho>: "renaming \<rho> (vars_of_cl (cl_ecl P1))" and
    P1'_def: "P1' = subst_ecl P1 \<rho>"
    unfolding renaming_cl_def by blast

  from fin have fin_vars_P1: "finite (vars_of_cl (cl_ecl P1))"
    using set_of_variables_is_finite_cl by blast
  with ren_\<rho> obtain \<rho>_inv where
    \<rho>_\<rho>_inv_ident: "\<forall>x\<in>vars_of_cl (cl_ecl P1). Var x \<lhd> \<rho> \<lhd> \<rho>_inv = Var x" and
      "\<forall>x. x \<notin> subst_codomain \<rho> (vars_of_cl (cl_ecl P1)) \<longrightarrow> Var x \<lhd> \<rho>_inv = Var x" and
      "\<forall>x. is_a_variable (Var x \<lhd> \<rho>_inv)"
    using renamings_admit_inverse by blast

  define \<sigma>\<^sub>D where
    "\<sigma>\<^sub>D = map (map_prod (\<lambda>x. the_Var (Var x \<lhd> \<rho>)) (\<lambda>v. v \<lhd> \<rho>)) \<sigma>\<^sub>C"

  define D' where
    "D' = cl_ecl P1' -
      {equational_clausal_logic.subst_lit L2 \<rho>} \<union>
      {equational_clausal_logic.subst_lit L' \<rho>}"

  define D where
    "D = (let Cl_D = subst_cl D' \<sigma>\<^sub>D in
      Ecl Cl_D (SuperCalc.get_trms Cl_D
        (SuperCalc.dom_trms Cl_D (subst_set (trms_ecl P1' \<union> proper_subterms_of (t \<lhd> \<rho>)) \<sigma>\<^sub>D))
        SuperCalc.FirstOrder))"

  have "t \<lhd> \<rho> \<lhd> \<sigma>\<^sub>D = t \<lhd> \<sigma>\<^sub>C \<lhd> \<rho>"
    using subst_renaming_map_map_prod_eq[of t \<sigma>\<^sub>C \<rho>, folded \<sigma>\<^sub>D_def]
    by (smt (verit, ccfv_SIG) UnE dom_\<sigma>\<^sub>C_subset_weak inj_on_def ren_\<rho>
        renaming_imp_ball_neq_imp_neq_subst renaming_imp_ball_var subsetD vars_t_subset)

  have "u \<lhd> \<rho> \<lhd> \<sigma>\<^sub>D = u \<lhd> \<sigma>\<^sub>C \<lhd> \<rho>"
    using subst_renaming_map_map_prod_eq[of u \<sigma>\<^sub>C \<rho>, folded \<sigma>\<^sub>D_def]
    by (smt (verit, ccfv_SIG) UnE dom_\<sigma>\<^sub>C_subset_weak inj_on_def ren_\<rho>
        renaming_imp_ball_neq_imp_neq_subst renaming_imp_ball_var subsetD vars_u_subset)

  have "s \<lhd> \<rho> \<lhd> \<sigma>\<^sub>D = s \<lhd> \<sigma>\<^sub>C \<lhd> \<rho>"
    using subst_renaming_map_map_prod_eq[of s \<sigma>\<^sub>C \<rho>, folded \<sigma>\<^sub>D_def]
    by (smt (verit, ccfv_SIG) UnE dom_\<sigma>\<^sub>C_subset_weak inj_on_def ren_\<rho>
        renaming_imp_ball_neq_imp_neq_subst renaming_imp_ball_var subsetD vars_s_subset)

  have "v \<lhd> \<rho> \<lhd> \<sigma>\<^sub>D = v \<lhd> \<sigma>\<^sub>C \<lhd> \<rho>"
    using subst_renaming_map_map_prod_eq[of v \<sigma>\<^sub>C \<rho>, folded \<sigma>\<^sub>D_def]
    by (smt (verit, ccfv_SIG) UnE dom_\<sigma>\<^sub>C_subset_weak inj_on_def ren_\<rho>
        renaming_imp_ball_neq_imp_neq_subst renaming_imp_ball_var subsetD vars_v_subset)

  show ?thesis
  proof (intro exI conjI)
    have "SuperCalc.eligible_literal (equational_clausal_logic.subst_lit L1 \<rho>) P1' \<sigma>\<^sub>D"
      unfolding P1'_def
      using eligible_literal_of_renaming[OF eligible_L1 ren_\<rho> \<sigma>\<^sub>D_def _ _ range_\<sigma>\<^sub>C_weak L1_in]
      using inj_on_if_renaming[OF ren_\<rho>] renaming_imp_ball_var[OF ren_\<rho>]
      by (metis L1_in Un_absorb1 dom_\<sigma>\<^sub>C_subset_weak sup.order_iff vars_of_cl_lem)
    moreover have "equational_clausal_logic.subst_lit L1 \<rho> \<in> cl_ecl P1'"
      using L1_in by (simp add: P1'_def cl_ecl_subst_ecl_distrib subst_cl_conv)
    moreover have "equational_clausal_logic.subst_lit L2 \<rho> \<in> cl_ecl P1' -
      {equational_clausal_logic.subst_lit L1 \<rho>}"
    proof -
      from L2_in have "L2 \<in> cl_ecl P1" and "L2 \<noteq> L1"
        by simp_all
      hence "equational_clausal_logic.subst_lit L2 \<rho> \<noteq> equational_clausal_logic.subst_lit L1 \<rho>"
        using inj_subst_lit_if_renaming[OF ren_\<rho>, THEN inj_onD, of L2 L1, simplified]
        using L1_in vars_of_cl_lem by blast

      moreover have "equational_clausal_logic.subst_lit L2 \<rho> \<in> cl_ecl (subst_ecl P1 \<rho>)"
        using \<open>L2 \<in> cl_ecl P1\<close>
        by (simp add: cl_ecl_subst_ecl_distrib subst_cl_conv)

      ultimately show ?thesis
        by (simp add: P1'_def)
    qed
    moreover have "SuperCalc.orient_lit_inst (equational_clausal_logic.subst_lit L1 \<rho>)
      (t \<lhd> \<rho>) (s \<lhd> \<rho>) pos \<sigma>\<^sub>D"
      using orient_L1 unfolding SuperCalc.orient_lit_inst_def
      unfolding \<open>t \<lhd> \<rho> \<lhd> \<sigma>\<^sub>D = t \<lhd> \<sigma>\<^sub>C \<lhd> \<rho>\<close> \<open>s \<lhd> \<rho> \<lhd> \<sigma>\<^sub>D = s \<lhd> \<sigma>\<^sub>C \<lhd> \<rho>\<close>
      apply (elim disjE conjE)
         apply simp_all
      using SuperCalc.trm_ord_subst_renaming[of \<rho> "t \<lhd> \<sigma>\<^sub>C" "s \<lhd> \<sigma>\<^sub>C"]
      apply (smt (verit, ccfv_SIG) dual_order.trans range_\<sigma>\<^sub>C_weak ren_\<rho> sup.boundedI renaming_subset
          vars_of_subst_subset vars_s_subset vars_t_subset)
      using SuperCalc.trm_ord_subst_renaming[of \<rho> "t \<lhd> \<sigma>\<^sub>C" "s \<lhd> \<sigma>\<^sub>C"]
      apply (smt (verit, ccfv_SIG) dual_order.trans range_\<sigma>\<^sub>C_weak ren_\<rho> sup.boundedI renaming_subset
          vars_of_subst_subset vars_s_subset vars_t_subset)
      done
    moreover have "SuperCalc.orient_lit_inst (equational_clausal_logic.subst_lit L2 \<rho>)
      (u \<lhd> \<rho>) (v \<lhd> \<rho>) pos \<sigma>\<^sub>D"
      using orient_L2 unfolding SuperCalc.orient_lit_inst_def
      unfolding \<open>u \<lhd> \<rho> \<lhd> \<sigma>\<^sub>D = u \<lhd> \<sigma>\<^sub>C \<lhd> \<rho>\<close> \<open>v \<lhd> \<rho> \<lhd> \<sigma>\<^sub>D = v \<lhd> \<sigma>\<^sub>C \<lhd> \<rho>\<close>
      apply (elim disjE conjE)
         apply simp_all
      using SuperCalc.trm_ord_subst_renaming[of \<rho> "u \<lhd> \<sigma>\<^sub>C" "v \<lhd> \<sigma>\<^sub>C"]
      apply (smt (verit, ccfv_SIG) dual_order.trans range_\<sigma>\<^sub>C_weak ren_\<rho> sup.boundedI renaming_subset
          vars_of_subst_subset vars_u_subset vars_v_subset)
      using SuperCalc.trm_ord_subst_renaming[of \<rho> "u \<lhd> \<sigma>\<^sub>C" "v \<lhd> \<sigma>\<^sub>C"]
      apply (smt (verit, ccfv_SIG) dual_order.trans range_\<sigma>\<^sub>C_weak ren_\<rho> sup.boundedI renaming_subset
          vars_of_subst_subset vars_u_subset vars_v_subset)
      done
    moreover have "t \<lhd> \<rho> \<lhd> \<sigma>\<^sub>D \<noteq> s \<lhd> \<rho> \<lhd> \<sigma>\<^sub>D"
      unfolding \<open>t \<lhd> \<rho> \<lhd> \<sigma>\<^sub>D = t \<lhd> \<sigma>\<^sub>C \<lhd> \<rho>\<close> \<open>s \<lhd> \<rho> \<lhd> \<sigma>\<^sub>D = s \<lhd> \<sigma>\<^sub>C \<lhd> \<rho>\<close>
      using \<open>t \<lhd> \<sigma>\<^sub>C \<noteq> s \<lhd> \<sigma>\<^sub>C\<close> inj_subst_if_renaming[OF ren_\<rho>, THEN inj_onD, simplified]
      by (meson dual_order.trans le_sup_iff range_\<sigma>\<^sub>C_weak vars_of_subst_subset vars_s_subset
          vars_t_subset)
    moreover have "t \<lhd> \<rho> \<lhd> \<sigma>\<^sub>D \<noteq> v \<lhd> \<rho> \<lhd> \<sigma>\<^sub>D"
      unfolding \<open>t \<lhd> \<rho> \<lhd> \<sigma>\<^sub>D = t \<lhd> \<sigma>\<^sub>C \<lhd> \<rho>\<close> \<open>v \<lhd> \<rho> \<lhd> \<sigma>\<^sub>D = v \<lhd> \<sigma>\<^sub>C \<lhd> \<rho>\<close>
      using \<open>t \<lhd> \<sigma>\<^sub>C \<noteq> v \<lhd> \<sigma>\<^sub>C\<close> inj_subst_if_renaming[OF ren_\<rho>, THEN inj_onD, simplified]
      by (meson dual_order.trans le_sup_iff range_\<sigma>\<^sub>C_weak vars_of_subst_subset vars_v_subset
          vars_t_subset)
    moreover have "SuperCalc.ck_unifier (t \<lhd> \<rho>) (u \<lhd> \<rho>) \<sigma>\<^sub>D SuperCalc.FirstOrder"
      apply (rule ck_unifier_of_renamed_if_ck_unifier[
            OF unif_t_u_\<sigma>\<^sub>C ren_\<rho> \<rho>_\<rho>_inv_ident _ dom_\<sigma>\<^sub>C_subset, folded \<sigma>\<^sub>D_def])
      using vars_t_subset vars_u_subset by simp
    ultimately show "SuperCalc.factorization P1' D \<sigma>\<^sub>D SuperCalc.FirstOrder D'"
      unfolding SuperCalc.factorization_def
      apply -
      apply (rule exI[of _ "equational_clausal_logic.subst_lit L1 \<rho>"])
      apply (rule exI[of _ "equational_clausal_logic.subst_lit L2 \<rho>"])
      apply (rule exI[of _ "equational_clausal_logic.literal.Neg (Eq (s \<lhd> \<rho>) (v \<lhd> \<rho>))"])
      apply (rule exI[of _ "(t \<lhd> \<rho>)"])
      apply (rule exI[of _ "(s \<lhd> \<rho>)"])
      apply (rule exI[of _ "(u \<lhd> \<rho>)"])
      apply (rule exI[of _ "(v \<lhd> \<rho>)"])
      by (simp add: D_def D'_def Let_def L'_eq)
  next
    show "renaming_cl C D"
      unfolding renaming_cl_def
    proof (intro exI conjI)
      have "vars_of_cl (cl_ecl C) = vars_of_cl (subst_cl C' \<sigma>\<^sub>C)"
        by (simp add: C_def)
      also have "... = vars_of_cl (subst_cl (cl_ecl P1 - {L2} \<union> {L'}) \<sigma>\<^sub>C)"
        by (simp add: C'_def)
      also have "... = vars_of_cl (subst_cl (cl_ecl P1 - {L2}) \<sigma>\<^sub>C \<union> subst_cl {L'} \<sigma>\<^sub>C)"
        unfolding subst_cl_union by (rule refl)
      also have "... = vars_of_cl (subst_cl (cl_ecl P1 - {L2}) \<sigma>\<^sub>C) \<union> vars_of_cl (subst_cl {L'} \<sigma>\<^sub>C)"
        by (simp add: vars_of_cl_conv)
      also have "... \<subseteq> vars_of_cl (subst_cl (cl_ecl P1) \<sigma>\<^sub>C) \<union> vars_of_cl (subst_cl {L'} \<sigma>\<^sub>C)"
        by (smt (verit, del_insts) DiffD1 UN_iff Un_iff \<open>L2 \<in> cl_ecl P1 - {L1}\<close> image_insert
            insert_Diff insert_iff subsetI subst_cl_conv vars_of_cl_conv)
      also have "... =
        (\<Union>x \<in> vars_of_cl (cl_ecl P1). vars_of (Var x \<lhd> \<sigma>\<^sub>C)) \<union>
        (\<Union>x \<in> vars_of_lit L'. vars_of (Var x \<lhd> \<sigma>\<^sub>C))"
        unfolding vars_of_subst_cl_conv vars_of_cl_conv[of "{L'}"] by simp
      also have "... \<subseteq> (\<Union>x \<in> vars_of_cl (cl_ecl P1). vars_of (Var x \<lhd> \<sigma>\<^sub>C))"
        using vars_L'_subset by auto
      also have "... \<subseteq> (\<Union>x \<in> vars_of_cl (cl_ecl P1). insert x (range_vars \<sigma>\<^sub>C))"
        using vars_of_subst_subset[of "Var _" \<sigma>\<^sub>C] by auto
      also have "... \<subseteq> vars_of_cl (cl_ecl P1) \<union> range_vars \<sigma>\<^sub>C"
        by blast
      also have "... = vars_of_cl (cl_ecl P1)"
        using range_\<sigma>\<^sub>C_weak by fast
      finally show "renaming \<rho> (vars_of_cl (cl_ecl C))"
        by (rule renaming_subset[OF _ ren_\<rho>])
    next
      have "subst_cl D' \<sigma>\<^sub>D = subst_cl (cl_ecl P1' -
        {equational_clausal_logic.subst_lit L2 \<rho>} \<union>
        {equational_clausal_logic.subst_lit L' \<rho>}) \<sigma>\<^sub>D"
        by (simp add: D'_def)
      also have "... = subst_cl (cl_ecl P1' - subst_cl {L2} \<rho> \<union> subst_cl {L'} \<rho>) \<sigma>\<^sub>D"
        by (simp add: singleton_subst_lit_conv)
      also have "... = subst_cl (subst_cl (cl_ecl P1) \<rho> - subst_cl {L2} \<rho> \<union> subst_cl {L'} \<rho>) \<sigma>\<^sub>D"
        by (simp add: P1'_def cl_ecl_subst_ecl_distrib)
      also have "... = subst_cl (subst_cl (cl_ecl P1 - {L2}) \<rho> \<union> subst_cl {L'} \<rho>) \<sigma>\<^sub>D"
      proof -
        have "inj_on (\<lambda>L. equational_clausal_logic.subst_lit L \<rho>) (cl_ecl P1 \<union> {L2})"
          using inj_subst_lit_if_renaming[OF ren_\<rho>]
          by (rule inj_on_subset)
            (metis (no_types, lifting) CollectI DiffD1 Un_insert_right \<open>L2 \<in> cl_ecl P1 - {L1}\<close>
              insert_Diff insert_Diff_single subsetI sup_bot.right_neutral vars_of_cl_lem)
        thus ?thesis
          using subst_cl_minus_subst_cl_eq_subst_cl_minus[of \<rho> "cl_ecl P1" "{L2}"] by simp
      qed
      also have "... = subst_cl (subst_cl (cl_ecl P1 - {L2} \<union> {L'}) \<rho>) \<sigma>\<^sub>D"
        unfolding subst_cl_union by (rule refl)
      also have "... = subst_cl (subst_cl (cl_ecl P1 - {L2} \<union> {L'}) \<sigma>\<^sub>C) \<rho>"
      proof (rule subst_cl_renaming_map_map_prod_eq[of _ \<sigma>\<^sub>C \<rho>, folded \<sigma>\<^sub>D_def])
        have "vars_of_lit L' \<subseteq> vars_of_cl (cl_ecl P1)"
          using \<open>L1 \<in> cl_ecl P1\<close> \<open>L2 \<in> cl_ecl P1 - {L1}\<close>
          using \<open>SuperCalc.orient_lit_inst L1 t s pos \<sigma>\<^sub>C\<close> \<open>SuperCalc.orient_lit_inst L2 u v pos \<sigma>\<^sub>C\<close>
          unfolding L'_eq vars_of_lit.simps vars_of_eq.simps
          by (metis (no_types, lifting) DiffD1 SuperCalc.orient_lit_inst_vars le_sup_iff
              subset_trans vars_of_cl_lem)
        hence "vars_of_cl (cl_ecl P1 - {L2} \<union> {L'}) \<subseteq> vars_of_cl (cl_ecl P1)"
          unfolding vars_of_cl_conv by blast
        thus "\<forall>x \<in> vars_of_cl (cl_ecl P1 - {L2} \<union> {L'}) \<union> fst ` set \<sigma>\<^sub>C. is_a_variable (Var x \<lhd> \<rho>)"
          using renaming_imp_ball_var[OF ren_\<rho>] dom_\<sigma>\<^sub>C_subset_weak by blast
      next
        show "inj_on (\<lambda>x. Var x \<lhd> \<rho>) (vars_of_cl (cl_ecl P1 - {L2} \<union> {L'}) \<union> fst ` set \<sigma>\<^sub>C)"
          apply (rule inj_on_if_renaming[OF ren_\<rho>, THEN inj_on_subset])
          using vars_L'_subset dom_\<sigma>\<^sub>C_subset_weak
          by (simp add: vars_of_cl_conv Union_mono image_mono)
      qed
      finally have "subst_cl D' \<sigma>\<^sub>D = subst_cl (subst_cl C' \<sigma>\<^sub>C) \<rho>"
        by (simp add: C'_def)
      thus "D = subst_ecl C \<rho>"
        unfolding C_def subst_ecl.simps D_def Let_def
        by (simp add: SuperCalc.get_trms_def)
    qed
  qed
qed

lemma superposition_if_renaming:
  fixes \<sigma>
  assumes
    super: "SuperCalc.superposition P1 P2 C \<sigma>\<^sub>C SuperCalc.FirstOrder C'" and
    ren: "renaming_cl P1 P1'" "renaming_cl P2 P2'" and
    fin: "finite (cl_ecl P1)" "finite (cl_ecl P2)" (* and
    "variable_disjoint P1' P2'" *)
  shows "\<exists>D \<sigma>\<^sub>D D'. SuperCalc.superposition P1' P2' D \<sigma>\<^sub>D SuperCalc.FirstOrder D' \<and> renaming_cl C D"
proof -
  from super obtain L M u' p t u v s polarity t' L' where
    L_in: "L \<in> cl_ecl P1" and
    M_in: "M \<in> cl_ecl P2" and
    eligible_L: "SuperCalc.eligible_literal L P1 \<sigma>\<^sub>C" and
    eligible_M: "SuperCalc.eligible_literal M P2 \<sigma>\<^sub>C" and
    var_disj_P1_P2: "variable_disjoint P1 P2" and
    "\<not> is_a_variable u'" and
    "SuperCalc.allowed_redex u' P1 \<sigma>\<^sub>C" and
    "C = Ecl (subst_cl C' \<sigma>\<^sub>C) (SuperCalc.get_trms (subst_cl C' \<sigma>\<^sub>C)
      (SuperCalc.dom_trms (subst_cl C' \<sigma>\<^sub>C) (subst_set (trms_ecl P1 \<union> trms_ecl P2 \<union>
        {r. \<exists>q. (q, p) \<in> pos_ord P1 t \<and> subterm t q r}) \<sigma>\<^sub>C)) SuperCalc.FirstOrder)" and
    "SuperCalc.orient_lit_inst M u v pos \<sigma>\<^sub>C" and
    "SuperCalc.orient_lit_inst L t s polarity \<sigma>\<^sub>C" and
    "u \<lhd> \<sigma>\<^sub>C \<noteq> v \<lhd> \<sigma>\<^sub>C" and
    "subterm t p u'" and
    "SuperCalc.ck_unifier u' u \<sigma>\<^sub>C SuperCalc.FirstOrder" and
    "replace_subterm t p v t'" and
    "L' = mk_lit polarity (Eq t' s)" and
    "C' = cl_ecl P1 - {L} \<union> (cl_ecl P2 - {M} \<union> {L'})"
    unfolding SuperCalc.superposition_def
    by blast

  from ren obtain \<rho>\<^sub>1 \<rho>\<^sub>2 where
    ren_\<rho>\<^sub>1: "renaming \<rho>\<^sub>1 (vars_of_cl (cl_ecl P1))" and
    ren_\<rho>\<^sub>2: "renaming \<rho>\<^sub>2 (vars_of_cl (cl_ecl P2))" and
    P1'_def: "P1' = subst_ecl P1 \<rho>\<^sub>1" and
    P2'_def: "P2' = subst_ecl P2 \<rho>\<^sub>2"
    unfolding renaming_cl_def by blast

  define min_\<rho>\<^sub>1 where
    "min_\<rho>\<^sub>1 = filter (\<lambda>p. fst p \<in> vars_of_cl (cl_ecl P1)) \<rho>\<^sub>1"

  define min_\<rho>\<^sub>2 where
    "min_\<rho>\<^sub>2 = filter (\<lambda>p. fst p \<in> vars_of_cl (cl_ecl P2)) \<rho>\<^sub>2"

  define \<rho> where
    "\<rho> = min_\<rho>\<^sub>1 @ min_\<rho>\<^sub>2"

  have dom_filter_\<rho>\<^sub>1:
    "fst ` set min_\<rho>\<^sub>1 \<subseteq> vars_of_cl (cl_ecl P1)"
    unfolding min_\<rho>\<^sub>1_def by force

  have dom_filter_\<rho>\<^sub>2:
    "fst ` set min_\<rho>\<^sub>2 \<subseteq> vars_of_cl (cl_ecl P2)"
    unfolding min_\<rho>\<^sub>2_def by force

  have subst_append_keep_left:
    "t \<lhd> \<sigma>\<^sub>1 @ \<sigma>\<^sub>2 = t \<lhd> \<sigma>\<^sub>1"
    if "vars_of t \<subseteq> fst ` set \<sigma>\<^sub>1" and "fst ` set \<sigma>\<^sub>1 \<inter> fst ` set \<sigma>\<^sub>2 = {}" for t \<sigma>\<^sub>1 \<sigma>\<^sub>2
  proof -
    from that have "vars_of t \<inter> fst ` set \<sigma>\<^sub>2 = {}"
      by auto
    thus ?thesis
      by (simp add: subst_append_remove_right)
  qed

  have vars_P1_disj_dom_min_\<rho>\<^sub>2: "vars_of_cl (cl_ecl P1) \<inter> fst ` set min_\<rho>\<^sub>2 = {}"
    using var_disj_P1_P2 dom_filter_\<rho>\<^sub>2 by (auto simp: variable_disjoint_def)

  have ren_\<rho>: "renaming \<rho> (vars_of_cl (cl_ecl P1) \<union> vars_of_cl (cl_ecl P2))"
    unfolding renaming_def
  proof (intro ballI conjI allI impI)
    fix x assume "x \<in> vars_of_cl (cl_ecl P1) \<union> vars_of_cl (cl_ecl P2)"
    then show "is_a_variable (Var x \<lhd> \<rho>)"
      unfolding Set.Un_iff
    proof (elim disjE)
      assume x_in: "x \<in> vars_of_cl (cl_ecl P1)"
      hence "is_a_variable (Var x \<lhd> \<rho>\<^sub>1)"
        using renaming_imp_ball_var[OF ren_\<rho>\<^sub>1] by simp
      then show "is_a_variable (Var x \<lhd> \<rho>)"
        unfolding \<rho>_def min_\<rho>\<^sub>1_def
      proof (induction \<rho>\<^sub>1)
        case Nil
        thus ?case
          using x_in subst_ident_if_vars_distinct_dom[of "Var x" min_\<rho>\<^sub>2] vars_P1_disj_dom_min_\<rho>\<^sub>2
          by force
      next
        case (Cons p \<rho>\<^sub>1)
        then show ?case
          by (smt (verit, ccfv_SIG) append_Cons assoc.elims assoc.simps(2) filter.simps(2) fst_conv
              list.discI list.inject subst.simps(1) x_in)
      qed
    next
      assume x_in: "x \<in> vars_of_cl (cl_ecl P2)"
      hence "is_a_variable (Var x \<lhd> \<rho>\<^sub>2)"
        using renaming_imp_ball_var[OF ren_\<rho>\<^sub>2] by simp
      hence "is_a_variable (Var x \<lhd> min_\<rho>\<^sub>2)"
        unfolding min_\<rho>\<^sub>2_def
        apply (induction \<rho>\<^sub>2)
         apply simp
        using x_in by force

      moreover from x_in have "x \<notin> fst ` set min_\<rho>\<^sub>1"
        by (metis IntI dom_filter_\<rho>\<^sub>1 empty_iff subsetD var_disj_P1_P2 variable_disjoint_def)

      ultimately show "is_a_variable (Var x \<lhd> \<rho>)"
        unfolding \<rho>_def
        using subst_append_remove_left[of "Var x" min_\<rho>\<^sub>1 min_\<rho>\<^sub>2, simplified]
        by simp
    qed
  next
    fix x y
    assume
      "x \<in> vars_of_cl (cl_ecl P1) \<union> vars_of_cl (cl_ecl P2)"
      "y \<in> vars_of_cl (cl_ecl P1) \<union> vars_of_cl (cl_ecl P2)"
    show "x \<noteq> y \<Longrightarrow> Var x \<lhd> \<rho> \<noteq> Var y \<lhd> \<rho>"
      unfolding \<rho>_def
      using inj_subst_if_renaming[OF ren_\<rho>\<^sub>1]
        inj_subst_if_renaming[OF ren_\<rho>\<^sub>2, THEN inj_onD, simplified]
      
      sorry
  qed

  thm var_disj_P1_P2

  (* define \<sigma>\<^sub>D where
    "\<sigma>\<^sub>D = map (map_prod (\<lambda>x. the_Var (Var x \<lhd> \<rho>)) (\<lambda>v. v \<lhd> \<rho>)) \<sigma>\<^sub>C" *)

  show ?thesis
    sorry
qed

lemma derivable_list_if_renaming:
  fixes \<sigma>
  assumes
    deriv: "derivable_list C Ps \<sigma>\<^sub>C SuperCalc.FirstOrder C'" and
    ren: "list_all2 renaming_cl Ps Ps'" and
    fin: "list_all (finite \<circ> cl_ecl) Ps"
  shows "\<exists>D \<sigma>\<^sub>D D'. derivable_list D Ps' \<sigma>\<^sub>D SuperCalc.FirstOrder D' \<and> renaming_cl C D"
  using deriv[unfolded derivable_list_def]
proof (elim disjE exE conjE)
  fix P1 P2
  assume
    Ps_def: "Ps = [P2, P1]" and
    super: "SuperCalc.superposition P1 P2 C \<sigma>\<^sub>C SuperCalc.FirstOrder C'"
  
  from ren obtain P2' P1' where
    "Ps' = [P2', P1']" and "renaming_cl P2 P2'" and "renaming_cl P1 P1'"
    using Ps_def
    by (metis (no_types, opaque_lifting) list.rel_distinct(2) list.rel_inject(2) list_all2_Nil
        neq_Nil_conv)
  moreover from fin have "finite (cl_ecl P1)" and "finite (cl_ecl P2)"
    using Ps_def by auto
  ultimately show ?thesis
    using superposition_if_renaming[OF super, of P1' P2'] derivable_list_def by blast
next
  fix P1
  assume
    Ps_def: "Ps = [P1]" and
    fact: "SuperCalc.factorization P1 C \<sigma>\<^sub>C SuperCalc.FirstOrder C'"

  from ren obtain P1' where
    "Ps' = [P1']" and "renaming_cl P1 P1'"
    using Ps_def
    by (metis (no_types, opaque_lifting) list.rel_distinct(2) list.rel_inject(2) list_all2_Nil
        neq_Nil_conv)
  moreover from fin have "finite (cl_ecl P1)"
    using Ps_def by auto
  ultimately show ?thesis
    using factorization_if_renaming[OF fact, of P1'] derivable_list_def by blast
next
  fix P1
  assume
    Ps_def: "Ps = [P1]" and
    fact: "SuperCalc.reflexion P1 C \<sigma>\<^sub>C SuperCalc.FirstOrder C'"

  from ren obtain P1' where
    "Ps' = [P1']" and "renaming_cl P1 P1'"
    using Ps_def
    by (metis (no_types, opaque_lifting) list.rel_distinct(2) list.rel_inject(2) list_all2_Nil
        neq_Nil_conv)
  moreover from fin have "finite (cl_ecl P1)"
    using Ps_def by auto
  ultimately show ?thesis
    using reflexion_if_renaming[OF fact, of P1'] derivable_list_def by blast
qed


subsubsection \<open>First-Order Calculus\<close>

text \<open>
Renaming is performed here in order to keep @{const G_derivable_list} as similar as possible to
@{const SuperCalc.derivable}. Renaming would not strictly be necessary for
@{const SuperCalc.factorization} and @{const SuperCalc.reflexion}, but it does not hurt either.
\<close>

definition F_Inf :: "'a fclause inference set" where
  "F_Inf \<equiv> {Infer Ps (Abs_fset (subst_cl C' \<sigma>)) | Ps C \<sigma> C'.
    let Ps' = map2 (\<lambda>D \<rho>. Ecl (subst_cl (fset D) \<rho>) {}) Ps (renamings_apart Ps) in
    derivable_list C Ps' \<sigma> SuperCalc.FirstOrder C'}"

lemma F_Inf_have_prems: "\<iota> \<in> F_Inf \<Longrightarrow> prems_of \<iota> \<noteq> []"
  by (auto simp: F_Inf_def derivable_list_def)

interpretation F: inference_system F_Inf .

definition \<G>_F :: "'a fclause \<Rightarrow> 'a fclause set" where
  "\<G>_F C \<equiv> {Abs_fset (subst_cl (fset C) \<gamma>) | \<gamma>. ground_on (vars_of_cl (fset C)) \<gamma>}"

lemma \<G>_F_mempty[simp]: "\<G>_F {||} = {{||}}"
  using ground_subst_exists[OF finite.emptyI]
  by (simp add: \<G>_F_def vars_of_cl.simps ground_on_def)

definition \<G>_I where
  "\<G>_I M \<iota> \<equiv> {\<iota>' \<in> G_Inf M.
    (\<exists>\<gamma>s. prems_of \<iota>' = map2 (\<lambda>D \<gamma>. Abs_fset (subst_cl (fset D) \<gamma>)) (prems_of \<iota>) \<gamma>s \<and>
      length (prems_of \<iota>) = length \<gamma>s) \<and>
    (\<exists>\<gamma>. concl_of \<iota>' = Abs_fset (subst_cl (fset (concl_of \<iota>)) \<gamma>))}"

lemma grounding_of_inferences_are_grounded_inferences: "\<iota> \<in> F_Inf \<Longrightarrow> \<iota>' \<in> \<G>_I M \<iota> \<Longrightarrow> \<iota>' \<in> G_Inf M"
  by (simp add: \<G>_I_def)


interpretation F: lifting_intersection F_Inf "{{||}}" UNIV G_Inf "\<lambda>_. (\<TTurnstile>e)" G.Red_I "\<lambda>_. G.Red_F"
  "{{||}}" "\<lambda>_. \<G>_F" "\<lambda>M. Some \<circ> \<G>_I M" "\<lambda>_ _ _. False"
proof (unfold_locales; (intro ballI)?)
  show "UNIV \<noteq> {}"
    by (rule UNIV_not_empty)
next
  show "consequence_relation {{||}} (\<TTurnstile>e)"
    by (rule G.consequence_relation_axioms)
next
  show "\<And>M. tiebreaker_lifting {{||}} F_Inf {{||}} (\<TTurnstile>e) (G_Inf M) (G.Red_I M) G.Red_F \<G>_F
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

      obtain \<gamma> where concl_\<iota>'_conv:"concl_of \<iota>' = Abs_fset (subst_cl (fset (concl_of \<iota>)) \<gamma>)"
        using \<iota>'_grounding[unfolded \<G>_I_def mem_Collect_eq] by metis
      
      show "\<iota>' \<in> G.Red_I M (\<G>_F (concl_of \<iota>))"
        apply (rule G.Red_I_of_Inf_to_N[OF \<iota>'_in])
        unfolding \<G>_F_def Let_def mem_Collect_eq
      proof (intro exI[of _ \<gamma>] conjI)
        show "concl_of \<iota>' = Abs_fset (subst_cl (fset (concl_of \<iota>)) \<gamma>)"
          by (rule concl_\<iota>'_conv)
      next
        show "ground_on (vars_of_cl (fset (concl_of \<iota>))) \<gamma>"
          by (metis Abs_fset_inverse G_Inf_ground_concl \<iota>'_in concl_\<iota>'_conv finite_fset
              ground_clauses_and_ground_substs mem_Collect_eq substs_preserve_finiteness)
      qed
    qed
    thus "the ((Some \<circ> \<G>_I M) \<iota>) \<subseteq> G.Red_I M (\<G>_F (concl_of \<iota>))"
      by simp
  next
    show "po_on (\<lambda>_ _. False) UNIV"
      by (simp add: irreflp_onI po_onI transp_onI)
  next
    show "\<And>M C. \<G>_F C \<inter> {{||}} \<noteq> {} \<longrightarrow> C \<in> {{||}}"
      unfolding \<G>_F_def
      apply simp
      by (metis Abs_fset_inverse bot_fset.rep_eq fimage.rep_eq fset fset_cong image_is_empty
          subst_cl_conv)
  qed auto
qed

lemma vars_of_cl_subst_cl_conv:
  fixes C \<sigma>
  shows "vars_of_cl (subst_cl C \<sigma>) = \<Union>((\<lambda>v. vars_of (assoc v (Var v) \<sigma>)) ` vars_of_cl C)"
    (is "?lhs = ?rhs")
proof (rule Set.equalityI; rule Set.subsetI)
  fix x
  assume "x \<in> ?lhs"
  then obtain L where x_in_L: "x \<in> vars_of_lit L" and L_in_subst_C: "L \<in> subst_cl C \<sigma>"
    by (auto simp: vars_of_cl.simps)
  obtain L' where L'_in_C: "L' \<in> C" and L_def: "L = equational_clausal_logic.subst_lit L' \<sigma>"
    using L_in_subst_C by (auto simp: subst_cl.simps)
  then show "x \<in> ?rhs"
    using x_in_L by (auto simp: vars_of_lit_subst_lit_conv vars_of_cl.simps)
next
  fix x
  assume "x \<in> ?rhs"
  then obtain L v where
    L_in_C: "L \<in> C " and
    v_in_vars_C: "v \<in> vars_of_lit L" and
    x_in_vars_v_\<sigma>: "x \<in> vars_of (assoc v (Var v) \<sigma>)"
    by (auto simp: vars_of_cl.simps)
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
    by (auto simp: vars_of_cl.simps)
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
    by (auto simp: vars_of_cl.simps)
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

lemma closed_under_renaming_closure:
  fixes N N'
  defines "N' \<equiv> {Abs_fset (subst_cl (fset C) \<sigma>) |C \<sigma>. C \<in> N \<and> renaming \<sigma> (vars_of_cl (fset C))}"
  shows "closed_under_renaming ((\<lambda>C. Ecl (fset C) {}) ` N')"
  unfolding closed_under_renaming_def
proof (intro allI impI)
  fix C D
  assume "C \<in> (\<lambda>C. Ecl (fset C) {}) ` N'"
  then obtain CC \<sigma> where
    C_def: "C = Ecl (subst_cl (fset CC) \<sigma>) {}" and
    "CC \<in> N" and
    renaming_\<sigma>: "renaming \<sigma> (vars_of_cl (fset CC))"
    unfolding N'_def
    by (smt (verit, ccfv_threshold) Abs_fset_inverse fimage.rep_eq fset imageE mem_Collect_eq
        subst_cl_conv)

  assume "renaming_cl C D"
  then obtain \<eta> where
    renaming_\<eta>: "renaming \<eta> (vars_of_cl (subst_cl (fset CC) \<sigma>))" and
    D_def: "D = subst_ecl C \<eta>"
    unfolding renaming_cl_def
    unfolding C_def cl_ecl.simps
    by blast

  show "D \<in> (\<lambda>C. Ecl (fset C) {}) ` N'"
    unfolding image_iff
  proof (rule bexI)
    show "D = Ecl (fset (Abs_fset (subst_cl (subst_cl (fset CC) \<sigma>) \<eta>))) {}"
      by (simp add: D_def C_def Abs_fset_inverse substs_preserve_finiteness)
  next
    show "Abs_fset (subst_cl (subst_cl (fset CC) \<sigma>) \<eta>) \<in> N'"
      unfolding N'_def
    proof (intro CollectI exI conjI)
      show "CC \<in> N"
        by (rule \<open>CC \<in> N\<close>)
    next
      have "\<forall>x\<in>vars_of_cl (fset CC). is_a_variable (Var x \<lhd> \<sigma> \<lozenge> \<eta>)"
        using renaming_imp_ball_var[OF renaming_\<sigma>]
        using renaming_imp_ball_var[OF renaming_\<eta>]
        by (fact is_a_variable_subst_comp)

      moreover have "Var x \<lhd> \<sigma> \<lozenge> \<eta> \<noteq> Var y \<lhd> \<sigma> \<lozenge> \<eta>"
        if x_in_vars_CC: "x \<in> vars_of_cl (fset CC)" and
           y_in_vars_CC: "y \<in> vars_of_cl (fset CC)" and
           "x \<noteq> y"
        for x y
      proof -
        from that have x_\<sigma>_neq_y_\<sigma>: "Var x \<lhd> \<sigma> \<noteq> Var y \<lhd> \<sigma>"
          using renaming_imp_ball_neq_imp_neq_subst[OF renaming_\<sigma>] by simp

        have "is_a_variable (Var x \<lhd> \<sigma>)" and "is_a_variable (Var y \<lhd> \<sigma>)"
          using renaming_imp_ball_var[OF renaming_\<sigma>] x_in_vars_CC y_in_vars_CC by simp_all
        then obtain x' y' where
          x_subst_def: "(Var x \<lhd> \<sigma>) = Var x'" and
          y_subst_def: "(Var y \<lhd> \<sigma>) = Var y'"
          by (meson is_a_variable.elims(2))

        show "Var x \<lhd> \<sigma> \<lozenge> \<eta> \<noteq> Var y \<lhd> \<sigma> \<lozenge> \<eta> "
          unfolding Unification.subst_comp
          unfolding x_subst_def y_subst_def
          using renaming_imp_ball_neq_imp_neq_subst[OF renaming_\<eta>]
          using in_vars_of_cl_subst_cl[OF x_in_vars_CC x_subst_def]
          using in_vars_of_cl_subst_cl[OF y_in_vars_CC y_subst_def]
          using x_\<sigma>_neq_y_\<sigma>[unfolded x_subst_def y_subst_def]
          by simp
      qed

      ultimately show "renaming (\<sigma> \<lozenge> \<eta>) (vars_of_cl (fset CC))"
        unfolding renaming_def by simp
    next
      show "Abs_fset (subst_cl (subst_cl (fset CC) \<sigma>) \<eta>) = Abs_fset (subst_cl (fset CC) (\<sigma> \<lozenge> \<eta>))"
        by (simp add: composition_of_substs_cl)
    qed
  qed
qed

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
    "length ys = length zs" and "xs = map2 f ys zs" and "list_all2 P ys zs"
    by auto
  moreover from Cons.prems obtain y z where "x = f y z" and "P y z"
    by auto
  ultimately show ?case
    apply -
    by (rule exI[where x = "y # ys"], rule exI[where x = "z # zs"]) simp
qed

lemma map_eq_ConsD: "map f xs = y # ys \<Longrightarrow> \<exists>x xs'. xs = x # xs'"
  by (induction xs) simp_all

lemma saturated_renamings:
  assumes "F.saturated N"
  defines "N' \<equiv> {Abs_fset (subst_cl (fset C) \<sigma>) | C \<sigma>. C \<in> N \<and> renaming \<sigma> (vars_of_cl (fset C))}"
  shows "F.saturated N'"
proof -
  have "N \<subseteq> N'"
  proof (rule Set.subsetI)
    fix C
    show "C \<in> N \<Longrightarrow> C \<in> N'"
      unfolding N'_def Set.mem_Collect_eq
      by (metis SuperCalc.renaming_Nil assoc.simps(1) fset_inverse subst_cl_ident)
  qed

  from \<open>F.saturated N\<close> have sat_N_alt: "\<And>\<iota>. \<iota> \<in> F_Inf \<Longrightarrow> set (prems_of \<iota>) \<subseteq> N \<Longrightarrow> \<iota> \<in> F.Red_I_\<G> N"
    unfolding F.saturated_def F.Inf_from_def
    by (auto dest: Set.subsetD)

  show ?thesis
    unfolding F.saturated_def
  proof (rule Set.subsetI)
    fix \<iota>' :: "'a fclause inference"
    assume "\<iota>' \<in> F.Inf_from N'"
    hence \<iota>'_in: "\<iota>' \<in> F_Inf" and prems_\<iota>'_subset: "set (prems_of \<iota>') \<subseteq> N'"
      unfolding F.Inf_from_def Set.mem_Collect_eq by simp_all

    let ?map_prems = "\<lambda>Ps. map2 (\<lambda>D \<rho>. Ecl (subst_cl (fset D) \<rho>) {}) Ps (renamings_apart Ps)"

    from \<iota>'_in obtain C \<sigma>\<^sub>C C' where
      concl_of_\<iota>': "concl_of \<iota>' = Abs_fset (subst_cl C' \<sigma>\<^sub>C)" and
      deriv_prems_\<iota>': "derivable_list C (?map_prems (prems_of \<iota>')) \<sigma>\<^sub>C SuperCalc.FirstOrder C'"
      unfolding F_Inf_def mem_Collect_eq Let_def by force

    let ?prems_vars = "\<Union>(vars_of_cl ` cl_ecl ` set (?map_prems (prems_of \<iota>')))"

    from prems_\<iota>'_subset obtain Ps \<rho>s where
      prems_\<iota>'_def: "prems_of \<iota>' = map2 (\<lambda>C \<rho>. Abs_fset (subst_cl (fset C) \<rho>)) Ps \<rho>s" and
      "length Ps = length \<rho>s" and
      FOO: "list_all2 (\<lambda>C \<sigma>. C \<in> N \<and> renaming \<sigma> (vars_of_cl (fset C))) Ps \<rho>s"
      unfolding N'_def Ball_Collect[symmetric]
      by (auto dest: ex_eq_map2_if_ball_set_eq)

    from deriv_prems_\<iota>'[unfolded derivable_list_def] have
      "\<exists>D \<sigma>\<^sub>D D'. derivable_list D (?map_prems Ps) \<sigma>\<^sub>D SuperCalc.FirstOrder D' \<and> renaming_cl C D"
    proof (elim disjE exE conjE)
      fix P1
      assume
        prems_eq_P1: "?map_prems (prems_of \<iota>') = [P1]" and
        refl_P1: "SuperCalc.reflexion P1 C \<sigma>\<^sub>C SuperCalc.FirstOrder C'"

      from prems_eq_P1 have "Suc 0 = length (?map_prems (prems_of \<iota>'))"
        by simp
      also have "... = length (zip (prems_of \<iota>') (renamings_apart (prems_of \<iota>')))"
        by simp
      also have "... = min (length (prems_of \<iota>')) (length (renamings_apart (prems_of \<iota>')))"
        by simp
      also have "... = length (prems_of \<iota>')"
        by (simp add: renamings_apart_length[of "prems_of \<iota>'"])
      finally have "length Ps = Suc 0 \<and> length \<rho>s = Suc 0"
        using \<open>length Ps = length \<rho>s\<close> by (simp add: prems_\<iota>'_def)
      then obtain P1' \<rho> where
        Ps_def: "Ps = [P1']" and \<rho>s_def: "\<rho>s = [\<rho>]"
        by (metis Suc_length_conv length_0_conv)
      then obtain \<rho>1 where
        renamings_P1'_\<rho>: "renamings_apart [Abs_fset (subst_cl (fset P1') \<rho>)] = [\<rho>1]"
        using renamings_apart_length[of "prems_of \<iota>'"]
        using prems_\<iota>'_def
        by (smt (verit, del_insts) Suc_length_conv length_0_conv renamings_apart_length)

      have ren_\<rho>_\<rho>1: "renaming (\<rho> \<lozenge> \<rho>1) (vars_of_cl (fset P1'))"
      proof (rule renaming_subst_compI)
        show "renaming \<rho> (vars_of_cl (fset P1'))"
          using FOO by (simp add: Ps_def \<rho>s_def)
      next
        have "list_all2 (\<lambda>C \<rho>. renaming \<rho> (vars_of_cl (fset C))) [Abs_fset (subst_cl (fset P1') \<rho>)] [\<rho>1]"
          using renamings_apart_renaming[of "[Abs_fset (subst_cl (fset P1') \<rho>)]"]
          by (simp add: renamings_P1'_\<rho>)
        hence "renaming \<rho>1 (vars_of_cl (subst_cl (fset P1') \<rho>))"
          using Abs_fset_inverse substs_preserve_finiteness[of "fset P1'" \<rho>, simplified]
          by fastforce
        then show "renaming \<rho>1 (subst_codomain \<rho> (vars_of_cl (fset P1')))"
          unfolding subst_codomain_def
          by (smt (verit, best) in_vars_of_cl_subst_cl mem_Collect_eq renaming_def)
      qed

      from prems_eq_P1 have P1_def: "P1 = Ecl (subst_cl (subst_cl (fset P1') \<rho>) \<rho>1) {}"
        by (simp add: prems_\<iota>'_def Ps_def \<rho>s_def renamings_P1'_\<rho> Abs_fset_inverse
            substs_preserve_finiteness)

      have renaming_P1_P1': "renaming_cl P1 (Ecl (fset P1') {})"
      proof (rule renaming_cl_commutative)
        show "renaming_cl (Ecl (fset P1') {}) P1"
          unfolding P1_def renaming_cl_def
          apply (rule exI[of _ "\<rho> \<lozenge> \<rho>1"])
          using ren_\<rho>_\<rho>1 by (simp add: composition_of_substs_cl)
      qed simp_all

      have fin_P1: "finite (cl_ecl P1)"
        unfolding P1_def by (simp add: substs_preserve_finiteness)

      have prems_vars_subset: "?prems_vars \<subseteq> vars_of_cl (cl_ecl P1)"
        unfolding prems_eq_P1 by simp

      obtain \<rho>2 where renamings_P1': "renamings_apart [P1'] = [\<rho>2]"
        by (metis length_0_conv length_Suc_conv renamings_apart_length)
      hence ren_\<rho>2: "renaming \<rho>2 (vars_of_cl (fset P1'))"
        using renamings_apart_renaming by (metis list.rel_inject(2))

      obtain \<rho>2_inv where
        \<rho>2_\<rho>2_inv_ident: "(\<forall>x\<in>vars_of_cl (fset P1'). Var x \<lhd> \<rho>2 \<lhd> \<rho>2_inv = Var x)" and
        "(\<forall>x. x \<notin> subst_codomain \<rho>2 (vars_of_cl (fset P1')) \<longrightarrow> Var x \<lhd> \<rho>2_inv = Var x)" and
        all_\<rho>2_inv_vars: "\<forall>x. is_a_variable (Var x \<lhd> \<rho>2_inv)"
        using renamings_admit_inverse[OF _ ren_\<rho>2]
        using set_of_variables_is_finite_cl[OF finite_fset]
        by blast

      have ren_P1: "renaming_cl P1 (Ecl (subst_cl (fset P1') \<rho>2) {})"
      proof (rule renaming_cl_commutative)
        show "renaming_cl (Ecl (subst_cl (fset P1') \<rho>2) {}) P1"
          unfolding renaming_cl_def
        proof (intro exI[of _ "\<rho>2_inv \<lozenge> \<rho> \<lozenge> \<rho>1"] conjI)
          show "P1 = subst_ecl (Ecl (subst_cl (fset P1') \<rho>2) {}) (\<rho>2_inv \<lozenge> \<rho> \<lozenge> \<rho>1)"
            unfolding P1_def
            apply (simp add: composition_of_substs_cl[symmetric])
            by (metis \<rho>2_\<rho>2_inv_ident order_refl subst_cl_identI)
        next
          show "renaming (\<rho>2_inv \<lozenge> \<rho> \<lozenge> \<rho>1) (vars_of_cl (cl_ecl (Ecl (subst_cl (fset P1') \<rho>2) {})))"
            unfolding cl_ecl.simps
            unfolding renaming_def
          proof (intro ballI conjI allI impI)
            show "\<And>x. x \<in> vars_of_cl (subst_cl (fset P1') \<rho>2) \<Longrightarrow>
              is_a_variable (Var x \<lhd> \<rho>2_inv \<lozenge> \<rho> \<lozenge> \<rho>1)"
              using ren_\<rho>_\<rho>1
              by (metis (no_types, opaque_lifting) all_\<rho>2_inv_vars \<rho>2_\<rho>2_inv_ident
                  is_a_variable_subst_comp order_refl renaming_def subst_cl_identI subst_comp)
          next
            fix x y
            assume
              "x \<in> vars_of_cl (subst_cl (fset P1') \<rho>2)" and
              "y \<in> vars_of_cl (subst_cl (fset P1') \<rho>2)"
            then obtain x' y' where
              x'_in: "x' \<in> vars_of_cl (fset P1')" and "Var x = Var x' \<lhd> \<rho>2" and
              y'_in: "y' \<in> vars_of_cl (fset P1')" and "Var y = Var y' \<lhd> \<rho>2"
              by (meson ex_subst_var_in_vars_if_in_vars_subst_cl ren_\<rho>2 renaming_imp_ball_var)
            then show "x \<noteq> y \<Longrightarrow> Var x \<lhd> \<rho>2_inv \<lozenge> \<rho> \<lozenge> \<rho>1 \<noteq> Var y \<lhd> \<rho>2_inv \<lozenge> \<rho> \<lozenge> \<rho>1"
              using ren_\<rho>_\<rho>1 \<rho>2_\<rho>2_inv_ident
              by (metis renaming_imp_ball_neq_imp_neq_subst subst_comp trm.inject(1))
          qed
        qed
      qed (simp_all add: substs_preserve_finiteness)

      show ?thesis
        unfolding Ps_def renamings_P1'
        apply simp
        using reflexion_if_renaming[OF refl_P1 ren_P1 fin_P1]
        using derivable_list_def
        by blast
    next
      show ?thesis sorry
    next
      show ?thesis sorry
    qed
    then obtain D D' \<sigma>\<^sub>D where
      deriv_Ps: "derivable_list D (map2 (\<lambda>D \<rho>. Ecl (subst_cl (fset D) \<rho>) {}) Ps
        (renamings_apart Ps)) \<sigma>\<^sub>D SuperCalc.FirstOrder D'" and
      "renaming_cl C D"
      by blast

    from deriv_prems_\<iota>' have "cl_ecl C = subst_cl C' \<sigma>\<^sub>C"
      using derivable_list_concl_conv by blast

    have "finite C'"
      apply (rule derivable_list_finite_conclusion[OF _ deriv_prems_\<iota>'])
      apply simp
      apply (rule ballI)
      subgoal for p
        apply (cases p)
        by (simp add: comp_def substs_preserve_finiteness)
      done
    hence "finite (subst_cl C' \<sigma>\<^sub>C)"
      by (rule substs_preserve_finiteness)
    hence "finite (cl_ecl C)"
      unfolding \<open>cl_ecl C = subst_cl C' \<sigma>\<^sub>C\<close> by assumption

    have "finite D'"
      apply (rule derivable_list_finite_conclusion[OF _ deriv_Ps])
      apply simp
      apply (rule ballI)
      subgoal for p
        apply (cases p)
        by (simp add: comp_def substs_preserve_finiteness)
      done
    hence "finite (subst_cl D' \<sigma>\<^sub>D)"
      by (rule substs_preserve_finiteness)

    from \<open>renaming_cl C D\<close> obtain \<rho> where
      ren_\<rho>: "renaming \<rho> (vars_of_cl (cl_ecl C))" and "D = subst_ecl C \<rho>"
      by (auto simp add: renaming_cl_def)
    hence "cl_ecl D = subst_cl (cl_ecl C) \<rho>"
      using cl_ecl_subst_ecl_distrib by blast
    hence "subst_cl D' \<sigma>\<^sub>D = subst_cl (subst_cl C' \<sigma>\<^sub>C) \<rho>"
      by (metis \<open>cl_ecl C = subst_cl C' \<sigma>\<^sub>C\<close> deriv_Ps derivable_list_concl_conv)
    then obtain \<rho>' where
      "renaming \<rho>' (vars_of_cl (subst_cl D' \<sigma>\<^sub>D))" and
      "subst_cl C' \<sigma>\<^sub>C = subst_cl (subst_cl D' \<sigma>\<^sub>D) \<rho>'"
      using ex_renaming_swap[OF \<open>finite (cl_ecl C)\<close> ren_\<rho>, unfolded \<open>cl_ecl C = subst_cl C' \<sigma>\<^sub>C\<close>]
      by blast

    have "subst_cl C' \<sigma>\<^sub>C = subst_cl D' (\<sigma>\<^sub>D \<lozenge> \<rho>')"
      using \<open>subst_cl C' \<sigma>\<^sub>C = subst_cl (subst_cl D' \<sigma>\<^sub>D) \<rho>'\<close> composition_of_substs_cl by blast

    define \<iota> where "\<iota> = Infer Ps (Abs_fset (subst_cl D' \<sigma>\<^sub>D))"

    have \<iota>_in: "\<iota> \<in> F_Inf"
      unfolding \<iota>_def F_Inf_def mem_Collect_eq Let_def
    proof (intro exI conjI)
      show "Infer Ps (Abs_fset (subst_cl D' \<sigma>\<^sub>D)) = Infer Ps (Abs_fset (subst_cl D' \<sigma>\<^sub>D))"
        by (rule refl)
    next
      show "derivable_list D (?map_prems Ps) \<sigma>\<^sub>D SuperCalc.FirstOrder D'"
        by (rule deriv_Ps)
    qed

    have prems_\<iota>_in_subset: "set (prems_of \<iota>) \<subseteq> N"
      using FOO by (simp add: \<iota>_def list_all2_conj_unary_iff list_all_member_iff_subset)

    from sat_N_alt[OF \<iota>_in prems_\<iota>_in_subset]
    have \<G>_subset_Red_\<iota>: "\<And>q. \<G>_I q \<iota> \<subseteq> G.Red_I q (\<Union> (\<G>_F ` N))"
      unfolding F.Red_I_\<G>_def F.Red_I_\<G>_q_def by simp

    have "\<G>_I q \<iota>' \<subseteq> G.Red_I q (\<Union> (\<G>_F ` N'))" for q
    proof (rule subsetI)
      fix \<iota>g
      assume "\<iota>g \<in> \<G>_I q \<iota>'"
      then obtain \<gamma>\<^sub>\<iota>s \<gamma>\<^sub>\<iota> where "\<iota>g \<in> G_Inf q" and
        prems_of_\<iota>g: "prems_of \<iota>g = map2 (\<lambda>D \<gamma>. Abs_fset (subst_cl (fset D) \<gamma>)) (prems_of \<iota>') \<gamma>\<^sub>\<iota>s" and
        concl_of_\<iota>g: "concl_of \<iota>g = Abs_fset (subst_cl (fset (concl_of \<iota>')) \<gamma>\<^sub>\<iota>)" and
        "length (prems_of \<iota>') = length \<gamma>\<^sub>\<iota>s"
        by (auto simp add: \<G>_I_def)

      have "length \<rho>s = length \<gamma>\<^sub>\<iota>s"
        using \<open>length (prems_of \<iota>') = length \<gamma>\<^sub>\<iota>s\<close> \<open>length Ps = length \<rho>s\<close> prems_\<iota>'_def by auto

      have "\<iota>g \<in> \<G>_I q \<iota>"
        unfolding \<G>_I_def
        unfolding mem_Collect_eq \<iota>_def inference.sel
      proof (intro conjI exI)
        show "\<iota>g \<in> G_Inf q"
          by (rule \<open>\<iota>g \<in> G_Inf q\<close>)
      next
        show "prems_of \<iota>g = map2 (\<lambda>D \<gamma>. Abs_fset (subst_cl (fset D) \<gamma>)) Ps (map2 (\<lozenge>) \<rho>s \<gamma>\<^sub>\<iota>s)"
          unfolding prems_of_\<iota>g
          unfolding prems_\<iota>'_def
          using \<open>length Ps = length \<rho>s\<close> \<open>length \<rho>s = length \<gamma>\<^sub>\<iota>s\<close>
        proof (induction Ps \<rho>s \<gamma>\<^sub>\<iota>s rule: list_induct3)
          case Nil
          show ?case by simp
        next
          case (Cons x xs y ys z zs)
          then show ?case
            apply simp
            by (metis Abs_fset_inverse composition_of_substs_cl finite_fset mem_Collect_eq
                substs_preserve_finiteness)
        qed
      next
        show "length Ps = length (map2 (\<lozenge>) \<rho>s \<gamma>\<^sub>\<iota>s)"
          using \<open>length Ps = length \<rho>s\<close> \<open>length \<rho>s = length \<gamma>\<^sub>\<iota>s\<close> by simp
      next
        have "concl_of \<iota>g = Abs_fset (subst_cl (fset (Abs_fset (subst_cl C' \<sigma>\<^sub>C))) \<gamma>\<^sub>\<iota>)"
          by (simp add: concl_of_\<iota>g concl_of_\<iota>')
        also have "... = Abs_fset (subst_cl (subst_cl C' \<sigma>\<^sub>C) \<gamma>\<^sub>\<iota>)"
          by (simp add: Abs_fset_inverse \<open>finite (subst_cl C' \<sigma>\<^sub>C)\<close>)
        also have "... = Abs_fset (subst_cl D' (\<sigma>\<^sub>D \<lozenge> \<rho>' \<lozenge> \<gamma>\<^sub>\<iota>))"
          by (simp add: \<open>subst_cl C' \<sigma>\<^sub>C = subst_cl (subst_cl D' \<sigma>\<^sub>D) \<rho>'\<close> composition_of_substs_cl)
        finally show "concl_of \<iota>g = Abs_fset (subst_cl (fset (Abs_fset (subst_cl D' \<sigma>\<^sub>D))) (\<rho>' \<lozenge> \<gamma>\<^sub>\<iota>))"
          apply simp
          by (metis Abs_fset_inverse CollectI \<open>finite (subst_cl D' \<sigma>\<^sub>D)\<close> composition_of_substs_cl)
      qed
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
qed

lemma set_entails_clause_Un_\<G>_FI: "set_entails_clause (fset ` \<Union> (\<G>_F ` N)) {}"
  if N_entails_empty: "set_entails_clause (fset ` N) {}"
  for N
  unfolding set_entails_clause_def
proof (intro allI impI)
  fix I
  assume "fo_interpretation I" and
    validate_I_\<G>_F_N: "validate_clause_set I (fset ` \<Union> (\<G>_F ` N))"

  have "validate_clause_set I (fset ` N)"
    unfolding validate_clause_set.simps validate_clause.simps
  proof (intro allI impI)
    have 1: "f ` (\<Union>x\<in>N. {g x \<gamma> |\<gamma>. P x \<gamma>}) = (\<Union>x\<in>N. f ` {g x \<gamma> |\<gamma>. P x \<gamma>})"
      for f g P
      by blast
    have 2: "(\<Union>x\<in>N. f ` {g x \<gamma> |\<gamma>. P x \<gamma>}) = (\<Union>x\<in>N. {f (g x \<gamma>) |\<gamma>. P x \<gamma>})" for f g P
      by blast

    fix C \<gamma>
    assume "C \<in> fset ` N" and gr_C_\<gamma>: "ground_clause (subst_cl C \<gamma>)"
    hence "subst_cl C \<gamma> \<in> fset ` \<Union> (\<G>_F ` N)"
      apply (simp add: \<G>_F_def 1 2)
      by (metis Abs_fset_inverse CollectI finite_fset ground_clauses_and_ground_substs imageE
          substs_preserve_finiteness)
    hence validate_I_C_\<gamma>: "validate_clause I (subst_cl C \<gamma>)"
      using validate_I_\<G>_F_N by simp

    have "validate_ground_clause I (subst_cl (subst_cl C \<gamma>) [])"
      using gr_C_\<gamma> validate_I_C_\<gamma>[unfolded validate_clause.simps, rule_format, of "[]"]
      by simp
    thus "validate_ground_clause I (subst_cl C \<gamma>)"
      by simp
  qed
  thus "validate_clause I {}"
    using \<open>fo_interpretation I\<close> N_entails_empty
    by (simp add: set_entails_clause_def)
qed

lemma set_entails_clause_Un_\<G>_FD: "set_entails_clause (fset ` N) {}"
  if N_entails_empty: "set_entails_clause (fset ` \<Union> (\<G>_F ` N)) {}"
  for N
  unfolding set_entails_clause_def
proof (intro allI impI)
  fix I
  assume "fo_interpretation I" and validate_I: "validate_clause_set I (fset ` N)"
  have "validate_clause_set I (fset ` \<Union> (\<G>_F ` N))"
    unfolding validate_clause_set.simps validate_clause.simps
  proof (intro allI impI)
    have 1: "f ` (\<Union>x\<in>N. {g x \<gamma> |\<gamma>. P x \<gamma>}) = (\<Union>x\<in>N. f ` {g x \<gamma> |\<gamma>. P x \<gamma>})"
      for f g P
      by blast
    have 2: "(\<Union>x\<in>N. f ` {g x \<gamma> |\<gamma>. P x \<gamma>}) = (\<Union>x\<in>N. {f (g x \<gamma>) |\<gamma>. P x \<gamma>})" for f g P
      by blast

    fix C \<gamma>
    assume C_in: "C \<in> fset ` \<Union> (\<G>_F ` N)" and gr_C_\<gamma>: "ground_clause (subst_cl C \<gamma>)"

    from C_in have "C \<in> (\<Union>C\<in>N. {subst_cl (fset C) \<gamma> | \<gamma>. ground_on (vars_of_cl (fset C)) \<gamma>})"
      by (smt (verit, del_insts) Abs_fset_inverse UN_iff \<G>_F_def finite_fset imageE mem_Collect_eq
          substs_preserve_finiteness)
    then obtain C' where
      "C' \<in> N" and C_in':"C \<in> {subst_cl (fset C') \<gamma> | \<gamma>. ground_on (vars_of_cl (fset C')) \<gamma>}"
      by auto

    from C_in' have gr_C: "ground_clause C"
      using ground_substs_yield_ground_clause by blast

    from \<open>C' \<in> N\<close> have "validate_clause I (fset C')"
      using validate_I[unfolded validate_clause_set.simps] by blast
    hence "validate_ground_clause I C"
      unfolding validate_clause.simps
      using C_in' gr_C by blast
    thus "validate_ground_clause I (subst_cl C \<gamma>)"
      using gr_C
      by (simp add: substs_preserve_ground_clause)
  qed
  thus "validate_clause I {}"
    using \<open>fo_interpretation I\<close> N_entails_empty
    by (simp add: set_entails_clause_def)
qed

lemma derivable_list_if_SuperCalc_derivable:
  assumes "SuperCalc.derivable C P N \<sigma> k C'"
  shows "\<exists>Ps. P = set Ps \<and> derivable_list C Ps \<sigma> k C'"
  using assms
  unfolding SuperCalc.derivable_def derivable_list_def
  by (metis (no_types, lifting) empty_set insert_commute list.simps(15))

lemma lifting_lemma_derivable_list:
  assumes "derivable_list C Ps \<sigma> SuperCalc.Ground C'"
  shows "\<exists>D \<theta>. derivable_list D Ps \<theta> SuperCalc.FirstOrder C' \<and>
           \<sigma> \<doteq> \<theta> \<lozenge> \<sigma> \<and> SuperCalc.trms_subsumes D C \<sigma>"
  using assms SuperCalc.lifting_lemma_reflexion SuperCalc.lifting_lemma_factorization
    SuperCalc.lifting_lemma_superposition
  unfolding derivable_list_def
  by metis

lemma map2_cong0: "(\<And>x y. (x, y) \<in> set (zip xs ys) \<Longrightarrow> f x y = g x y) \<Longrightarrow> map2 f xs ys = map2 g xs ys"
  by (auto intro: list.map_cong0)

lemma map2_ap_ap: "map2 (\<lambda>x y. f (g x y)) xs ys = map f (map2 g xs ys)"
  by auto

lemma ex_conj_swap: "(\<exists>x y. f y \<and> g x y) \<longleftrightarrow> (\<exists>y. f y \<and> (\<exists>x. g x y))"
  by blast

lemma derivable_list_no_trms:
  assumes "derivable_list C P \<sigma> k C'"
  shows "\<exists>trms. derivable_list (Ecl (subst_cl C' \<sigma>) trms) (map (\<lambda>x. Ecl (cl_ecl x) {}) P) \<sigma> k C'"
  using assms[unfolded derivable_list_def]
proof (elim disjE exE conjE)
  fix P1
  assume "P = [P1]" and "SuperCalc.reflexion P1 C \<sigma> k C'"
  hence "\<exists>trms. SuperCalc.reflexion (Ecl (cl_ecl P1) {}) (Ecl (subst_cl C' \<sigma>) trms) \<sigma> k C'"
    unfolding SuperCalc.reflexion_def
    apply safe
    apply simp
    using SuperCalc.eligible_literal_def by auto
  thus ?thesis
    using \<open>P = [P1]\<close> by (auto simp: derivable_list_def)
next
  fix P1
  assume "P = [P1]" and "SuperCalc.factorization P1 C \<sigma> k C'"
  hence "\<exists>trms. SuperCalc.factorization (Ecl (cl_ecl P1) {}) (Ecl (subst_cl C' \<sigma>) trms) \<sigma> k C'"
    unfolding SuperCalc.factorization_def
    apply safe
    apply simp
    by (metis (no_types, lifting) SuperCalc.eligible_literal_def cl_ecl.simps)
  thus ?thesis
    using \<open>P = [P1]\<close> by (auto simp: derivable_list_def)
next
  fix P1 P2
  assume "P = [P2, P1]" and "SuperCalc.superposition P1 P2 C \<sigma> k C'"
  hence "\<exists>trms. SuperCalc.superposition (Ecl (cl_ecl P1) {}) (Ecl (cl_ecl P2) {}) (Ecl (subst_cl C' \<sigma>) trms) \<sigma> k C'"
    unfolding SuperCalc.superposition_def
    apply (elim exE conjE)
    subgoal for L _ _ _ _ M _ _ _ _ _ _ u'
      apply (simp add: ex_conj_swap)
      apply (rule exI[of _ L])
      apply simp
      apply (rule exI[of _ M])
      apply (simp add: SuperCalc.eligible_literal_def variable_disjoint_def)
      apply (rule exI[of _ u'])
      apply (simp add: SuperCalc.allowed_redex_def)
      by (metis (no_types, lifting) SuperCalc.strictly_maximal_literal_def cl_ecl.simps)
    done
  thus ?thesis
    using \<open>P = [P2, P1]\<close> by (auto simp: derivable_list_def)
qed

lemma finite_subst_cl:
  assumes inj: "inj_on (\<lambda>L. subst_lit L \<sigma>) C"
  shows "finite (subst_cl C \<sigma>) = finite C"
  unfolding subst_cl_conv finite_image_iff[OF inj]
  by (rule refl)

lemma finite_cl_ecl_iff_renaming_cl:
  assumes "renaming_cl C D"
  shows "finite (cl_ecl C) \<longleftrightarrow> finite (cl_ecl D)"
proof -
  from assms obtain \<rho> where
    D_def: "D = subst_ecl C \<rho>" and
    ren_\<rho>: "renaming \<rho> (vars_of_cl (cl_ecl C))"
    unfolding renaming_cl_def by auto

  obtain C' trms where C_def: "C = Ecl C' trms"
    by (cases C)

  have inj: "inj_on (\<lambda>L. subst_lit L \<rho>) C'"
  proof (rule inj_on_subset)
    show "inj_on (\<lambda>L. subst_lit L \<rho>) {L. vars_of_lit L \<subseteq> vars_of_cl C'}"
      by (rule inj_subst_lit_if_renaming[OF ren_\<rho>, unfolded C_def cl_ecl.simps])
  next
    show "C' \<subseteq> {L. vars_of_lit L \<subseteq> vars_of_cl C'}"
      by (simp add: subsetI vars_of_cl_lem)
  qed

  show ?thesis
    unfolding D_def C_def
    unfolding cl_ecl.simps subst_ecl.simps
    unfolding finite_subst_cl[OF inj]
    by (rule refl)
qed

thm SuperCalc.grounding_set_def

lemma totalp_on_singleton: "totalp_on {x} R"
  by (simp add: totalp_on_def)

lemma total_on_singleton: "Relation.total_on {x} r"
  by (simp add: Relation.total_on_def)

lemma G_derivable_list_if_derivable_list:
  assumes deriv: "derivable_list C Ps \<gamma> SuperCalc.Ground C'" and
    grounds: "SuperCalc.grounding_set (set Ps) \<gamma>" and
    grounds_subset: "(\<lambda>D. subst_cl (cl_ecl D) \<gamma>) ` set Ps \<subseteq>
      (\<Union>D\<in>M. {subst_cl D \<gamma> | \<gamma>. ground_clause (subst_cl D \<gamma>)})"
  shows "\<exists>CC. \<exists>CC' \<subseteq> subst_cl C' \<gamma>.
    G_derivable_list M CC (map (\<lambda>D. Ecl (subst_cl (cl_ecl D) \<gamma>) {}) Ps) \<gamma> SuperCalc.Ground CC'"
  using deriv[unfolded derivable_list_def]
proof (elim disjE exE conjE)
  fix P1 assume Ps_def: "Ps = [P1]" and "SuperCalc.reflexion P1 C \<gamma> SuperCalc.Ground C'"
  then obtain L1 t s where
    eligible_L1: "SuperCalc.eligible_literal L1 P1 \<gamma>" and
    L1_in: "L1 \<in> cl_ecl P1" and
    orient_L1: "SuperCalc.orient_lit_inst L1 t s neg \<gamma>" and
    unif_t_s: "SuperCalc.ck_unifier t s \<gamma> SuperCalc.Ground" and
    C_def: "C = Ecl (subst_cl C' \<gamma>) (SuperCalc.get_trms (subst_cl C' \<gamma>) (SuperCalc.dom_trms
              (subst_cl C' \<gamma>) (subst_set (trms_ecl P1 \<union> {t}) \<gamma>)) SuperCalc.Ground)" and
    C'_def: "C' = cl_ecl P1 - {L1}"
    by (auto simp: SuperCalc.reflexion_def)

  define CC' where
    "CC' = subst_cl (cl_ecl P1) \<gamma> - {subst_lit L1 \<gamma>}"

  define trms_CC where
    "trms_CC = SuperCalc.get_trms CC' (SuperCalc.dom_trms CC' (subst_set {t \<lhd> \<gamma>} \<gamma>))
      SuperCalc.Ground"

  define CC where
    "CC = Ecl CC' trms_CC"

  from grounds have ground_P1_\<gamma>: "ground_clause (subst_cl (cl_ecl P1) \<gamma>)"
    by (simp add: Ps_def SuperCalc.grounding_set_def)
  hence ground_CC': "ground_clause CC'"
    by (simp add: CC'_def SuperCalc.ground_clause_subset[OF Diff_subset])

  from grounds_subset have P1_\<gamma>_in: "subst_cl (cl_ecl P1) \<gamma> \<in>
    (\<Union>D\<in>M. {subst_cl D \<gamma> |\<gamma>. ground_clause (subst_cl D \<gamma>)})"
    by (simp add: Ps_def)

  have "CC' \<subseteq> subst_cl C' \<gamma>"
    unfolding CC'_def C'_def
    by (metis Diff_eq_empty_iff Diff_insert2 L1_in cl_ecl_subst_ecl_distrib insert_Diff insert_is_Un
        set_eq_subset singleton_subst_lit_conv subst_cl_union)

  moreover have "G_SuperCalc.reflexion M (Ecl (subst_cl (cl_ecl P1) \<gamma>) {}) CC \<gamma> SuperCalc.Ground CC'"
    unfolding G_SuperCalc.reflexion_def
  proof (intro exI conjI)
    show "G_SuperCalc.eligible_literal M (subst_lit L1 \<gamma>) (Ecl (subst_cl (cl_ecl P1) \<gamma>) {}) \<gamma>"
      using eligible_L1
      unfolding SuperCalc.eligible_literal_def
      using select_stable_under_grounding[rule_format]
      using ground_select_at_limit_grounding[OF P1_\<gamma>_in]
      by (smt (verit, ccfv_SIG) G_SuperCalc.eligible_literal_def L1_in cl_ecl.simps image_empty
          image_eqI subst_cl_conv substs_preserve_ground_clause substs_preserve_ground_lit)
  next
    show "subst_lit L1 \<gamma> \<in> cl_ecl (Ecl (subst_cl (cl_ecl P1) \<gamma>) {})"
      using L1_in by (simp add: subst_cl_conv)
  next
    show "SuperCalc.orient_lit_inst (subst_lit L1 \<gamma>) (subst t \<gamma>) (subst s \<gamma>) neg \<gamma>"
      by (metis (no_types, opaque_lifting) SuperCalc.ck_unifier_thm SuperCalc.lift_orient_lit
          SuperCalc.orient_lit_def SuperCalc.orient_lit_inst_def
          \<open>SuperCalc.ck_unifier t s \<gamma> SuperCalc.Ground\<close> irrefl_def orient_L1 trm_ord_irrefl)
  next
    show "SuperCalc.ck_unifier (subst t \<gamma>) (subst s \<gamma>) \<gamma> SuperCalc.Ground"
      by (metis SuperCalc.ck_unifier_def SuperCalc.inferences.simps(1) Unifier_def unif_t_s)
  next
    show "CC' = subst_cl CC' \<gamma>"
      by (simp only: substs_preserve_ground_clause[OF ground_CC', symmetric])
  qed (simp_all add: CC_def CC'_def trms_CC_def cl_ecl_subst_ecl_distrib)
  
  ultimately show ?thesis
    unfolding Ps_def G_derivable_list_def
    by auto
next
  fix P1 assume Ps_def: "Ps = [P1]" and "SuperCalc.factorization P1 C \<gamma> SuperCalc.Ground C'"
  then obtain L1 L2 t s u v where
    eligible_L1: "SuperCalc.eligible_literal L1 P1 \<gamma>" and
    L1_in: "L1 \<in> cl_ecl P1" and
    L2_in: "L2 \<in> cl_ecl P1 - {L1}" and
    orient_L1: "SuperCalc.orient_lit_inst L1 t s pos \<gamma>" and
    orient_L2: "SuperCalc.orient_lit_inst L2 u v pos \<gamma>" and
    t_\<gamma>_neq_s_\<gamma>: "t \<lhd> \<gamma> \<noteq> s \<lhd> \<gamma>" and
    t_\<gamma>_neq_v_\<gamma>: "t \<lhd> \<gamma> \<noteq> v \<lhd> \<gamma>" and
    unif_t_u: "SuperCalc.ck_unifier t u \<gamma> SuperCalc.Ground" and
    C_def: "C = Ecl (subst_cl C' \<gamma>) (SuperCalc.get_trms (subst_cl C' \<gamma>)
      (SuperCalc.dom_trms (subst_cl C' \<gamma>) (subst_set (trms_ecl P1 \<union> proper_subterms_of t) \<gamma>))
      SuperCalc.Ground)" and
    C'_def: "C' = cl_ecl P1 - {L2} \<union> {Neg (Eq s v)}"
    unfolding SuperCalc.factorization_def
    by metis

  from grounds have ground_P1_\<gamma>: "ground_clause (subst_cl (cl_ecl P1) \<gamma>)"
    by (simp add: Ps_def SuperCalc.grounding_set_def)
  with L1_in L2_in have
    "vars_of_lit (subst_lit L1 \<gamma>) = {}" and
    "vars_of_lit (subst_lit L2 \<gamma>) = {}"
    by (simp_all add: SuperCalc.ground_clause_lit subst_cl_conv)
  hence
    "vars_of (subst t \<gamma>) = {}" and "vars_of (subst s \<gamma>) = {}" and
    "vars_of (subst u \<gamma>) = {}" and "vars_of (subst v \<gamma>) = {}"
    using orient_L1 orient_L2
    by (auto dest: SuperCalc.lift_orient_lit[THEN SuperCalc.orient_lit_vars])


  from grounds_subset have P1_\<gamma>_in: "subst_cl (cl_ecl P1) \<gamma> \<in>
    (\<Union>D\<in>M. {subst_cl D \<gamma> |\<gamma>. ground_clause (subst_cl D \<gamma>)})"
    by (simp add: Ps_def)

  define CC' where
    "CC' = subst_cl (cl_ecl P1) \<gamma> - {subst_lit L2 \<gamma>} \<union> {Neg (Eq (subst s \<gamma>) (subst v \<gamma>))}"

  define trms_CC where
    "trms_CC = SuperCalc.get_trms CC' (SuperCalc.dom_trms CC'
      (subst_set (proper_subterms_of (t \<lhd> \<gamma>)) \<gamma>)) SuperCalc.Ground"

  term "SuperCalc.get_trms CC' (SuperCalc.dom_trms CC' (subst_set {s. \<exists>p. p \<noteq> [] \<and> subterm (t \<lhd> \<gamma>) p s} \<gamma>))
     SuperCalc.Ground"

  define CC where
    "CC = Ecl CC' trms_CC"

  have ground_CC': "ground_clause CC'"
    unfolding CC'_def
  proof (rule SuperCalc.ground_clause_union)
    show "ground_clause (subst_cl (cl_ecl P1) \<gamma> - {subst_lit L2 \<gamma>})"
      by (rule SuperCalc.ground_clause_subset[OF Diff_subset ground_P1_\<gamma>])
  next
    show "ground_clause {Neg (Eq (s \<lhd> \<gamma>) (v \<lhd> \<gamma>))}"
      using \<open>vars_of (subst s \<gamma>) = {}\<close> \<open>vars_of (subst v \<gamma>) = {}\<close>
      by (simp add: ground_clause.simps vars_of_cl.simps)
  qed

  have "CC' \<subseteq> subst_cl C' \<gamma>"
    apply (simp add: CC'_def C'_def)
    by (smt (verit, ccfv_threshold) DiffD2 insert_Diff_single insert_iff insert_is_Un
        singleton_subst_lit_conv subsetI subst_cl_union subst_equation.simps subst_lit.simps(2))

  moreover have "G_SuperCalc.factorization M (Ecl (subst_cl (cl_ecl P1) \<gamma>) {}) CC \<gamma> SuperCalc.Ground CC'"
    unfolding G_SuperCalc.factorization_def
  proof (intro exI conjI)
    show "G_SuperCalc.eligible_literal M (subst_lit L1 \<gamma>) (Ecl (subst_cl (cl_ecl P1) \<gamma>) {}) \<gamma>"
      using eligible_L1
      unfolding SuperCalc.eligible_literal_def
      using select_stable_under_grounding[rule_format]
      using ground_select_at_limit_grounding[OF P1_\<gamma>_in]
      by (smt (verit, ccfv_SIG) G_SuperCalc.eligible_literal_def L1_in cl_ecl.simps image_empty
          image_eqI subst_cl_conv substs_preserve_ground_clause substs_preserve_ground_lit)
  next
    show "subst_lit L1 \<gamma> \<in> cl_ecl (Ecl (subst_cl (cl_ecl P1) \<gamma>) {})"
      using L1_in by (simp add: subst_cl_conv)
  next
    have "subst_lit L2 \<gamma> \<in> cl_ecl (Ecl (subst_cl (cl_ecl P1) \<gamma>) {})"
    (* have "subst_lit L1 \<gamma> \<noteq> subst_lit L2 \<gamma>"
      using orient_L1 orient_L2 t_\<gamma>_neq_v_\<gamma>
      unfolding SuperCalc.orient_lit_inst_def
      apply simp
      apply (elim conjE disjE)
      using SuperCalc.ck_unifier_thm[OF unif_t_u] u_\<gamma>_neq_v_\<gamma> t_\<gamma>_neq_s_\<gamma>
         apply simp_all
      using SuperCalc.eligible_literal_def *)
      sorry
      
    show "subst_lit L2 \<gamma> \<in> cl_ecl (Ecl (subst_cl (cl_ecl P1) \<gamma>) {}) - {subst_lit L1 \<gamma>}"
      unfolding cl_ecl.simps
      using L2_in
      sorry
  next
    show "SuperCalc.orient_lit_inst (subst_lit L1 \<gamma>) (subst t \<gamma>) (subst s \<gamma>) pos \<gamma>"
      using orient_L1
      apply (simp add: SuperCalc.orient_lit_inst_def)
      apply (elim conjE disjE)
      using \<open>vars_of (subst t \<gamma>) = {}\<close> \<open>vars_of (subst s \<gamma>) = {}\<close>
      by (simp_all add: subst_ident_if_vars_empty)
  next
    show "SuperCalc.orient_lit_inst (subst_lit L2 \<gamma>) (subst u \<gamma>) (subst v \<gamma>) pos \<gamma>"
      using orient_L2
      apply (simp add: SuperCalc.orient_lit_inst_def)
      apply (elim conjE disjE)
      using \<open>vars_of (subst u \<gamma>) = {}\<close> \<open>vars_of (subst v \<gamma>) = {}\<close>
      by (simp_all add: subst_ident_if_vars_empty)
  next
    show "CC' = subst_cl (cl_ecl P1) \<gamma> - {subst_lit L2 \<gamma>} \<union> {Neg (Eq (s \<lhd> \<gamma>) (v \<lhd> \<gamma>))}"
      by (rule CC'_def)
  next
    show "CC = Ecl CC' trms_CC"
      by (rule CC_def)
  next
    show "SuperCalc.ck_unifier (t \<lhd> \<gamma>) (u \<lhd> \<gamma>) \<gamma> SuperCalc.Ground"
      using unif_t_u by (simp add: SuperCalc.ck_unifier_def Unifier_def)
  next
    show "t \<lhd> \<gamma> \<lhd> \<gamma> \<noteq> s \<lhd> \<gamma> \<lhd> \<gamma>"
      using t_\<gamma>_neq_s_\<gamma> \<open>vars_of (subst t \<gamma>) = {}\<close> \<open>vars_of (subst s \<gamma>) = {}\<close>
      by (simp add: subst_ident_if_vars_empty)
  next
    show "t \<lhd> \<gamma> \<lhd> \<gamma> \<noteq> v \<lhd> \<gamma> \<lhd> \<gamma>"
      using t_\<gamma>_neq_v_\<gamma> \<open>vars_of (subst t \<gamma>) = {}\<close> \<open>vars_of (subst v \<gamma>) = {}\<close>
      by (simp add: subst_ident_if_vars_empty)
  next
    show "CC' = subst_cl CC' \<gamma>"
      using ground_CC' by (simp add: substs_preserve_ground_clause)
  qed (simp_all add: CC'_def CC_def trms_CC_def cl_ecl_subst_ecl_distrib)

  ultimately show ?thesis
    unfolding Ps_def G_derivable_list_def by auto
next
  fix P1 P2
  assume Ps_def: "Ps = [P2, P1]" and "SuperCalc.superposition P1 P2 C \<gamma> SuperCalc.Ground C'"
  show ?thesis
    sorry
qed


sublocale statically_complete_calculus "{{||}}" F_Inf "(\<TTurnstile>e)" F.Red_I_\<G> F.Red_F_\<G>
proof unfold_locales
  show "\<And>N. F.Red_I_\<G> N \<subseteq> F_Inf"
    by (rule F.Red_I_to_Inf)
next
  fix B N
  assume "B \<in> {{||}}" and "N \<TTurnstile>e {B}"
  hence B_def: "B = {||}" and "N \<TTurnstile>e {{||}}"
    by simp_all
  hence N_entails_empty: "set_entails_clause (fset ` N) {}"
    by (simp add: entails_def)
  hence "set_entails_clause (fset ` \<Union> (\<G>_F ` N)) {}"
    by (rule set_entails_clause_Un_\<G>_FI)
  hence "\<Union> (\<G>_F ` N) \<TTurnstile>e {{||}}"
    by (simp add: entails_def)
  hence "\<Union> (\<G>_F ` (N - F.Red_F_\<G> N)) \<TTurnstile>e {{||}}"
    using F.Red_F_Bot[simplified, OF refl, unfolded F.entails_\<G>_def, simplified, of N]
    by simp
  hence "set_entails_clause (fset ` \<Union> (\<G>_F ` (N - F.Red_F_\<G> N))) {}"
    by (simp add: entails_def)
  hence "set_entails_clause (fset ` (N - F.Red_F_\<G> N)) {}"
    by (rule set_entails_clause_Un_\<G>_FD)
  thus "N - F.Red_F_\<G> N \<TTurnstile>e {B}"
    by (simp add: B_def entails_def)
next
  show "\<And>N N'. N \<subseteq> N' \<Longrightarrow> F.Red_F_\<G> N \<subseteq> F.Red_F_\<G> N'"
    by (rule F.Red_F_of_subset)
next
  show "\<And>N N'. N \<subseteq> N' \<Longrightarrow> F.Red_I_\<G> N \<subseteq> F.Red_I_\<G> N'"
    by (rule F.Red_I_of_subset)
next
  show "\<And>N' N. N' \<subseteq> F.Red_F_\<G> N \<Longrightarrow> F.Red_F_\<G> N \<subseteq> F.Red_F_\<G> (N - N')"
    by (rule F.Red_F_of_Red_F_subset)
next
  show "\<And>N' N. N' \<subseteq> F.Red_F_\<G> N \<Longrightarrow> F.Red_I_\<G> N \<subseteq> F.Red_I_\<G> (N - N')"
    by (rule F.Red_I_of_Red_F_subset)
next
  show "\<And>\<iota> N. \<iota> \<in> F_Inf \<Longrightarrow> concl_of \<iota> \<in> N \<Longrightarrow> \<iota> \<in> F.Red_I_\<G> N"
    by (rule F.Red_I_of_Inf_to_N)
next
  fix B and N :: "'a fclause set"
  assume "B \<in> {{||}}" and "F.saturated N" and "N \<TTurnstile>e {B}"
  hence B_def: "B = {||}" by simp

  \<comment> \<open>We close @{term N} under \<alpha>-renaming.\<close>
  define N' :: "'a fclause set" where
    "N' \<equiv> {Abs_fset (subst_cl (fset C) \<sigma>) | C \<sigma>. C \<in> N \<and> renaming \<sigma> (vars_of_cl (fset C))}"

  have "N \<subseteq> N'"
  proof (rule Set.subsetI)
    fix C
    show "C \<in> N \<Longrightarrow> C \<in> N'"
      unfolding N'_def Set.mem_Collect_eq
      by (metis SuperCalc.renaming_Nil assoc.simps(1) fset_inverse subst_cl_ident)
  qed
  hence "N' \<TTurnstile>e {{||}}"
    using \<open>N \<TTurnstile>e {B}\<close>[unfolded B_def]
    by (auto intro: G.entails_trans[of N' N "{{||}}"] G.subset_entailed)

  have all_finite_N': "\<forall>x \<in> (\<lambda>C. Ecl (fset C) {}) ` N'. finite (cl_ecl x)"
    by simp

  have saturated_N': "F.saturated N'"
    by (rule saturated_renamings[OF \<open>F.saturated N\<close>, folded N'_def])

  have gr_inf_satur_N': "SuperCalc.ground_inference_saturated ((\<lambda>C. Ecl (fset C) {}) ` N')"
    (* using saturated_N'[unfolded F.saturated_def F.Inf_from_def F.Red_I_\<G>_def
          F.Red_I_\<G>_q_def, simplified, unfolded subset_iff mem_Collect_eq, rule_format] *)
    unfolding SuperCalc.ground_inference_saturated_def
  proof (intro allI impI)
    fix C P \<sigma> C'
    assume
      deriv_C_P: "SuperCalc.derivable C P ((\<lambda>C. Ecl (fset C) {}) ` N') \<sigma> SuperCalc.Ground C'" and
      ground_C: "ground_clause (cl_ecl C)" and
      grounding_P: "SuperCalc.grounding_set P \<sigma>"

    from deriv_C_P have P_subset: "P \<subseteq> (\<lambda>C. Ecl (fset C) {}) ` N'"
      by (simp add: SuperCalc.derivable_premisses)
    hence ball_fin_P: "\<forall>D \<in> P. finite (cl_ecl D)"
      using all_finite_N' by blast

    have fin_P: "finite P"
      using deriv_C_P[unfolded SuperCalc.derivable_def] by auto

    from deriv_C_P obtain Ps
      where P_eq: "P = set Ps" and deriv_C_Ps: "derivable_list C Ps \<sigma> SuperCalc.Ground C'"
      by (auto dest: derivable_list_if_SuperCalc_derivable)

    thm SuperCalc.factorization_def SuperCalc.ck_unifier_def Unifier_def

    have "(\<lambda>D. subst_cl (cl_ecl D) \<sigma>) ` P \<subseteq>
            (\<Union>D\<in>fset ` N'. {subst_cl D \<gamma> |\<gamma>. ground_clause (subst_cl D \<gamma>)})"
      using fin_P grounding_P P_subset
    proof (induction P rule: finite_induct)
      case empty
      show ?case by simp
    next
      case (insert x F)
      have "subst_cl (cl_ecl x) \<sigma> \<in>
              (\<Union>D\<in>fset ` N'. {subst_cl D \<gamma> |\<gamma>. ground_clause (subst_cl D \<gamma>)})"
      proof -
        have "cl_ecl x \<in>fset ` N'"
          using insert.prems by fastforce
        moreover have "ground_clause (subst_cl (cl_ecl x) \<sigma>)"
          using insert.prems by (meson SuperCalc.grounding_set_def insert_iff)
        ultimately show ?thesis by blast
      qed

      moreover have "(\<lambda>D. subst_cl (cl_ecl D) \<sigma>) ` F \<subseteq>
              (\<Union>D\<in>fset ` N'. {subst_cl D \<gamma> |\<gamma>. ground_clause (subst_cl D \<gamma>)})"
      proof (rule insert.IH)
        show "SuperCalc.grounding_set F \<sigma>"
          using insert.prems by (meson SuperCalc.grounding_set_def insert_iff)
      next
        show "F \<subseteq> (\<lambda>C. Ecl (fset C) {}) ` N'"
          using insert.prems by simp
      qed

      ultimately show ?case
        by simp
    qed

    then obtain CC CC' where
      "CC' \<subseteq> subst_cl C' \<sigma>" and
      G_deriv_CC_Ps_\<sigma>: "G_derivable_list (fset ` N') CC
        (map (\<lambda>D. Ecl (subst_cl (cl_ecl D) \<sigma>) {}) Ps) \<sigma> SuperCalc.Ground CC'"
      using G_derivable_list_if_derivable_list[OF deriv_C_Ps, folded P_eq, OF grounding_P,
          of "fset ` N'"]
      by auto

    from deriv_C_Ps obtain D \<sigma>' where
      deriv_D: "derivable_list D Ps \<sigma>' SuperCalc.FirstOrder C'" and
      "\<sigma> \<doteq> \<sigma>' \<lozenge> \<sigma>" and
      "SuperCalc.trms_subsumes D C \<sigma>"
      using lifting_lemma_derivable_list by blast

    have fin_Ps: "list_all (finite \<circ> cl_ecl) Ps"
      using Ball_set P_eq P_subset by fastforce

    let ?renamed_Ps = "map2 subst_ecl Ps (renamings_apart (map (Abs_fset \<circ> cl_ecl) Ps))"

    have all2_renaming_Ps: "list_all2 renaming_cl Ps ?renamed_Ps"
      using deriv_C_Ps[unfolded derivable_list_def]
    proof (elim disjE exE conjE)
      fix P1 assume Ps_def: "Ps = [P1]"
      then obtain \<rho> where ren_apa_eq: "renamings_apart [Abs_fset (cl_ecl P1)] = [\<rho>]"
        using renamings_apart_length by (metis length_0_conv length_Suc_conv)
      hence "renaming \<rho> (vars_of_cl (fset (Abs_fset (cl_ecl P1))))"
        using renamings_apart_renaming[of "[Abs_fset (cl_ecl P1)]"] by simp
      hence "renaming \<rho> (vars_of_cl (cl_ecl P1))"
        by (metis Abs_fset_inverse P_eq P_subset Ps_def all_finite_N' list.set_intros(1)
            mem_Collect_eq subsetD)
      then show ?thesis
        by (auto simp add: Ps_def ren_apa_eq renaming_cl_def)
    next
      fix P1 assume Ps_def: "Ps = [P1]"
      then obtain \<rho> where ren_apa_eq: "renamings_apart [Abs_fset (cl_ecl P1)] = [\<rho>]"
        using renamings_apart_length by (metis length_0_conv length_Suc_conv)
      hence "renaming \<rho> (vars_of_cl (fset (Abs_fset (cl_ecl P1))))"
        using renamings_apart_renaming[of "[Abs_fset (cl_ecl P1)]"] by simp
      hence "renaming \<rho> (vars_of_cl (cl_ecl P1))"
        by (metis Abs_fset_inverse P_eq P_subset Ps_def all_finite_N' list.set_intros(1)
            mem_Collect_eq subsetD)
      then show ?thesis
        by (auto simp add: Ps_def ren_apa_eq renaming_cl_def)
    next
      fix P1 P2 assume Ps_def: "Ps = [P1, P2]"
      then obtain \<rho>1 \<rho>2 where
        ren_apa_eq: "renamings_apart [Abs_fset (cl_ecl P1), Abs_fset (cl_ecl P2)] = [\<rho>1, \<rho>2]"
        using renamings_apart_length
        by (smt (verit, ccfv_threshold) length_0_conv length_0_conv length_0_conv length_Suc_conv
            length_Suc_conv length_Suc_conv)
      hence
        "renaming \<rho>1 (vars_of_cl (fset (Abs_fset (cl_ecl P1))))" and
        "renaming \<rho>2 (vars_of_cl (fset (Abs_fset (cl_ecl P2))))"
        using renamings_apart_renaming[of "[Abs_fset (cl_ecl P1), Abs_fset (cl_ecl P2)]"]
        by simp_all
      hence "renaming \<rho>1 (vars_of_cl (cl_ecl P1)) \<and> renaming \<rho>2 (vars_of_cl (cl_ecl P2))"
        by (metis (no_types, lifting) Abs_fset_inverse P_eq P_subset Ps_def cl_ecl.simps fset
            imageE list.set_intros(1) list.set_intros(2) subset_iff)
      then show ?thesis
        by (auto simp add: Ps_def ren_apa_eq renaming_cl_def)
    qed

    obtain E \<sigma>\<^sub>E E' where
      deriv_E: "derivable_list E (map2 subst_ecl Ps (renamings_apart (map (Abs_fset \<circ> cl_ecl) Ps)))
        \<sigma>\<^sub>E SuperCalc.FirstOrder E'" and "renaming_cl D E"
      using derivable_list_if_renaming[OF deriv_D all2_renaming_Ps fin_Ps]
      by blast

    define \<iota> where
      "\<iota> \<equiv> Infer (map (Abs_fset \<circ> cl_ecl) Ps) (Abs_fset (subst_cl E' \<sigma>\<^sub>E))"

    define \<iota>\<^sub>\<G> where
      "\<iota>\<^sub>\<G> \<equiv> Infer (map (Abs_fset \<circ> (\<lambda>P. subst_cl P \<sigma>) \<circ> cl_ecl) Ps) (Abs_fset CC')"

    have map2_map: "map2 f (map h xs) ys = map2 (\<lambda>x. f (h x)) xs ys" for f h xs ys
      using map_zip_map
      by (simp add: map_zip_map)

    have
      "map2 (\<lambda>x y. Ecl (subst_cl (fset x) y) {}) (map (Abs_fset \<circ> cl_ecl) Ps)
        (renamings_apart (map (Abs_fset \<circ> cl_ecl) Ps)) =
       map2 (\<lambda>x y. Ecl (subst_cl (fset (Abs_fset (cl_ecl x))) y) {}) Ps
        (renamings_apart (map (Abs_fset \<circ> cl_ecl) Ps))"
      by (simp add: map2_map comp_def)
    also have "... = map2 (\<lambda>x y. Ecl (subst_cl (cl_ecl x) y) {}) Ps
      (renamings_apart (map (Abs_fset \<circ> cl_ecl) Ps))"
      apply (rule map2_cong0)
      apply simp
      using Abs_fset_inverse[simplified, OF ball_fin_P[unfolded P_eq, rule_format]]
      by (metis set_zip_leftD)
    also have "... = map2 (\<lambda>x y. Ecl (cl_ecl (subst_ecl x y)) {}) Ps
      (renamings_apart (map (Abs_fset \<circ> cl_ecl) Ps))"
      by (simp add: cl_ecl_subst_ecl_distrib[symmetric])
    also have "... = map (\<lambda>x. Ecl (cl_ecl x) {}) (map2 subst_ecl Ps
      (renamings_apart (map (Abs_fset \<circ> cl_ecl) Ps)))"
      by auto
    finally have FOO:
      "map2 (\<lambda>x y. Ecl (subst_cl (fset x) y) {})
        (map (Abs_fset \<circ> cl_ecl) Ps) (renamings_apart (map (Abs_fset \<circ> cl_ecl) Ps)) =
       map (\<lambda>x. Ecl (cl_ecl x) {})
        (map2 subst_ecl Ps (renamings_apart (map (Abs_fset \<circ> cl_ecl) Ps)))"
      by simp

    have \<iota>\<^sub>\<G>_in_\<G>_I_\<iota>: "\<iota>\<^sub>\<G> \<in> \<G>_I (fset ` N') \<iota>"
      unfolding \<G>_I_def mem_Collect_eq
    proof (intro conjI)
      have *: "map (\<lambda>x. Ecl (fset (Abs_fset (subst_cl (cl_ecl x) \<sigma>))) {}) Ps =
        map (\<lambda>x. Ecl (subst_cl (cl_ecl x) \<sigma>) {}) Ps"
        using Abs_fset_inverse[simplified]
        by (smt (verit, ccfv_SIG) P_eq ball_fin_P map_eq_conv substs_preserve_finiteness)
      
      have ball_ground_clause: "\<forall>D\<in>set Ps. ground_clause (fset (Abs_fset (subst_cl (cl_ecl D) \<sigma>)))"
        using grounding_P
        by (simp add: Abs_fset_inverse P_eq SuperCalc.grounding_set_def ball_fin_P
            substs_preserve_finiteness)
      thus "\<iota>\<^sub>\<G> \<in> G_Inf (fset ` N')"
        unfolding G_Inf_def mem_Collect_eq
        unfolding \<iota>\<^sub>\<G>_def
        using G_deriv_CC_Ps_\<sigma>
        by (auto simp: comp_def *)
    next
      show "\<exists>\<gamma>s. prems_of \<iota>\<^sub>\<G> = map2 (\<lambda>x y. Abs_fset (subst_cl (fset x) y)) (prems_of \<iota>) \<gamma>s \<and>
        length (prems_of \<iota>) = length \<gamma>s"
        sorry
    next
      have "finite (subst_cl C' \<sigma>)"
        using SuperCalc.derivable_finite_conclusion ball_fin_P deriv_C_P substs_preserve_finiteness
        by blast
      have "finite (subst_cl E' \<sigma>\<^sub>E)"
        unfolding derivable_list_concl_conv[OF deriv_E, symmetric]
        unfolding finite_cl_ecl_iff_renaming_cl[OF \<open>renaming_cl D E\<close>, symmetric]
        by (metis P_eq ball_fin_P deriv_D derivable_list_concl_conv derivable_list_finite_conclusion
            substs_preserve_finiteness)
      hence fin: "finite (subst_cl (subst_cl E' \<sigma>\<^sub>E) \<gamma>)" for \<gamma>
        by (rule substs_preserve_finiteness)
      show "\<exists>\<gamma>. concl_of \<iota>\<^sub>\<G> = Abs_fset (subst_cl (fset (concl_of \<iota>)) \<gamma>)"
        unfolding \<iota>\<^sub>\<G>_def \<iota>_def inference.sel
        unfolding Abs_fset_inverse[of "subst_cl E' \<sigma>\<^sub>E", simplified, OF \<open>finite (subst_cl E' \<sigma>\<^sub>E)\<close>]
        unfolding Abs_fset_inject[of "subst_cl C' \<sigma>" "subst_cl (subst_cl E' \<sigma>\<^sub>E) \<gamma>" for \<gamma>,
            simplified, OF \<open>finite (subst_cl C' \<sigma>)\<close> fin]
        by (smt (verit, best) \<open>\<sigma> \<doteq> \<sigma>' \<lozenge> \<sigma>\<close> \<open>finite (subst_cl E' \<sigma>\<^sub>E)\<close> \<open>renaming_cl D E\<close>
            cl_ecl_subst_ecl_distrib composition_of_substs_cl deriv_D deriv_E
            derivable_list_concl_conv ex_renaming_swap finite_cl_ecl_iff_renaming_cl renaming_cl_def
            subst_eq_cl)
    qed

    have "\<iota> \<in> F_Inf"
      unfolding F_Inf_def mem_Collect_eq Let_def \<iota>_def
      apply simp
      using derivable_list_no_trms[OF deriv_E, unfolded FOO[symmetric]]
      by blast

    moreover have all_prems_in_N': "C \<in> N'" if C_in: "C \<in> set (prems_of \<iota>)" for C
    proof -
      from C_in obtain x where x_in: "x \<in> P" and C_eq: "C = Abs_fset (cl_ecl x)"
        using P_eq[symmetric] by (auto simp add: \<iota>_def image_iff)

      from x_in P_subset have "x \<in> (\<lambda>C. Ecl (fset C) {}) ` N'"
        by auto
      then show ?thesis
        unfolding image_iff C_eq by (auto simp add: fset_inverse)
    qed

    ultimately have "\<iota> \<in> (\<Inter>x. {\<iota> \<in> F_Inf. \<forall>t. t \<in> \<G>_I x \<iota> \<longrightarrow> t \<in> G.Red_I x (\<Union> (\<G>_F ` N'))})"
      using saturated_N'[unfolded F.saturated_def F.Inf_from_def F.Red_I_\<G>_def
          F.Red_I_\<G>_q_def, simplified, unfolded subset_iff mem_Collect_eq, rule_format]
      by auto
    hence "\<iota>\<^sub>\<G> \<in> \<G>_I x \<iota> \<Longrightarrow> \<iota>\<^sub>\<G> \<in> G.Red_I x (\<Union> (\<G>_F ` N'))" for \<iota>\<^sub>\<G> x
      by simp
    hence "\<iota>\<^sub>\<G> \<in> \<G>_I x \<iota> \<Longrightarrow> G.redundant_infer (\<Union> (\<G>_F ` N')) \<iota>\<^sub>\<G>" for \<iota>\<^sub>\<G> x
      unfolding G.Red_I_def mem_Collect_eq by simp
    moreover obtain \<iota>\<^sub>\<G> where "\<iota>\<^sub>\<G> \<in> \<G>_I (fset ` N') \<iota>"
      unfolding \<G>_I_def mem_Collect_eq
      unfolding G_Inf_def mem_Collect_eq
      using all_prems_in_N'
      sorry
    ultimately have "G.redundant_infer (\<Union> (\<G>_F ` N')) \<iota>\<^sub>\<G>"
      by simp
    then obtain DD where
      "DD \<subseteq> \<Union> (\<G>_F ` N')" and
      "finite DD" and
      "DD \<union> set (side_prems_of \<iota>\<^sub>\<G>) \<TTurnstile>e {concl_of \<iota>\<^sub>\<G>}" and
      ball_DD_smaller: "\<forall>D\<in>DD. fclause_ord D (main_prem_of \<iota>\<^sub>\<G>)"
      unfolding G.redundant_infer_def by auto
    
    define S' where
      "S' = fset ` DD \<union> fset ` set (side_prems_of \<iota>\<^sub>\<G>)"
    \<comment> \<open>@{term \<iota>\<^sub>\<G>} doit être basé sur la substitution @{term \<sigma>}\<close>
    \<comment> \<open>les clauses de DD peuvent être basé sur n'importe quelle substition grâce à
      @{thm ball_DD_smaller}\<close>
    \<comment> \<open>trouver un obtain DD' tel que tous les éléments sont une paire de clause et subst tel que
      plus haut\<close>

    show "SuperCalc.redundant_inference C ((\<lambda>C. Ecl (fset C) {}) ` N') P \<sigma>"
      unfolding SuperCalc.redundant_inference_def
      unfolding SuperCalc.derivable_clauses_lemma[OF deriv_C_P]
      using all_prems_in_N'
      sorry
    (* proof (intro exI conjI)
      show "S' \<subseteq> SuperCalc.instances (to_SuperCalc_ecl ` N')"
      unfolding SuperCalc.instances_def
      apply (intro exI conjI) *)
  qed

  have ball_well_constrained_N': "Ball ((\<lambda>C. Ecl (fset C) {}) ` N') SuperCalc.well_constrained"
    by (simp add: SuperCalc.well_constrained_def)

  have closed_renaming_N': "closed_under_renaming ((\<lambda>C. Ecl (fset C) {}) ` N')"
    unfolding N'_def by (fact closed_under_renaming_closure)

  define I where "I \<equiv> SuperCalc.same_values (\<lambda>t. SuperCalc.trm_rep t ((\<lambda>C. Ecl (fset C) {}) ` N'))"

  note int_clset_is_a_model' = SuperCalc.int_clset_is_a_model[OF gr_inf_satur_N' all_finite_N'
      ball_well_constrained_N' _ closed_renaming_N', folded I_def, of "(x, y)" for x y, simplified]

  have fo_int_I: "fo_interpretation I"
    unfolding I_def
    using SuperCalc.same_values_fo_int SuperCalc.trm_rep_compatible_with_structure by blast

  have "\<exists>B \<in> {{||}}. B \<in> N'"
  proof (rule contrapos_pp[OF \<open>N' \<TTurnstile>e {{||}}\<close>])
    assume "\<not> (\<exists>B \<in> {{||}}. B \<in> N')"
    hence ball_N_not_empty: "\<forall>C \<in> N'. fset C \<noteq> {}"
      by (metis B_def \<open>B \<in> {{||}}\<close> bot_fset.rep_eq fset_cong)
  
    have val_I_N': "validate_clause_set I (fset ` N')"
      unfolding validate_clause_set.simps validate_clause.simps
    proof (intro allI impI)
      fix C \<sigma>
      assume "C \<in> fset ` N'" and "ground_clause (subst_cl C \<sigma>)"
      thus "validate_ground_clause I (subst_cl C \<sigma>)"
        using int_clset_is_a_model'[OF ball_N_not_empty, of "Ecl C {}", simplified] by blast
    qed
  
    show "\<not> N' \<TTurnstile>e {{||}}"
    proof (rule notI)
      assume "N' \<TTurnstile>e {{||}}"
      hence "validate_ground_clause I {}"
        using fo_int_I val_I_N' by (simp add: entails_def set_entails_set_def)
      thus False
        by (simp add: validate_ground_clause.simps)
    qed
  qed
  thus "\<exists>B \<in> {{||}}. B \<in> N"
    apply (simp add: N'_def)
    by (metis bot_fset.rep_eq fimage.rep_eq fset_inverse image_is_empty subst_cl_conv)
qed

end

end
