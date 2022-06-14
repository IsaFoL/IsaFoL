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

(* sledgehammer_params [verbose, slices = 24] *)

term monotone


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

lemma
  assumes "inj_on f (set_mset M1 \<union> set_mset M2)"
  shows "image_mset f M1 = image_mset f M2 \<longleftrightarrow> M1 = M2"
  using assms
  by (metis (mono_tags, lifting) UnCI inj_onD multiset.inj_map_strong)

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

lemma monotone_multp_multp_image_mset:
  assumes "monotone R S f" and "transp R"
  shows "monotone (multp R) (multp S) (image_mset f)"
proof (rule monotoneI)
  fix M1 M2 assume "multp R M1 M2"
  with multp_implies_one_step[OF \<open>transp R\<close>] obtain I J K where
    M2_eq: "M2 = I + J" and
    M1_eq: "M1 = I + K" and
    J_neq_mempty: "J \<noteq> {#}" and
    ball_K_less: "\<forall>k\<in>#K. \<exists>x\<in>#J. R k x"
    by metis

  have "multp S (image_mset f I + image_mset f K) (image_mset f I + image_mset f J)"
  proof (rule one_step_implies_multp)
    show "image_mset f J \<noteq> {#}"
      using J_neq_mempty by simp
  next
    show "\<forall>k\<in>#image_mset f K. \<exists>j\<in>#image_mset f J. S k j"
      using \<open>monotone R S f\<close>[THEN monotoneD] ball_K_less by fastforce
  qed
  thus "multp S (image_mset f M1) (image_mset f M2)"
    by (simp add: M1_eq M2_eq)
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
          unfolding I_def by blast
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
    by (auto simp: I_def dest: image_mset_eq_image_mset_plusD[OF inj_on_f'])

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

text \<open>Idempotent MGU\<close>

definition IMGU :: "'a subst \<Rightarrow> 'a trm \<Rightarrow> 'a trm \<Rightarrow> bool" where
  "IMGU \<mu> t u \<longleftrightarrow> Unifier \<mu> t u \<and> (\<forall>\<theta>. Unifier \<theta> t u \<longrightarrow> \<theta> \<doteq> \<mu> \<lozenge> \<theta>)"

lemma IMGU_iff_Idem_and_MGU: "IMGU \<mu> t u \<longleftrightarrow> Idem \<mu> \<and> MGU \<mu> t u"
  unfolding IMGU_def Idem_def MGU_def
  by (smt (verit, best) subst_comp subst_eq_def)

lemma unify_computes_IMGU:
  "unify M N = Some \<sigma> \<Longrightarrow> IMGU \<sigma> M N"
  by (simp add: IMGU_iff_Idem_and_MGU unify_computes_MGU unify_gives_Idem)

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

lemma assoc_eq_map_of_or_default: "assoc x y xs = (case map_of xs x of None \<Rightarrow> y | Some z \<Rightarrow> z)"
  by (induction xs) auto

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

lemma singleton_subst_li_conv: "{equational_clausal_logic.subst_lit L1 \<sigma>} = subst_cl {L1} \<sigma>"
  unfolding subst_cl.simps
  by simp

lemma
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
    by (rule unif_t_u[THEN ck_unifier_thm])
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

lemma from_SuperCalc_cl_empty[simp]: "from_SuperCalc_cl {} = {#}"
  by (simp add: from_SuperCalc_cl_def)

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
    select_renaming_strong: "\<forall>\<eta> C. renaming \<eta> (vars_of_cl C) \<longrightarrow> select (subst_cl C \<eta>) = subst_cl (select C) \<eta>" and
    infinite_vars: "infinite (UNIV :: 'a set)"
begin

text \<open>
These simplification rules often hurt more than they help.
Better to remove it and selectively add them tho @{method simp} when necessary.
\<close>

lemmas [simp del] = equational_clausal_logic.ground_clause.simps
lemmas [simp del] = equational_clausal_logic.subst_cl.simps
lemmas [simp del] = equational_clausal_logic.validate_ground_clause.simps
lemmas [simp del] = equational_clausal_logic.vars_of_cl.simps
lemmas [simp del] = terms.subst_set.simps

lemma subst_lit_from_SuperCalc_lit_swap: "subst_lit (from_SuperCalc_lit L) \<sigma> =
  from_SuperCalc_lit (equational_clausal_logic.subst_lit L \<sigma>)" for L \<sigma>
  by (cases L) simp_all

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
  "G_Inf M \<equiv> {Infer (map from_SuperCalc_cl Ps) (from_SuperCalc_cl (subst_cl C' \<sigma>)) | Ps C \<sigma> C'.
    (\<forall>D \<in> set Ps. finite D \<and> ground_clause D) \<and>
    G_derivable_list M C (map (\<lambda>C. Ecl C {}) Ps) \<sigma> G_SuperCalc.Ground C'}"

lemma count_concl_of_G_Inf_le_1:
  assumes "\<iota>g \<in> G_Inf M"
  shows "count (concl_of \<iota>g) x \<le> 1"
proof -
  from assms obtain Ps \<sigma> C' where
     \<iota>g_def: "\<iota>g = Infer (map from_SuperCalc_cl Ps) (from_SuperCalc_cl (subst_cl C' \<sigma>))"
    by (auto simp: G_Inf_def)

  show ?thesis
    using inj_on_subset[OF inj_from_SuperCalc_lit subset_UNIV]
    apply (simp add: \<iota>g_def from_SuperCalc_cl_def image_mset_mset_set)
    by (metis One_nat_def count_mset_set_le_one)
qed

lemma count_prem_of_G_Inf_le_1:
  assumes \<iota>g_in: "\<iota>g \<in> G_Inf M" and P_in: "P \<in> set (prems_of \<iota>g)"
  shows "count P x \<le> 1"
proof -
  from \<iota>g_in obtain Ps \<sigma> C' where
     \<iota>g_def: "\<iota>g = Infer (map from_SuperCalc_cl Ps) (from_SuperCalc_cl (subst_cl C' \<sigma>))"
    by (auto simp: G_Inf_def)

  from P_in \<iota>g_def obtain P' where
    "P' \<in> set Ps" and P_def: "P = from_SuperCalc_cl P'"
    by auto
  hence "P = mset_set (from_SuperCalc_lit ` P')"
    by (simp add: from_SuperCalc_cl_def image_mset_mset_set)
  thus ?thesis
    by (meson count_mset_set_le_one)
qed

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
    \<iota>_def: "\<iota> = Infer (map from_SuperCalc_cl Ps) (from_SuperCalc_cl (subst_cl C' \<sigma>))" and
    Ps_ground: "\<forall>C \<in> set Ps. finite C \<and> ground_clause C" and
    deriv_Ps: "G_derivable_list M C (map (\<lambda>C. Ecl C {}) Ps) \<sigma> G_SuperCalc.Ground C'"
    by blast

  have ground_C': "ground_clause C'"
    using Ps_ground
    by (auto intro!: G_derivable_list_ground_premises[OF _ deriv_Ps])

  have "fclause_ord (from_SuperCalc_cl C') (from_SuperCalc_cl (last Ps))"
    using deriv_Ps[unfolded G_derivable_list_def]
  proof (elim disjE exE conjE)
    fix P1
    assume map_Ps_conv: "map (\<lambda>C. Ecl C {}) Ps = [P1]" and
      refl_P1: "G_SuperCalc.reflexion M P1 C \<sigma> G_SuperCalc.Ground C'"
    with Ps_ground have fin_P1: "finite (cl_ecl P1)" and ground_P1: "ground_clause (cl_ecl P1)"
      by auto

    from map_Ps_conv have last_Ps_conv: "last Ps = cl_ecl P1"
      by force

    from fin_P1 refl_P1 have fin_C': "finite C'"
      using G_SuperCalc.reflexion_preserves_finiteness by blast

    show ?thesis
      unfolding fclause_ord_def to_from_SuperCalc_cl[OF fin_C'] last_Ps_conv
      using G_SuperCalc.reflexion_conclusion_smaller[OF refl_P1 fin_P1]
      using ground_C' ground_P1
      by (metis G_SuperCalc.cl_ord_ground_subst fin_P1 to_from_SuperCalc_cl)
  next
    fix P1
    assume
      map_Ps_conv: "map (\<lambda>C. Ecl C {}) Ps = [P1]" and
      fact_P1: "G_SuperCalc.factorization M P1 C \<sigma> G_SuperCalc.Ground C'"
    with Ps_ground have fin_P1: "finite (cl_ecl P1)" and ground_P1: "ground_clause (cl_ecl P1)"
      by auto

    from map_Ps_conv have last_Ps_conv: "last Ps = cl_ecl P1"
      by force

    from fin_P1 fact_P1 have fin_C': "finite C'"
      using G_SuperCalc.factorization_preserves_finiteness by blast

    show "fclause_ord (from_SuperCalc_cl C') (from_SuperCalc_cl (last Ps))"
      unfolding fclause_ord_def to_from_SuperCalc_cl[OF fin_C'] last_Ps_conv
      using G_SuperCalc.factorization_conclusion_smaller[OF fact_P1 fin_P1]
      using G_SuperCalc.trm_ord_total_on_ground_clause
      using ground_C' ground_P1
      by (metis G_SuperCalc.cl_ord_ground_subst fin_P1 to_from_SuperCalc_cl)
  next
    fix P1 P2
    assume
      map_Ps_conv: "map (\<lambda>C. Ecl C {}) Ps = [P2, P1]" and
      super_P1_P2: "G_SuperCalc.superposition M P1 P2 C \<sigma> G_SuperCalc.Ground C'"
    with Ps_ground have
      fin_P1: "finite (cl_ecl P1)" and ground_P1: "ground_clause (cl_ecl P1)" and
      fin_P2: "finite (cl_ecl P2)" and ground_P2: "ground_clause (cl_ecl P2)"
      by auto

    from fin_P1 fin_P2 super_P1_P2 have fin_C': "finite C'"
      using G_SuperCalc.superposition_preserves_finiteness by blast

    from map_Ps_conv have last_Ps_conv: "last Ps = cl_ecl P1"
      by force

    have "((C', \<sigma>), cl_ecl P1, \<sigma>) \<in> G_SuperCalc.cl_ord"
    proof (rule G_SuperCalc.superposition_conclusion_smaller[OF super_P1_P2 fin_P1 fin_P2])
      show "Relation.total_on (\<Union> (case_equation (\<lambda>t1 t2. {t1, t2}) ` atom ` cl_ecl P2)) trm_ord"
        using G_SuperCalc.trm_ord_total_on_ground_clause ground_P2 by blast
    qed
    thus "fclause_ord (from_SuperCalc_cl C') (from_SuperCalc_cl (last Ps))"
      unfolding fclause_ord_def to_from_SuperCalc_cl[OF fin_C'] to_from_SuperCalc_cl[OF fin_P1]
        last_Ps_conv
      by (rule G_SuperCalc.cl_ord_ground_subst[OF _ ground_C' ground_P1])
  qed

  thus ?thesis
    unfolding \<iota>_def inference.sel
    unfolding substs_preserve_ground_clause[OF ground_C']
    using G_derivable_list_non_empty_premises[OF deriv_Ps, simplified]
    by (simp add: last_map)
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
        ground_clause.simps validate_ground_clause.simps vars_of_cl.simps)
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
  then obtain Ps C \<sigma> C' where
    \<iota>_def: "\<iota> = Infer (map from_SuperCalc_cl Ps) (from_SuperCalc_cl (subst_cl C' \<sigma>))" and
    ball_Ps_ground: "\<forall>C \<in> set Ps. finite C \<and> ground_clause C" and
    deriv_Ps: "G_derivable_list M C (map (\<lambda>C. Ecl C {}) Ps) \<sigma> G_SuperCalc.Ground C'"
    unfolding G_Inf_def mem_Collect_eq by blast

  from deriv_Ps have cl_ecl_C_conv: "cl_ecl C = subst_cl C' \<sigma>"
    by (simp add: G_derivable_list_concl_conv)

  have "finite (subst_cl C' \<sigma>)"
    apply (rule substs_preserve_finiteness)
    apply (rule G_derivable_list_finite_conclusion[OF _ deriv_Ps])
    using ball_Ps_ground by simp
  hence to_from_SuperCalc_cl_subst_C':
    "to_SuperCalc_cl (from_SuperCalc_cl (subst_cl C' \<sigma>)) = subst_cl C' \<sigma>"
    by simp

  have to_SuperCalc_cl_set_P_conv: "set Ps = cl_ecl ` set (map (\<lambda>C. Ecl C {}) Ps)"
    by (simp add: image_comp)

  from deriv_Ps show "set (prems_of \<iota>) \<TTurnstile>e {concl_of \<iota>}"
    unfolding G_derivable_list_def
  proof (elim disjE exE conjE)
    fix P1 P2
    assume
      map_P_conv: "map (\<lambda>C. Ecl C {}) Ps = [P2, P1]" and
      super_P1_P2: "G_SuperCalc.superposition M P1 P2 C \<sigma> G_SuperCalc.Ground C'"
    hence "set_entails_clause {cl_ecl P1, cl_ecl P2} (cl_ecl C)"
      using ball_Ps_ground
      by (auto intro: G_SuperCalc.superposition_is_sound)
    then show "set (prems_of \<iota>) \<TTurnstile>e {concl_of \<iota>}"
      using ball_Ps_ground
      by (simp add: entails_def \<iota>_def cl_ecl_C_conv to_from_SuperCalc_cl_subst_C'
          to_SuperCalc_cl_set_P_conv[unfolded map_P_conv] insert_commute)
  next
    fix P1
    assume
      map_P_conv: "map (\<lambda>C. Ecl C {}) Ps = [P1]" and
      fact_P1: "G_SuperCalc.factorization M P1 C \<sigma> G_SuperCalc.Ground C'"
    hence "clause_entails_clause (cl_ecl P1) (cl_ecl C)"
      using ball_Ps_ground
      by (auto intro: G_SuperCalc.factorization_is_sound)
    then show "set (prems_of \<iota>) \<TTurnstile>e {concl_of \<iota>}"
      using ball_Ps_ground
      by (simp add: entails_def \<iota>_def cl_ecl_C_conv to_from_SuperCalc_cl_subst_C'
          to_SuperCalc_cl_set_P_conv[unfolded map_P_conv])
  next
    fix P1
    assume
      map_P_conv: "map (\<lambda>C. Ecl C {}) Ps = [P1]" and
      refl_P1: "G_SuperCalc.reflexion M P1 C \<sigma> G_SuperCalc.Ground C'"
    hence "clause_entails_clause (cl_ecl P1) (cl_ecl C)"
      using ball_Ps_ground
      by (auto intro: G_SuperCalc.reflexion_is_sound)
    then show "set (prems_of \<iota>) \<TTurnstile>e {concl_of \<iota>}"
      using ball_Ps_ground
      by (simp add: entails_def \<iota>_def cl_ecl_C_conv to_from_SuperCalc_cl_subst_C'
          to_SuperCalc_cl_set_P_conv[unfolded map_P_conv])
  qed
qed

interpretation G: calculus_with_finitary_standard_redundancy "G_Inf M" "{{#}}" "(\<TTurnstile>e)" fclause_ord
  using wfP_fclause_ord transp_fclause_ord G_Inf_have_prems G_Inf_reductive
  by (unfold_locales)


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

  have "MGU (comp_subst_abbrev \<rho>_inv \<mu>) (Var x \<lhd> \<rho>) (Var y \<lhd> \<rho>)"
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

lemma subst_Var_ident_if_not_in_dom: "x \<notin> fst ` set \<sigma> \<Longrightarrow> Var x \<lhd> \<sigma> = Var x"
  by (metis assoc.simps(1) assoc_eq_map_of_or_default empty_iff image_empty list.set(1)
      map_of_eq_None_iff subst.simps(1))

lemma subst_if_in_dom: "x \<in> fst ` set \<sigma> \<Longrightarrow> \<exists>p \<in> set \<sigma>. Var x \<lhd> \<sigma> = snd p"
  apply (induction \<sigma>)
   apply simp
  apply simp
  by force

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
  assumes inj_f: "inj_on f V" and
    "dom (map_of xs) \<subseteq> V" and
    "f k' = k" and "g v' = v" and "map_of xs k' = Some v'"
  shows "map_of (map (map_prod f g) xs) k = Some v"
  using assms(2,5-)
proof (induction xs)
  case Nil
  thus ?case by simp
next
  case (Cons x xs)
  show ?case 
  proof (cases "k = f (fst x)")
    case True
    with Cons.prems inj_f assms(3,4) show ?thesis
      by (smt (verit, best) domI inj_onD inj_on_subset list.simps(9) map_of_Cons_code(2)
          map_prod_simp option.sel prod.collapse)
  next
    case False
    with Cons assms(3,4) show ?thesis
      by (smt (verit, ccfv_SIG) domIff fst_map_prod fun_upd_apply list.simps(9) map_of.simps(2)
          option.simps(3) subset_iff)
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
    unfolding composition_of_substs Unification.agreement[of t]
  proof (rule ballI)
    fix x assume "x \<in> vars_of t"
    with \<open>vars_of t \<subseteq> V\<close> have "x \<in> V" by blast
    then obtain x' where x_\<rho>: "Var x \<lhd> \<rho> = Var x'"
      using all_var_\<rho> is_a_variable.elims(2) by blast
    hence x_\<rho>': "the_Var (Var x \<lhd> \<rho>) = x'" by force

    show "Var x \<lhd> \<rho> \<lozenge> \<mu>' = Var x \<lhd> \<mu> \<lozenge> \<rho>"
    proof (cases "x \<in> subst_domain \<mu>")
      case True
      then obtain v where "map_of \<mu> x = Some v" and "v \<noteq> Var x"
        unfolding subst_domain_def mem_Collect_eq
        apply (simp add: assoc_eq_map_of_or_default)
        by (metis option.case_eq_if option.collapse)
      hence "map_of \<mu>' x' = Some (v \<lhd> \<rho>)"
        using map_of_map_map_prod_eq_Some_if[
            of _ _ _ _ _ "\<lambda>v. v \<lhd> \<rho>", OF inj_\<rho>' dom_\<mu>' x_\<rho>' refl]
        by (simp add: \<mu>'_def)
      then show ?thesis
        unfolding composition_of_substs[symmetric] x_\<rho>
        by (simp add: assoc_eq_map_of_or_default \<open>map_of \<mu> x = Some v\<close>)
    next
      case False
      hence "Var x \<lhd> \<mu> = Var x"
        by (simp add: subst_domain_def)
      hence FOO: "map_of \<mu> x = None \<or> map_of \<mu> x = Some (Var x)"
        apply (simp add: assoc_eq_map_of_or_default)
        by (metis option.case_eq_if option.collapse)
      show ?thesis
        unfolding composition_of_substs[symmetric]
        unfolding assoc_ident_if_not_in_dom'[OF False]
        unfolding x_\<rho>
        apply (simp add: assoc_eq_map_of_or_default)
        unfolding \<mu>'_def
        using FOO
        apply (elim disjE)
        subgoal premises prem
          unfolding map_of_map_map_prod_eq_None_if[OF inj_\<rho>' dom_\<mu>' \<open>x \<in> V\<close> prem, unfolded x_\<rho>']
          by simp
        subgoal premises prem
          unfolding map_of_map_map_prod_eq_Some_if[OF inj_\<rho>' dom_\<mu>' x_\<rho>' refl prem]
          using x_\<rho> by simp
        done
    qed
  qed

  show "Unifier \<mu>' (t \<lhd> \<rho>) (u \<lhd> \<rho>)"
    using unif_\<mu> vars_t_u_subset
    by (simp add: Unifier_def *)
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

  show ?thesis
    unfolding x_\<rho>
    unfolding subst_Var_eq_map_of_or_default[of x] \<open>map_of \<sigma> x = Some v'\<close> option.case
    unfolding subst_Var_eq_map_of_or_default[of x']
    unfolding map_of_map_map_prod_eq_Some_if[OF inj_subst_\<rho>' dom_\<sigma> x_\<rho>' refl \<open>map_of \<sigma> x = Some v'\<close>]
      option.case
    by (rule refl)
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

definition range_vars where
  "range_vars \<sigma> = \<Union> {vars_of (Var x \<lhd> \<sigma>) |x. Var x \<lhd> \<sigma> \<noteq> Var x}"

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

lemma ck_unifier_of_renamed_if_ck_unifier:
  assumes "SuperCalc.ck_unifier t u \<mu> k" and
    ren_\<rho>: "renaming \<rho> V" and
    \<rho>_\<rho>_inv_ident: "\<forall>x\<in>V. Var x \<lhd> \<rho> \<lhd> \<rho>_inv = Var x" and
    vars_t_u_subset: "vars_of t \<union> vars_of u \<subseteq> V" and
    dom_\<mu>: "fst ` set \<mu> \<subseteq> V" and
    range_vars_\<mu>: "range_vars \<mu> \<subseteq> V" and
    "Idem \<mu>"
  defines "\<mu>' \<equiv> map (map_prod (\<lambda>x. the_Var (Var x \<lhd> \<rho>)) (\<lambda>v. v \<lhd> \<rho>)) \<mu>"
  shows "SuperCalc.ck_unifier (t \<lhd> \<rho>) (u \<lhd> \<rho>) \<mu>' k \<and> Idem \<mu>'"
proof -
  show ?thesis
  proof (cases k)
    case Ground
    moreover with assms(1) have "Unifier \<mu> t u"
      by (simp add: SuperCalc.ck_unifier_def)
    ultimately show ?thesis
      using Unifier_of_renamed_if_Unifier[OF ren_\<rho> vars_t_u_subset dom_\<mu>, folded \<mu>'_def]
      using Idem_of_subst_adapted_to_renaming[
          OF ren_\<rho> \<rho>_\<rho>_inv_ident dom_\<mu> range_vars_\<mu> \<open>Idem \<mu>\<close>, folded \<mu>'_def]
      by (simp add: SuperCalc.ck_unifier_def)
  next
    case FirstOrder
    moreover with assms(1) \<open>Idem \<mu>\<close> have "IMGU \<mu> t u"
      by (simp add: SuperCalc.ck_unifier_def IMGU_iff_Idem_and_MGU)
    ultimately show ?thesis
      using IMGU_of_renamed_if_IMGU[OF ren_\<rho> \<rho>_\<rho>_inv_ident vars_t_u_subset dom_\<mu>]
      by (simp add: \<mu>'_def SuperCalc.ck_unifier_def IMGU_iff_Idem_and_MGU)
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


lemma reflexion_if_renaming:
  fixes \<sigma>
  assumes
    refl: "SuperCalc.reflexion P1 C \<sigma>\<^sub>C k C'" and
    ren: "renaming_cl P1 P1'" and
    fin_P1: "finite (cl_ecl P1)" and
    trms_P1_subset:"(\<Union>t \<in> trms_ecl P1. vars_of t) \<subseteq> vars_of_cl (cl_ecl P1)" and
    trms_ecl_P1_empty: "trms_ecl P1 = {}" and
    range_vars_\<sigma>\<^sub>C: "range_vars \<sigma>\<^sub>C \<subseteq> vars_of_cl (cl_ecl P1)" and
    dom_vars_\<sigma>\<^sub>C: "fst ` set \<sigma>\<^sub>C \<subseteq> vars_of_cl (cl_ecl P1)" and
    "Idem \<sigma>\<^sub>C"
  shows "\<exists>D \<sigma>\<^sub>D D'. SuperCalc.reflexion P1' D \<sigma>\<^sub>D k D' \<and>
    renaming_cl C D \<and>
    range_vars \<sigma>\<^sub>D \<subseteq> vars_of_cl (cl_ecl P1') \<and>
    fst ` set \<sigma>\<^sub>D \<subseteq> vars_of_cl (cl_ecl P1') \<and>
    Idem \<sigma>\<^sub>D"
proof -
  from refl obtain L1 t s Cl_P Cl_C trms_C where
    "SuperCalc.eligible_literal L1 P1 \<sigma>\<^sub>C" and
    "L1 \<in> cl_ecl P1" and
    "Cl_C = cl_ecl C" and
    Cl_P_def: "Cl_P = cl_ecl P1" and
    "SuperCalc.orient_lit_inst L1 t s neg \<sigma>\<^sub>C" and
    "SuperCalc.ck_unifier t s \<sigma>\<^sub>C k" and
    C_def: "C = Ecl Cl_C trms_C" and
    trms_C_def: "trms_C = SuperCalc.get_trms Cl_C
      (SuperCalc.dom_trms Cl_C (subst_set (trms_ecl P1 \<union> {t}) \<sigma>\<^sub>C)) k" and
    Cl_C_def: "Cl_C = subst_cl C' \<sigma>\<^sub>C" and
    C'_def: "C' = Cl_P - {L1}"
    unfolding SuperCalc.reflexion_def by blast

  from ren obtain \<rho> where
    ren_\<rho>: "renaming \<rho> (vars_of_cl (cl_ecl P1))" and
    P1'_def: "P1' = subst_ecl P1 \<rho>"
    unfolding renaming_cl_def by blast

  have vars_t_s_subset: "vars_of t \<union> vars_of s \<subseteq> vars_of_cl (cl_ecl P1)"
    using SuperCalc.orient_lit_inst_vars \<open>L1 \<in> cl_ecl P1\<close> \<open>SuperCalc.orient_lit_inst L1 t s neg \<sigma>\<^sub>C\<close>
    using vars_of_cl_lem by fastforce

  from fin_P1 have fin_vars_P1: "finite (vars_of_cl (cl_ecl P1))"
    using set_of_variables_is_finite_cl by blast
  with ren_\<rho> obtain \<rho>_inv where
    \<rho>_\<rho>_inv_ident: "\<forall>x\<in>vars_of_cl (cl_ecl P1). Var x \<lhd> \<rho> \<lhd> \<rho>_inv = Var x" and
      "\<forall>x. x \<notin> subst_codomain \<rho> (vars_of_cl (cl_ecl P1)) \<longrightarrow> Var x \<lhd> \<rho>_inv = Var x"
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

  have "SuperCalc.ck_unifier (t \<lhd> \<rho>) (s \<lhd> \<rho>) \<sigma>\<^sub>D k" and "Idem \<sigma>\<^sub>D"
    using ck_unifier_of_renamed_if_ck_unifier[OF \<open>SuperCalc.ck_unifier t s \<sigma>\<^sub>C k\<close> ren_\<rho> \<rho>_\<rho>_inv_ident
        vars_t_s_subset dom_vars_\<sigma>\<^sub>C range_vars_\<sigma>\<^sub>C \<open>Idem \<sigma>\<^sub>C\<close>, folded \<sigma>\<^sub>D_def]
    by simp_all
  hence "Unifier \<sigma>\<^sub>D (t \<lhd> \<rho>) (s \<lhd> \<rho>)"
    using SuperCalc.ck_unifier_thm Unifier_def by blast

  have subst_\<rho>_\<sigma>\<^sub>D_conv:
    "Var x \<lhd> \<rho> \<lhd> \<sigma>\<^sub>D = Var x \<lhd> \<sigma>\<^sub>C \<lhd> \<rho>" if x_in: "x \<in> vars_of_cl (cl_ecl P1)" for x
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
        (SuperCalc.dom_trms Cl_D (subst_set (trms_ecl P1' \<union> {t \<lhd> \<rho>}) \<sigma>\<^sub>D)) k))"

  have vars_of_L1_subset: "vars_of_lit L1 \<subseteq> vars_of_cl (cl_ecl P1)"
    using \<open>L1 \<in> cl_ecl P1\<close> vars_of_cl_lem by blast

  hence vars_of_t_s_subset:
    "vars_of t \<subseteq> vars_of_cl (cl_ecl P1)" "vars_of s \<subseteq> vars_of_cl (cl_ecl P1)"
    using \<open>SuperCalc.orient_lit_inst L1 t s neg \<sigma>\<^sub>C\<close>
    unfolding SuperCalc.orient_lit_inst_def
    by auto

  show ?thesis
  proof (intro exI conjI)
    show "SuperCalc.reflexion P1' D \<sigma>\<^sub>D k D'"
      unfolding SuperCalc.reflexion_def
    proof (intro exI conjI)
      show "equational_clausal_logic.subst_lit L1 \<rho> \<in> cl_ecl P1'"
        by (rule L1_\<rho>_in_P1')
    next
      show "SuperCalc.eligible_literal (equational_clausal_logic.subst_lit L1 \<rho>) P1' \<sigma>\<^sub>D"
        using \<open>SuperCalc.eligible_literal L1 P1 \<sigma>\<^sub>C\<close>[unfolded SuperCalc.eligible_literal_def]
      proof (elim disjE conjE)
        assume "L1 \<in> select (cl_ecl P1)"
        hence "equational_clausal_logic.subst_lit L1 \<rho> \<in> select (subst_cl (cl_ecl P1) \<rho>)"
          unfolding \<open>P1' = subst_ecl P1 \<rho>\<close> cl_ecl_subst_ecl_distrib
          using select_renaming_strong[rule_format, of \<rho> "cl_ecl P1", OF ren_\<rho>]
          by (simp add: subst_cl_conv)
        thus ?thesis
          unfolding SuperCalc.eligible_literal_def \<open>P1' = subst_ecl P1 \<rho>\<close> cl_ecl_subst_ecl_distrib
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
          unfolding subst_cl_\<rho>_\<sigma>\<^sub>D_conv subst_lit_\<rho>_\<sigma>\<^sub>D_conv[OF \<open>L1 \<in> cl_ecl P1\<close>]
        proof (intro allI impI)
          fix x assume x_in: "x \<in> subst_cl (subst_cl (cl_ecl P1) \<sigma>\<^sub>C) \<rho>"
          then obtain x' where
            x'_in: "x' \<in> subst_cl (cl_ecl P1) \<sigma>\<^sub>C" and
            x_def: "x = equational_clausal_logic.subst_lit x' \<rho>"
            by (metis (mono_tags, lifting) image_iff subst_cl_conv)

          have vars_of_x': "vars_of_lit x' \<subseteq> vars_of_cl (cl_ecl P1)"
            using x'_in
            apply (auto simp add: subst_cl.simps vars_of_subst_lit)
             apply (auto simp add: vars_of_cl.simps) [1]
            using range_vars_\<sigma>\<^sub>C unfolding range_vars_def
            by (smt (verit, ccfv_SIG) Cl_P_def Sup_upper insertI1 insert_absorb insert_subset
                mem_Collect_eq occs.simps(1) subsetD subst.simps(1) the_Var.simps vars_iff_occseq
                vars_of_cl_lem)

          have vars_of_L_\<sigma>\<^sub>C: "vars_of_lit (equational_clausal_logic.subst_lit L1 \<sigma>\<^sub>C) \<subseteq>
            vars_of_cl (cl_ecl P1)"
            unfolding vars_of_subst_lit
            using vars_of_L1_subset
            apply (auto simp del: vars_of_cl.simps)
            using range_vars_\<sigma>\<^sub>C unfolding range_vars_def
            by (smt (verit, best) Cl_P_def Sup_upper insert_absorb insert_subset mem_Collect_eq
                occs.simps(1) subst.simps(1) the_Var.simps vars_iff_occseq vars_of_L1_subset)

          show
            "(equational_clausal_logic.subst_lit (equational_clausal_logic.subst_lit L1 \<sigma>\<^sub>C) \<rho>, x)
              \<notin> SuperCalc.lit_ord"
            unfolding x_def
            using 2[unfolded SuperCalc.maximal_literal_def, rule_format, OF x'_in]
            apply (rule contrapos_nn)
            apply (rule subst_lit_renaming_ord_iff[THEN iffD1])
            apply (rule renaming_subset[OF _ ren_\<rho>])
            using vars_of_x' vars_of_L_\<sigma>\<^sub>C
            by (simp del: vars_of_cl.simps)
        qed
        ultimately show ?thesis
          unfolding SuperCalc.eligible_literal_def \<open>P1' = subst_ecl P1 \<rho>\<close> cl_ecl_subst_ecl_distrib
          by simp
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
      show "SuperCalc.ck_unifier (t \<lhd> \<rho>) (s \<lhd> \<rho>) \<sigma>\<^sub>D k"
        by (rule \<open>SuperCalc.ck_unifier (t \<lhd> \<rho>) (s \<lhd> \<rho>) \<sigma>\<^sub>D k\<close>)
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

    have INJ_lit:  "L1 \<in> cl_ecl P1 \<Longrightarrow> L2 \<in> cl_ecl P1 \<Longrightarrow> L1 \<noteq> L2 \<Longrightarrow>
      equational_clausal_logic.subst_lit L1 \<rho> \<noteq> equational_clausal_logic.subst_lit L2 \<rho>" for L1 L2
      using subst_lit_identI[OF \<rho>_\<rho>_inv_ident vars_of_cl_lem] by metis

    have singleton_subst_conv: "{t \<lhd> \<sigma>} = (\<lambda>t. t \<lhd> \<sigma>) ` {t}" for t \<sigma>
      by simp

    have singleton_subst_lit_conv: "{equational_clausal_logic.subst_lit L \<sigma>} =
      (\<lambda>L. equational_clausal_logic.subst_lit L \<sigma>) ` {L}" for L \<sigma>
      by blast

    have FOO: "cl_ecl (subst_ecl P1 \<rho>) - {equational_clausal_logic.subst_lit L1 \<rho>} =
      subst_cl (cl_ecl P1 - {L1}) \<rho>"
      unfolding cl_ecl_subst_ecl_distrib
    proof (rule Set.equalityI; rule subsetI)
      fix K
      assume "K \<in> subst_cl (cl_ecl P1) \<rho> - {equational_clausal_logic.subst_lit L1 \<rho>}"
      then show "K \<in> subst_cl (cl_ecl P1 - {L1}) \<rho>"
        apply simp
        using INJ_lit
        by (smt (verit, best) image_iff insert_Diff_single insert_iff subst_cl_conv)
    next
      fix K
      assume "K \<in> subst_cl (cl_ecl P1 - {L1}) \<rho>"
      then show "K \<in> subst_cl (cl_ecl P1) \<rho> - {equational_clausal_logic.subst_lit L1 \<rho>}"
        apply simp
        using INJ_lit
        by (smt (verit, best) DiffD1 DiffD2 \<open>L1 \<in> cl_ecl P1\<close> image_iff insertCI subst_cl_conv)
    qed

    have vars_of_cl_minus_subset: "vars_of_cl (C - D) \<subseteq> vars_of_cl C" for C D
      by (auto simp: vars_of_cl.simps)

    have trms_ecl_subst_ecl: "trms_ecl (subst_ecl C \<sigma>) = (\<lambda>t. t \<lhd> \<sigma>) ` trms_ecl C" for C \<sigma>
      by (cases C) auto

    have subst_set_comp: "subst_set N (\<sigma> \<lozenge> \<tau>) = subst_set (subst_set N \<sigma>) \<tau>" for N \<sigma> \<tau>
      by (simp add: subst_set_image_conv image_image)

    have vars_P1_t_subset: "\<Union> (vars_of ` (trms_ecl P1 \<union> {t})) \<subseteq> vars_of_cl (cl_ecl P1)"
      unfolding UN_subset_iff
    proof (rule ballI, unfold Un_iff, erule disjE)
      fix u
      show "u \<in> {t} \<Longrightarrow> vars_of u \<subseteq> vars_of_cl (cl_ecl P1)"
        using vars_of_t_s_subset(1) by simp
    next
      fix u
      show "u \<in> trms_ecl P1 \<Longrightarrow> vars_of u \<subseteq> vars_of_cl (cl_ecl P1)"
        using trms_P1_subset
        by blast
    qed

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
        by (simp add: singleton_subst_li_conv)
      also have "... = subst_cl (subst_cl (cl_ecl P1) \<rho> - subst_cl {L1} \<rho>) \<sigma>\<^sub>D"
        by (simp add: P1'_def cl_ecl_subst_ecl_distrib)
      also have "... = subst_cl (subst_cl (cl_ecl P1 - {L1}) \<rho>) \<sigma>\<^sub>D"
        using D'_def FOO P1'_def calculation by presburger
      also have "... = subst_cl (subst_cl (cl_ecl P1 - {L1}) \<sigma>\<^sub>C) \<rho>"
        using subst_lit_\<rho>_\<sigma>\<^sub>D_conv
        by (metis (mono_tags, lifting) DiffD1 composition_of_substs_cl composition_of_substs_lit
            image_cong subst_cl_conv)
      also have "... = subst_cl (subst_cl C' \<sigma>\<^sub>C) \<rho>"
        by (simp add: C'_def Cl_P_def)
      also have "... = subst_cl Cl_C \<rho>"
        by (simp add: Cl_C_def)
      finally have D'_\<sigma>\<^sub>D: "subst_cl D' \<sigma>\<^sub>D = subst_cl Cl_C \<rho>"
        by assumption

      moreover have "SuperCalc.get_trms (subst_cl D' \<sigma>\<^sub>D)
        (SuperCalc.dom_trms (subst_cl D' \<sigma>\<^sub>D) (subst_set (trms_ecl P1' \<union> {t \<lhd> \<rho>}) \<sigma>\<^sub>D)) k =
        {t \<lhd> \<rho> |t. t \<in> trms_C}" (is "?lhs = ?rhs")
      proof (rule Set.equalityI; rule Set.subsetI)
        fix x assume "x \<in> ?lhs"
        show "x \<in> ?rhs"
        proof (cases k)
          case Ground
          with \<open>x \<in> ?lhs\<close> obtain x' where
            x_def: "x = x' \<lhd> \<sigma>\<^sub>D" and
            x'_eq_or_in: "x' = t \<lhd> \<rho> \<or> x' \<in> trms_ecl P1'" and
            dom_trm_x: "SuperCalc.dom_trm x (subst_cl D' \<sigma>\<^sub>D)"
            by (auto simp add: trms_C_def SuperCalc.get_trms_def SuperCalc.dom_trms_def subst_set.simps)

          have "(\<Union>x\<in>vars_of t. vars_of (Var x \<lhd> \<sigma>\<^sub>C)) \<subseteq> vars_of_cl (cl_ecl P1)"
            unfolding UN_subset_iff
            using vars_of_subst_var_in_P1 vars_of_t_s_subset(1)
            by blast
          hence vars_of_t_\<sigma>\<^sub>C: "vars_of (t \<lhd> \<sigma>\<^sub>C) \<subseteq> vars_of_cl (cl_ecl P1)"
            unfolding vars_of_subst[of t \<sigma>\<^sub>C]
            using vars_t_s_subset range_vars_\<sigma>\<^sub>C
            by fast

          have vars_of_P_\<sigma>\<^sub>C: "vars_of_cl (subst_cl (cl_ecl P1 - {L1}) \<sigma>\<^sub>C) \<subseteq> vars_of_cl (cl_ecl P1)"
            unfolding vars_of_subst_cl
            by (smt (verit, ccfv_threshold) DiffD1 UN_iff Un_iff subsetD subsetI
                vars_of_cl_minus_subset vars_of_subst_var_in_P1)

          from x'_eq_or_in show ?thesis
            unfolding mem_Collect_eq
          proof (elim disjE)
            assume x'_def: "x' = t \<lhd> \<rho>"
            have x_def: "x = t \<lhd> \<sigma>\<^sub>C \<lhd> \<rho>"
              using x_def[unfolded x'_def]
              using subst_\<rho>_\<sigma>\<^sub>D_conv
              by (metis agreement subset_iff subst_comp vars_of_t_s_subset(1))
            moreover have "t \<lhd> \<sigma>\<^sub>C \<in> trms_C"
              unfolding trms_C_def Cl_C_def C'_def Cl_P_def
              unfolding SuperCalc.get_trms_def
              using dom_trm_x
              apply (auto simp add: Ground x_def SuperCalc.dom_trms_def subst_set.simps)
              unfolding C'_def[symmetric] Cl_P_def[symmetric]
              unfolding D'_\<sigma>\<^sub>D Cl_C_def
              apply (erule dom_trm_if_dom_trm_subst_renaming[
                      OF renaming_subset[OF _ ren_\<rho>] _, rotated])
              unfolding C'_def Cl_P_def
              using vars_of_t_\<sigma>\<^sub>C vars_of_P_\<sigma>\<^sub>C
              by simp
            ultimately show "\<exists>t. x = t \<lhd> \<rho> \<and> t \<in> trms_C"
              by auto
          next
            assume "x' \<in> trms_ecl P1'"
            hence False
              unfolding P1'_def trms_ecl_subst_ecl trms_ecl_P1_empty
              by simp
            thus "\<exists>t. x = t \<lhd> \<rho> \<and> t \<in> trms_C"
              by simp
          qed
        next
          case FirstOrder
          with \<open>x \<in> ?lhs\<close> have False
            by (simp add: trms_C_def SuperCalc.get_trms_def)
          thus ?thesis ..
        qed
      next
        fix x assume "x \<in> ?rhs"
        then obtain x' where "x = x' \<lhd> \<rho>" and "x' \<in> trms_C"
          by auto
        then show "x \<in> ?lhs"
          unfolding trms_C_def
          unfolding SuperCalc.get_trms_def
          apply (cases k)
          subgoal
            apply simp
            unfolding SuperCalc.dom_trms_def mem_Collect_eq trms_ecl_P1_empty subst_set.simps
            apply simp
            apply (rule conjI)
             apply (rule exI[of _ "t \<lhd> \<rho>"])
             apply (metis agreement subset_iff subst_\<rho>_\<sigma>\<^sub>D_conv subst_comp vars_of_t_s_subset(1))
            using SuperCalc.substs_preserve_dom_trm calculation by auto
          subgoal by simp
          done
      qed

      ultimately show "D = subst_ecl C \<rho>"
        by (simp add: \<open>C = Ecl Cl_C trms_C\<close> D_def)
    qed
  next
    have "range_vars \<sigma>\<^sub>D \<subseteq> (\<lambda>x. the_Var (Var x \<lhd> \<rho>)) ` range_vars \<sigma>\<^sub>C"
      by (rule range_vars_of_subst_adapted_to_renaming[OF ren_\<rho> dom_vars_\<sigma>\<^sub>C range_vars_\<sigma>\<^sub>C,
            folded \<sigma>\<^sub>D_def])
    also have "... \<subseteq> (\<lambda>x. the_Var (Var x \<lhd> \<rho>)) ` vars_of_cl (cl_ecl P1)"
      using range_vars_\<sigma>\<^sub>C by fast
    also have "... \<subseteq> vars_of_cl (cl_ecl (subst_ecl P1 \<rho>))"
      by (smt (verit, best) UN_iff cl_ecl_subst_ecl_distrib image_iff ren_\<rho> renaming_var_to_var
          subset_iff the_Var.simps vars_iff_occseq vars_of_cl_subst_renaming_conv)
    also have "... \<subseteq> vars_of_cl (cl_ecl P1')"
      by (simp add: P1'_def)
    finally show "range_vars \<sigma>\<^sub>D \<subseteq> vars_of_cl (cl_ecl P1')"
      by assumption
  next
    have dom_vars_\<sigma>\<^sub>D: "fst ` set \<sigma>\<^sub>D \<subseteq> (\<lambda>x. the_Var (Var x \<lhd> \<rho>)) ` fst ` set \<sigma>\<^sub>C"
      by (rule dom_of_subst_adapted_to_renaming[OF ren_\<rho> dom_vars_\<sigma>\<^sub>C, folded \<sigma>\<^sub>D_def])
    also have "... \<subseteq> (\<lambda>x. the_Var (Var x \<lhd> \<rho>)) ` vars_of_cl (cl_ecl P1)"
      using dom_vars_\<sigma>\<^sub>C by blast
    also have "... \<subseteq> vars_of_cl (subst_cl (cl_ecl P1) \<rho>)"
      using ren_\<rho> renaming_var_to_var vars_of_cl_subst_renaming_conv by fastforce
    also have "... \<subseteq> vars_of_cl (cl_ecl P1')"
      by (simp add: P1'_def cl_ecl_subst_ecl_distrib)
    finally show "fst ` set \<sigma>\<^sub>D \<subseteq> vars_of_cl (cl_ecl P1')"
      by assumption
  next
    show "Idem \<sigma>\<^sub>D"
      by (rule \<open>Idem \<sigma>\<^sub>D\<close>)
  qed
qed


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
    let Ps' = map to_SuperCalc_ecl (Map2.map2 subst_cls Ps (renamings_apart Ps)) in
    derivable_list C Ps' \<sigma> SuperCalc.FirstOrder C' \<and>
    fst ` set \<sigma> \<subseteq> \<Union> (vars_of_cl ` cl_ecl ` set Ps') \<and>
    range_vars \<sigma> \<subseteq> \<Union> (vars_of_cl ` cl_ecl ` set Ps') \<and>
    Idem \<sigma>}"

lemma F_Inf_have_prems: "\<iota> \<in> F_Inf \<Longrightarrow> prems_of \<iota> \<noteq> []"
  by (auto simp: F_Inf_def derivable_list_def)

interpretation F: inference_system F_Inf .

definition \<G>_F :: "'a equation Clausal_Logic.clause \<Rightarrow> 'a equation Clausal_Logic.clause set" where
  "\<G>_F C \<equiv> {from_SuperCalc_cl (subst_cl (to_SuperCalc_cl C) \<gamma>) | \<gamma>.
    ground_on (vars_of_cl (to_SuperCalc_cl C)) \<gamma>}"

lemma \<G>_F_mempty[simp]: "\<G>_F {#} = {{#}}"
  using ground_subst_exists[OF finite.emptyI]
  by (simp add: \<G>_F_def from_SuperCalc_cl_def vars_of_cl.simps ground_on_def)

definition \<G>_I where
  "\<G>_I M \<iota> \<equiv> {\<iota>' \<in> G_Inf M.
    (\<exists>\<gamma>s. prems_of \<iota>' = map (mset_set \<circ> set_mset) (subst_cls_lists (prems_of \<iota>) \<gamma>s)) \<and>
    (\<exists>\<gamma>. concl_of \<iota>' = mset_set (set_mset (subst_cls (concl_of \<iota>) \<gamma>)))}"

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

      obtain \<gamma> where concl_\<iota>'_conv:"concl_of \<iota>' = mset_set (set_mset (subst_cls (concl_of \<iota>) \<gamma>))"
        using \<iota>'_grounding[unfolded \<G>_I_def mem_Collect_eq]
        by metis
      
      show "\<iota>' \<in> G.Red_I M (\<G>_F (concl_of \<iota>))"
        apply (rule G.Red_I_of_Inf_to_N[OF \<iota>'_in])
        unfolding \<G>_F_def Let_def mem_Collect_eq
      proof (intro exI[of _ \<gamma>] conjI)
        show "concl_of \<iota>' = from_SuperCalc_cl (subst_cl (to_SuperCalc_cl (concl_of \<iota>)) \<gamma>)"
          unfolding concl_\<iota>'_conv
          by (smt (verit, best) G_Inf_def \<iota>'_in concl_\<iota>'_conv finite.intros(1) finite_set_mset
              finite_set_mset_mset_set from_SuperCalc_cl_def inference.sel(2) mem_Collect_eq
              mset_set.empty mset_set.infinite to_SuperCalc_cl_def to_SuperCalc_cl_subst_cls
              to_from_SuperCalc_cl)
      next
        show "ground_on (vars_of_cl (to_SuperCalc_cl (concl_of \<iota>))) \<gamma> "
          by (metis G_Inf_ground_concl \<iota>'_in concl_\<iota>'_conv finite_set_mset finite_set_mset_mset_set
              ground_clauses_and_ground_substs to_SuperCalc_cl_subst_cls to_SuperCalc_cl_def)
      qed
    qed
    thus "the ((Some \<circ> \<G>_I M) \<iota>) \<subseteq> G.Red_I M (\<G>_F (concl_of \<iota>))"
      by simp
  next
    show "po_on (\<lambda>_ _. False) UNIV"
      by (simp add: irreflp_onI po_onI transp_onI)
  next
    show "\<And>M C. \<G>_F C \<inter> {{#}} \<noteq> {} \<longrightarrow> C \<in> {{#}}"
      using \<G>_F_def ground_subst_exists vars_of_cl.simps
      by (smt (verit, ccfv_SIG) disjoint_iff_not_equal finite_to_SuperCalc_cl mem_Collect_eq
          set_mset_eq_empty_iff singletonD subst_cls_empty_iff to_SuperCalc_cl_eq_conv
          to_SuperCalc_cl_subst_cls to_from_SuperCalc_cl)
  qed (auto simp add: )
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

lemma finite_vars_of_to_SuperCalc_cl[simp]: "finite (vars_of_cl (to_SuperCalc_cl C))"
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

lemma map_eq_ConsD: "map f xs = y # ys \<Longrightarrow> \<exists>x xs'. xs = x # xs'"
  by (induction xs) simp_all

lemma saturated_renamings:
  assumes "F.saturated N"
  defines "N' \<equiv> {subst_cls C \<sigma> | C \<sigma>. C \<in> N \<and> renaming \<sigma> (vars_of_cl (to_SuperCalc_cl C))}"
  shows "F.saturated N'"
proof -
  have "N \<subseteq> N'"
  proof (rule Set.subsetI)
    fix C
    show "C \<in> N \<Longrightarrow> C \<in> N'"
      unfolding N'_def Set.mem_Collect_eq
      by (auto intro!: exI[of _ C] exI[of _ "[]"])
  qed

  from \<open>F.saturated N\<close> have sat_N_alt: "\<And>\<iota>. \<iota> \<in> F_Inf \<Longrightarrow> set (prems_of \<iota>) \<subseteq> N \<Longrightarrow> \<iota> \<in> F.Red_I_\<G> N"
    unfolding F.saturated_def F.Inf_from_def
    by (auto dest: Set.subsetD)

  show ?thesis
    unfolding F.saturated_def
  proof (rule Set.subsetI)
    fix \<iota>' :: "'a equation Clausal_Logic.clause inference"
    assume "\<iota>' \<in> F.Inf_from N'"
    hence \<iota>'_in: "\<iota>' \<in> F_Inf" and prems_\<iota>'_subset: "set (prems_of \<iota>') \<subseteq> N'"
      unfolding F.Inf_from_def Set.mem_Collect_eq by simp_all

    let ?map_prems = "\<lambda>Ps. map to_SuperCalc_ecl (map2 subst_cls Ps (renamings_apart Ps))"

    from \<iota>'_in obtain C \<sigma>\<^sub>C C' where
      concl_of_\<iota>': "concl_of \<iota>' = subst_cls (from_SuperCalc_cl C') \<sigma>\<^sub>C" and
      deriv_prems_\<iota>': "derivable_list C (?map_prems (prems_of \<iota>'))
        \<sigma>\<^sub>C SuperCalc.FirstOrder C'" and
      dom_vars_\<sigma>\<^sub>C: "fst ` set \<sigma>\<^sub>C \<subseteq> \<Union> (vars_of_cl ` cl_ecl ` set (?map_prems (prems_of \<iota>')))" and
      range_vars_\<sigma>\<^sub>C: "range_vars \<sigma>\<^sub>C \<subseteq> \<Union> (vars_of_cl ` cl_ecl ` set (?map_prems (prems_of \<iota>')))" and
      "Idem \<sigma>\<^sub>C"
      unfolding F_Inf_def mem_Collect_eq by force

    let ?prems_vars = "\<Union>(vars_of_cl ` cl_ecl ` set (?map_prems (prems_of \<iota>')))"

    from prems_\<iota>'_subset obtain Ps \<rho>s where
      prems_\<iota>'_def: "prems_of \<iota>' = Map2.map2 subst_cls Ps \<rho>s" and "length Ps = length \<rho>s" and
      FOO: "list_all2 (\<lambda>C \<sigma>. C \<in> N \<and> renaming \<sigma> (vars_of_cl (to_SuperCalc_cl C))) Ps \<rho>s"
      unfolding N'_def Ball_Collect[symmetric]
      by (auto dest: ex_eq_map2_if_ball_set_eq)

    from deriv_prems_\<iota>'[unfolded derivable_list_def] have
      "\<exists>D D' \<sigma>\<^sub>D. renaming_cl C D \<and> derivable_list D (?map_prems Ps) \<sigma>\<^sub>D SuperCalc.FirstOrder D' \<and>
        fst ` set \<sigma>\<^sub>D \<subseteq> \<Union> (vars_of_cl ` cl_ecl ` set (?map_prems Ps)) \<and>
        range_vars \<sigma>\<^sub>D \<subseteq> \<Union> (vars_of_cl ` cl_ecl ` set (?map_prems Ps)) \<and>
        Idem \<sigma>\<^sub>D"
      using prems_\<iota>'_def
    proof (elim disjE exE conjE)
      fix P1
      assume
        prems_eq_P1: "?map_prems (prems_of \<iota>') = [P1]" and
        refl_P1: "SuperCalc.reflexion P1 C \<sigma>\<^sub>C SuperCalc.FirstOrder C'"

      from prems_eq_P1 have "Suc 0 = length (?map_prems (prems_of \<iota>'))"
        by simp
      also have "... = length (Map2.map2 subst_cls (prems_of \<iota>') (renamings_apart (prems_of \<iota>')))"
        by simp
      also have "... = length (zip (prems_of \<iota>') (renamings_apart (prems_of \<iota>')))"
        by simp
      also have "... = min (length (prems_of \<iota>')) (length (renamings_apart (prems_of \<iota>')))"
        by simp
      also have "... = length (prems_of \<iota>')"
        by (simp add: renamings_apart_length[of "prems_of \<iota>'"])
      finally have "length Ps = Suc 0 \<and> length \<rho>s = Suc 0"
        using \<open>length Ps = length \<rho>s\<close>
        by (simp add: prems_\<iota>'_def)
      then obtain P1' \<rho> where Ps_def: "Ps = [P1']" and \<rho>s_def: "\<rho>s = [\<rho>]"
        by (metis Suc_length_conv length_0_conv)
      then obtain \<rho>1 where renamings_P1'_\<rho>: "renamings_apart [subst_cls P1' \<rho>] = [\<rho>1]"
        using renamings_apart_length[of "prems_of \<iota>'"]
        using prems_\<iota>'_def
        by (metis (no_types, opaque_lifting) Suc_length_conv length_0_conv subst_cls_lists_def
            subst_cls_lists_single)
      
      have ren_\<rho>_\<rho>1: "renaming (\<rho> \<lozenge> \<rho>1) (vars_of_cl (to_SuperCalc_cl P1'))"
      proof (rule renaming_subst_compI)
        show "renaming \<rho> (vars_of_cl (to_SuperCalc_cl P1'))"
          using FOO by (simp add: Ps_def \<rho>s_def)
      next
        have "is_renaming \<rho>1"
          using renamings_P1'_\<rho> renamings_apart_renaming[of _ "[subst_cls P1' \<rho>]"]
          by simp
        then show "renaming \<rho>1 (subst_codomain \<rho> (vars_of_cl (to_SuperCalc_cl P1')))"
          by (rule is_renaming_imp_renaming)
      qed

      from prems_eq_P1 have P1_def: "P1 = to_SuperCalc_ecl (subst_cls (subst_cls P1' \<rho>) \<rho>1)"
        by (simp add: Ps_def \<rho>s_def prems_\<iota>'_def renamings_P1'_\<rho>)

      have renaming_P1_P1': "renaming_cl P1 (to_SuperCalc_ecl P1')"
      proof (rule renaming_cl_commutative)
        show "renaming_cl (to_SuperCalc_ecl P1') P1"
          unfolding P1_def renaming_cl_def
          apply (rule exI[of _ "\<rho> \<lozenge> \<rho>1"])
          using ren_\<rho>_\<rho>1
          by (metis cl_ecl.simps subst_cls_comp_subst subst_ecl.simps subst_set.simps
              subst_set_empty to_SuperCalc_cl_subst_cls)
      qed simp_all

      from prems_eq_P1 have trms_P1_empty: "trms_ecl P1 = {}"
        by force
      hence vars_of_trms_P1: "\<Union>(vars_of ` trms_ecl P1) \<subseteq> vars_of_cl (cl_ecl P1)"
        by simp

      have fin_P1: "finite (cl_ecl P1)"
        unfolding P1_def by simp

      have prems_vars_subset: "?prems_vars \<subseteq> vars_of_cl (cl_ecl P1)"
        unfolding prems_eq_P1 by simp

      from range_vars_\<sigma>\<^sub>C have range_vars_\<sigma>\<^sub>C': "range_vars \<sigma>\<^sub>C \<subseteq> vars_of_cl (cl_ecl P1)"
        unfolding range_vars_def
        by (rule subset_trans[OF _ prems_vars_subset])

      from dom_vars_\<sigma>\<^sub>C have dom_vars_\<sigma>\<^sub>C': "fst ` set \<sigma>\<^sub>C \<subseteq> vars_of_cl (cl_ecl P1)"
        by (rule subset_trans[OF _ prems_vars_subset])

      obtain \<rho>2 where renamings_P1': "renamings_apart [P1'] = [\<rho>2]"
        by (metis length_0_conv length_Suc_conv renamings_apart_length)
      hence "is_renaming \<rho>2"
        by (metis list.set_intros(1) renamings_apart_renaming)

      obtain \<rho>2_inv where
        \<rho>2_\<rho>2_inv_ident: "(\<forall>x\<in>vars_of_cl (to_SuperCalc_cl P1'). Var x \<lhd> \<rho>2 \<lhd> \<rho>2_inv = Var x)" and
        "(\<forall>x. x \<notin> subst_codomain \<rho>2 (vars_of_cl (to_SuperCalc_cl P1')) \<longrightarrow>
          Var x \<lhd> \<rho>2_inv = Var x)" and
        all_\<rho>2_inv_vars: "\<forall>x. is_a_variable (Var x \<lhd> \<rho>2_inv)"
        using renamings_admit_inverse[OF _ is_renaming_imp_renaming[OF \<open>is_renaming \<rho>2\<close>],
              of "vars_of_cl (to_SuperCalc_cl P1')"]
        by auto

      have ren_P1: "renaming_cl P1 (to_SuperCalc_ecl (subst_cls P1' \<rho>2))"
      proof (rule renaming_cl_commutative)
        show "renaming_cl (to_SuperCalc_ecl (subst_cls P1' \<rho>2)) P1"
          unfolding renaming_cl_def
        proof (intro exI[of _ "\<rho>2_inv \<lozenge> \<rho> \<lozenge> \<rho>1"] conjI)
          show "P1 = subst_ecl (to_SuperCalc_ecl (subst_cls P1' \<rho>2)) (\<rho>2_inv \<lozenge> \<rho> \<lozenge> \<rho>1)"
            unfolding P1_def
            apply (simp add: to_SuperCalc_cl_subst_cls composition_of_substs_cl[symmetric])
            by (metis \<rho>2_\<rho>2_inv_ident order_refl subst_cl_identI)
        next
          show "renaming (\<rho>2_inv \<lozenge> \<rho> \<lozenge> \<rho>1)
            (vars_of_cl (cl_ecl (to_SuperCalc_ecl (subst_cls P1' \<rho>2))))"
            unfolding renaming_def unfolding cl_ecl.simps
          proof (intro ballI conjI allI impI)
            show "\<And>x. x \<in> vars_of_cl (to_SuperCalc_cl (subst_cls P1' \<rho>2)) \<Longrightarrow>
              is_a_variable (Var x \<lhd> \<rho>2_inv \<lozenge> \<rho> \<lozenge> \<rho>1)"
              using ren_\<rho>_\<rho>1
              by (metis (no_types, opaque_lifting) all_\<rho>2_inv_vars \<rho>2_\<rho>2_inv_ident
                  is_a_variable_subst_comp order_refl renaming_def subst_cl_identI subst_comp
                  to_SuperCalc_cl_subst_cls)
          next
            fix x y
            assume
              "x \<in> vars_of_cl (to_SuperCalc_cl (subst_cls P1' \<rho>2))" and
              "y \<in> vars_of_cl (to_SuperCalc_cl (subst_cls P1' \<rho>2))"
            then obtain x' y' where
              x'_in: "x' \<in> vars_of_cl (to_SuperCalc_cl P1')" and "Var x = Var x' \<lhd> \<rho>2" and
              y'_in: "y' \<in> vars_of_cl (to_SuperCalc_cl P1')" and "Var y = Var y' \<lhd> \<rho>2"
              by (smt (verit, ccfv_SIG) \<open>is_renaming \<rho>2\<close> ex_subst_var_in_vars_if_in_vars_subst_cl
                  is_renaming_imp_renaming renaming_imp_ball_var to_SuperCalc_cl_subst_cls)
            then show "x \<noteq> y \<Longrightarrow> Var x \<lhd> \<rho>2_inv \<lozenge> \<rho> \<lozenge> \<rho>1 \<noteq> Var y \<lhd> \<rho>2_inv \<lozenge> \<rho> \<lozenge> \<rho>1"
              using ren_\<rho>_\<rho>1 \<rho>2_\<rho>2_inv_ident
              by (metis renaming_imp_ball_neq_imp_neq_subst subst_comp trm.inject(1))
          qed
        qed
      qed simp_all

      show ?thesis
        unfolding Ps_def renamings_P1'
        apply simp
        using reflexion_if_renaming[OF refl_P1 ren_P1 fin_P1 vars_of_trms_P1 trms_P1_empty
            range_vars_\<sigma>\<^sub>C' dom_vars_\<sigma>\<^sub>C' \<open>Idem \<sigma>\<^sub>C\<close>]
        using derivable_list_def
        by auto
    next
      show ?thesis sorry
    next
      show ?thesis sorry
    qed
    then obtain D D' \<sigma>\<^sub>D where
      deriv_Ps: "derivable_list D (map to_SuperCalc_ecl (map2 subst_cls Ps (renamings_apart Ps)))
        \<sigma>\<^sub>D SuperCalc.FirstOrder D'" and
      "renaming_cl C D" and
      dom_vars_\<sigma>\<^sub>D: "fst ` set \<sigma>\<^sub>D \<subseteq> \<Union> (vars_of_cl ` cl_ecl ` set (?map_prems Ps))" and
      range_vars_\<sigma>\<^sub>D: "range_vars \<sigma>\<^sub>D \<subseteq> \<Union> (vars_of_cl ` cl_ecl ` set (?map_prems Ps))" and
      "Idem \<sigma>\<^sub>D"
      by blast

    from deriv_prems_\<iota>' have "cl_ecl C = subst_cl C' \<sigma>\<^sub>C"
      using derivable_list_concl_conv by blast

    have "finite C'"
      by (smt (verit, del_insts) cl_ecl.simps deriv_prems_\<iota>' derivable_list_finite_conclusion
          finite_to_SuperCalc_cl imageE list.set_map)
    hence "finite (subst_cl C' \<sigma>\<^sub>C)"
      by (rule substs_preserve_finiteness)
    hence "finite (cl_ecl C)"
      unfolding \<open>cl_ecl C = subst_cl C' \<sigma>\<^sub>C\<close> by assumption

    have "finite D'"
      by (smt (verit) cl_ecl.simps deriv_Ps finite_to_SuperCalc_cl imageE list.set_map
          derivable_list_finite_conclusion)
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

    define \<iota> where "\<iota> = Infer Ps (subst_cls (from_SuperCalc_cl D') \<sigma>\<^sub>D)"

    have \<iota>_in: "\<iota> \<in> F_Inf"
      unfolding \<iota>_def F_Inf_def mem_Collect_eq Let_def
    proof (intro exI conjI)
      show "Infer Ps (subst_cls (from_SuperCalc_cl D') \<sigma>\<^sub>D) = Infer Ps (subst_cls (from_SuperCalc_cl D') \<sigma>\<^sub>D)"
        by (rule refl)
    next
      show "derivable_list D (?map_prems Ps) \<sigma>\<^sub>D SuperCalc.FirstOrder D'"
        by (rule deriv_Ps)
    next
      show "fst ` set \<sigma>\<^sub>D \<subseteq> \<Union> (vars_of_cl ` cl_ecl ` set ((?map_prems Ps)))"
        by (rule dom_vars_\<sigma>\<^sub>D)
    next
      show "range_vars \<sigma>\<^sub>D \<subseteq> \<Union> (vars_of_cl ` cl_ecl ` set ((?map_prems Ps)))"
        by (rule range_vars_\<sigma>\<^sub>D)
    next
      show "Idem \<sigma>\<^sub>D"
        by (rule \<open>Idem \<sigma>\<^sub>D\<close>)
    qed

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
      then obtain \<gamma>\<^sub>\<iota>s \<gamma>\<^sub>\<iota> where "\<iota>g \<in> G_Inf q" and
        prems_of_\<iota>g: "prems_of \<iota>g = map (mset_set \<circ> set_mset) (subst_cls_lists (prems_of \<iota>') \<gamma>\<^sub>\<iota>s)" and
        concl_of_\<iota>g: "concl_of \<iota>g = mset_set (set_mset (subst_cls (concl_of \<iota>') \<gamma>\<^sub>\<iota>))"
        by (auto simp add: \<G>_I_def)

      have "\<iota>g \<in> \<G>_I q \<iota>"
        unfolding \<G>_I_def
        unfolding mem_Collect_eq \<iota>_def inference.sel
      proof (intro conjI)
        show "\<iota>g \<in> G_Inf q"
          by (rule \<open>\<iota>g \<in> G_Inf q\<close>)
      next
        show "\<exists>\<gamma>s. prems_of \<iota>g = map (mset_set \<circ> set_mset) (subst_cls_lists Ps \<gamma>s)"
          by (metis prems_of_\<iota>g prems_\<iota>'_def subst_cls_lists_comp_substs subst_cls_lists_def)
      next
        have "\<exists>\<gamma>. set_mset (subst_cls (concl_of \<iota>') \<gamma>\<^sub>\<iota>) =
          set_mset (subst_cls (subst_cls (from_SuperCalc_cl D') \<sigma>\<^sub>D) \<gamma>)"
          unfolding concl_of_\<iota>' to_SuperCalc_cl_eq_conv[symmetric]
          unfolding to_SuperCalc_cl_subst_cls composition_of_substs_cl
          unfolding to_from_SuperCalc_cl[OF \<open>finite C'\<close>]
          unfolding to_from_SuperCalc_cl[OF \<open>finite D'\<close>]
          using \<open>subst_cl C' \<sigma>\<^sub>C = subst_cl (subst_cl D' \<sigma>\<^sub>D) \<rho>'\<close>
          by (metis composition_of_substs_cl)
        thus "\<exists>\<gamma>. concl_of \<iota>g =
          mset_set (set_mset (subst_cls (subst_cls (from_SuperCalc_cl D') \<sigma>\<^sub>D) \<gamma>))"
          by (simp add: concl_of_\<iota>g)
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

sublocale statically_complete_calculus "{{#}}" F_Inf "(\<TTurnstile>e)" F.Red_I_\<G> F.Red_F_\<G>
proof unfold_locales
  show "\<And>N. F.Red_I_\<G> N \<subseteq> F_Inf"
    by (rule F.Red_I_to_Inf)
next
  fix B N
  assume "B \<in> {{#}}" and "N \<TTurnstile>e {B}"
  then show "N - F.Red_F_\<G> N \<TTurnstile>e {B}"
    using F.Red_F_Bot[simplified, OF refl, unfolded F.entails_\<G>_def, simplified, of N]
    sorry
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
  fix B and N :: "'a equation Clausal_Logic.clause set"
  assume "B \<in> {{#}}" and "F.saturated N" and "N \<TTurnstile>e {B}"
  hence B_def: "B = {#}" by simp

  \<comment> \<open>We close @{term N} under \<alpha>-renaming.\<close>
  \<comment> \<open>We cannot use @{const is_renaming} because we would need
  @{term "\<And>\<sigma> S. is_renaming \<sigma> \<longleftrightarrow> renaming \<sigma> S"} but only the forward direction holds.\<close>
  define N' :: "'a equation Clausal_Logic.clause set" where
    "N' \<equiv> {subst_cls C \<sigma> | C \<sigma>. C \<in> N \<and> renaming \<sigma> (vars_of_cl (to_SuperCalc_cl C))}"

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

  have saturated_N': "F.saturated N'"
    by (rule saturated_renamings[OF \<open>F.saturated N\<close>, folded N'_def])

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
          F.Red_I_\<G>_q_def, simplified, unfolded subset_iff mem_Collect_eq, rule_format]
      using F.Red_I_\<G>_def
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
