theory Term_Rewrite_System
  imports
    Regular_Tree_Relations.Ground_Ctxt
begin

definition compatible_with_gctxt :: "'f gterm rel \<Rightarrow> bool" where
  "compatible_with_gctxt I \<longleftrightarrow> (\<forall>t t' ctxt. (t, t') \<in> I \<longrightarrow> (ctxt\<langle>t\<rangle>\<^sub>G, ctxt\<langle>t'\<rangle>\<^sub>G) \<in> I)"

lemma compatible_with_gctxtD:
  "compatible_with_gctxt I \<Longrightarrow> (t, t') \<in> I \<Longrightarrow> (ctxt\<langle>t\<rangle>\<^sub>G, ctxt\<langle>t'\<rangle>\<^sub>G) \<in> I"
  by (simp add: compatible_with_gctxt_def)

lemma compatible_with_gctxt_converse:
  assumes "compatible_with_gctxt I"
  shows "compatible_with_gctxt (I\<inverse>)"
  unfolding compatible_with_gctxt_def
proof (intro allI impI)
  fix t t' ctxt
  assume "(t, t') \<in> I\<inverse>"
  thus "(ctxt\<langle>t\<rangle>\<^sub>G, ctxt\<langle>t'\<rangle>\<^sub>G) \<in> I\<inverse>"
    by (simp add: assms compatible_with_gctxtD)
qed

lemma compatible_with_gctxt_symcl:
  assumes "compatible_with_gctxt I"
  shows "compatible_with_gctxt (I\<^sup>\<leftrightarrow>)"
  unfolding compatible_with_gctxt_def
proof (intro allI impI)
  fix t t' ctxt
  assume "(t, t') \<in> I\<^sup>\<leftrightarrow>"
  thus "(ctxt\<langle>t\<rangle>\<^sub>G, ctxt\<langle>t'\<rangle>\<^sub>G) \<in> I\<^sup>\<leftrightarrow>"
  proof (induction ctxt arbitrary: t t')
    case GHole
    thus ?case by simp
  next
    case (GMore f ts1 ctxt ts2)
    thus ?case
      using assms[unfolded compatible_with_gctxt_def, rule_format]
      by blast
  qed
qed

lemma compatible_with_gctxt_rtrancl:
  assumes "compatible_with_gctxt I"
  shows "compatible_with_gctxt (I\<^sup>*)"
  unfolding compatible_with_gctxt_def
proof (intro allI impI)
  fix t t' ctxt
  assume "(t, t') \<in> I\<^sup>*"
  thus "(ctxt\<langle>t\<rangle>\<^sub>G, ctxt\<langle>t'\<rangle>\<^sub>G) \<in> I\<^sup>*"
  proof (induction t' rule: rtrancl_induct)
    case base
    show ?case
      by simp
  next
    case (step y z)
    thus ?case
      using assms[unfolded compatible_with_gctxt_def, rule_format]
      by (meson rtrancl.rtrancl_into_rtrancl)
  qed
qed

lemma compatible_with_gctxt_relcomp:
  assumes "compatible_with_gctxt I1" and "compatible_with_gctxt I2"
  shows "compatible_with_gctxt (I1 O I2)"
  unfolding compatible_with_gctxt_def
proof (intro allI impI)
  fix t t'' ctxt
  assume "(t, t'') \<in> I1 O I2"
  then obtain t' where "(t, t') \<in> I1" and "(t', t'') \<in> I2"
    by auto

  have "(ctxt\<langle>t\<rangle>\<^sub>G, ctxt\<langle>t'\<rangle>\<^sub>G) \<in> I1"
    using \<open>(t, t') \<in> I1\<close> assms(1) compatible_with_gctxtD by blast
  moreover have "(ctxt\<langle>t'\<rangle>\<^sub>G, ctxt\<langle>t''\<rangle>\<^sub>G) \<in> I2"
    using \<open>(t', t'') \<in> I2\<close> assms(2) compatible_with_gctxtD by blast
  ultimately show "(ctxt\<langle>t\<rangle>\<^sub>G, ctxt\<langle>t''\<rangle>\<^sub>G) \<in> I1 O I2"
    by auto
qed

lemma compatible_with_gctxt_join:
  assumes "compatible_with_gctxt I"
  shows "compatible_with_gctxt (I\<^sup>\<down>)"
  using assms
  by (simp_all add: join_def compatible_with_gctxt_relcomp compatible_with_gctxt_rtrancl
      compatible_with_gctxt_converse)

lemma compatible_with_gctxt_conversion:
  assumes "compatible_with_gctxt I"
  shows "compatible_with_gctxt (I\<^sup>\<leftrightarrow>\<^sup>*)"
  by (simp add: assms compatible_with_gctxt_rtrancl compatible_with_gctxt_symcl conversion_def)

definition rewrite_inside_gctxt :: "'f gterm rel \<Rightarrow> 'f gterm rel" where
  "rewrite_inside_gctxt R = {(ctxt\<langle>t1\<rangle>\<^sub>G, ctxt\<langle>t2\<rangle>\<^sub>G) | ctxt t1 t2. (t1, t2) \<in> R}"

lemma mem_rewrite_inside_gctxt_if_mem_rewrite_rules[intro]:
  "(l, r) \<in> R \<Longrightarrow> (l, r) \<in> rewrite_inside_gctxt R"
  by (metis (mono_tags, lifting) CollectI gctxt_apply_term.simps(1) rewrite_inside_gctxt_def)

lemma ctxt_mem_rewrite_inside_gctxt_if_mem_rewrite_rules[intro]:
  "(l, r) \<in> R \<Longrightarrow> (ctxt\<langle>l\<rangle>\<^sub>G, ctxt\<langle>r\<rangle>\<^sub>G) \<in> rewrite_inside_gctxt R"
  by (auto simp: rewrite_inside_gctxt_def)

lemma rewrite_inside_gctxt_mono: "R \<subseteq> S \<Longrightarrow> rewrite_inside_gctxt R \<subseteq> rewrite_inside_gctxt S"
  by (auto simp add: rewrite_inside_gctxt_def)

lemma rewrite_inside_gctxt_union:
  "rewrite_inside_gctxt (R \<union> S) = rewrite_inside_gctxt R \<union> rewrite_inside_gctxt S"
  by (auto simp add: rewrite_inside_gctxt_def)

lemma rewrite_inside_gctxt_insert:
  "rewrite_inside_gctxt (insert r R) = rewrite_inside_gctxt {r} \<union> rewrite_inside_gctxt R"
  using rewrite_inside_gctxt_union[of "{r}" R, simplified] .

lemma converse_rewrite_steps: "(rewrite_inside_gctxt R)\<inverse> = rewrite_inside_gctxt (R\<inverse>)"
  by (auto simp: rewrite_inside_gctxt_def)

lemma rhs_lt_lhs_if_rule_in_rewrite_inside_gctxt:
  fixes less_trm :: "'f gterm \<Rightarrow> 'f gterm \<Rightarrow> bool" (infix "\<prec>\<^sub>t" 50)
  assumes
    rule_in: "(t1, t2) \<in> rewrite_inside_gctxt R" and
    ball_R_rhs_lt_lhs: "\<And>t1 t2. (t1, t2) \<in> R \<Longrightarrow> t2 \<prec>\<^sub>t t1" and
    compatible_with_gctxt: "\<And>t1 t2 ctxt. t2 \<prec>\<^sub>t t1 \<Longrightarrow> ctxt\<langle>t2\<rangle>\<^sub>G \<prec>\<^sub>t ctxt\<langle>t1\<rangle>\<^sub>G"
  shows "t2 \<prec>\<^sub>t t1"
proof -
  from rule_in obtain t1' t2' ctxt where
    "(t1', t2') \<in> R" and
    "t1 = ctxt\<langle>t1'\<rangle>\<^sub>G" and
    "t2 = ctxt\<langle>t2'\<rangle>\<^sub>G"
    by (auto simp: rewrite_inside_gctxt_def)

  from ball_R_rhs_lt_lhs have "t2' \<prec>\<^sub>t t1'"
    using \<open>(t1', t2') \<in> R\<close> by simp

  with compatible_with_gctxt have "ctxt\<langle>t2'\<rangle>\<^sub>G \<prec>\<^sub>t ctxt\<langle>t1'\<rangle>\<^sub>G"
    by metis

  thus ?thesis
    using \<open>t1 = ctxt\<langle>t1'\<rangle>\<^sub>G\<close> \<open>t2 = ctxt\<langle>t2'\<rangle>\<^sub>G\<close> by metis
qed

lemma mem_rewrite_step_union_NF:
  assumes "(t, t') \<in> rewrite_inside_gctxt (R1 \<union> R2)"
    "t \<in> NF (rewrite_inside_gctxt R2)"
  shows "(t, t') \<in> rewrite_inside_gctxt R1"
  using assms
  unfolding rewrite_inside_gctxt_union
  by blast

lemma predicate_holds_of_mem_rewrite_inside_gctxt:
  assumes rule_in: "(t1, t2) \<in> rewrite_inside_gctxt R" and
    ball_P: "\<And>t1 t2. (t1, t2) \<in> R \<Longrightarrow> P t1 t2" and
    preservation: "\<And>t1 t2 ctxt \<sigma>. (t1, t2) \<in> R \<Longrightarrow> P t1 t2 \<Longrightarrow> P ctxt\<langle>t1\<rangle>\<^sub>G ctxt\<langle>t2\<rangle>\<^sub>G"
  shows "P t1 t2"
proof -
  from rule_in obtain t1' t2' ctxt \<sigma> where
    "(t1', t2') \<in> R" and
    "t1 = ctxt\<langle>t1'\<rangle>\<^sub>G" and
    "t2 = ctxt\<langle>t2'\<rangle>\<^sub>G"
    by (auto simp: rewrite_inside_gctxt_def)
  thus ?thesis
    using ball_P[OF \<open>(t1', t2') \<in> R\<close>]
    using preservation[OF \<open>(t1', t2') \<in> R\<close>, of ctxt]
    by simp
qed

lemma compatible_with_gctxt_rewrite_inside_gctxt[simp]: "compatible_with_gctxt (rewrite_inside_gctxt E)"
  unfolding compatible_with_gctxt_def rewrite_inside_gctxt_def
  unfolding mem_Collect_eq
  by (metis Pair_inject ctxt_ctxt)

lemma subset_rewrite_inside_gctxt[simp]: "E \<subseteq> rewrite_inside_gctxt E"
proof (rule Set.subsetI)
  fix e assume e_in: "e \<in> E"
  moreover obtain s t where e_def: "e = (s, t)"
    by fastforce
  show "e \<in> rewrite_inside_gctxt E"
    unfolding rewrite_inside_gctxt_def
    unfolding mem_Collect_eq
  proof (intro exI conjI)
    show "e = (\<box>\<^sub>G\<langle>s\<rangle>\<^sub>G, \<box>\<^sub>G\<langle>t\<rangle>\<^sub>G)"
      unfolding e_def gctxt_apply_term.simps ..
  next
    show "(s, t) \<in> E"
      using e_in
      unfolding e_def .
  qed
qed

lemma wf_converse_rewrite_inside_gctxt:
  fixes E :: "'f gterm rel"
  assumes
    wfP_R: "wfP R" and
    R_compatible_with_gctxt: "\<And>ctxt t t'. R t t' \<Longrightarrow> R ctxt\<langle>t\<rangle>\<^sub>G ctxt\<langle>t'\<rangle>\<^sub>G" and
    equations_subset_R: "\<And>x y. (x, y) \<in> E \<Longrightarrow> R y x"
  shows "wf ((rewrite_inside_gctxt E)\<inverse>)"
proof (rule wf_subset)
  from wfP_R show "wf {(x, y). R x y}"
    by (simp add: wfP_def)
next
  show "(rewrite_inside_gctxt E)\<inverse> \<subseteq> {(x, y). R x y}"
  proof (rule Set.subsetI)
    fix e assume "e \<in> (rewrite_inside_gctxt E)\<inverse>"
    then obtain ctxt s t where e_def: "e = (ctxt\<langle>s\<rangle>\<^sub>G, ctxt\<langle>t\<rangle>\<^sub>G)" and "(t, s) \<in> E"
      by (smt (verit) Pair_inject converseE mem_Collect_eq rewrite_inside_gctxt_def)
    hence "R s t"
      using equations_subset_R by simp
    hence "R ctxt\<langle>s\<rangle>\<^sub>G ctxt\<langle>t\<rangle>\<^sub>G"
      using R_compatible_with_gctxt by simp
    then show "e \<in> {(x, y). R x y}"
      by (simp add: e_def)
  qed
qed

end
