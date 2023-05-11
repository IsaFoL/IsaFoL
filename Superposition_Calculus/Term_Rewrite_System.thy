theory Term_Rewrite_System
  imports
    (* Theories from the AFP *)
    "Knuth_Bendix_Order.Subterm_and_Context"
begin

text \<open>This is for ground terms only!\<close>

definition compatible_with_ctxt :: "(('f, 'v) term \<times> ('f, 'v) term) set \<Rightarrow> bool" where
  "compatible_with_ctxt I \<longleftrightarrow> (\<forall>t t' ctxt. (t, t') \<in> I \<longrightarrow> (ctxt\<langle>t\<rangle>, ctxt\<langle>t'\<rangle>) \<in> I)"

lemma compatible_with_ctxtD:
  "compatible_with_ctxt I \<Longrightarrow> (t, t') \<in> I \<Longrightarrow> (ctxt\<langle>t\<rangle>, ctxt\<langle>t'\<rangle>) \<in> I"
  by (simp add: compatible_with_ctxt_def)

lemma compatible_with_ctxt_converse:
  assumes "compatible_with_ctxt I"
  shows "compatible_with_ctxt (I\<inverse>)"
  unfolding compatible_with_ctxt_def
proof (intro allI impI)
  fix t t' ctxt
  assume "(t, t') \<in> I\<inverse>"
  thus "(ctxt\<langle>t\<rangle>, ctxt\<langle>t'\<rangle>) \<in> I\<inverse>"
    by (simp add: assms compatible_with_ctxtD)
qed

lemma compatible_with_ctxt_symcl:
  assumes "compatible_with_ctxt I"
  shows "compatible_with_ctxt (I\<^sup>\<leftrightarrow>)"
  unfolding compatible_with_ctxt_def
proof (intro allI impI)
  fix t t' ctxt
  assume "(t, t') \<in> I\<^sup>\<leftrightarrow>"
  thus "(ctxt\<langle>t\<rangle>, ctxt\<langle>t'\<rangle>) \<in> I\<^sup>\<leftrightarrow>"
  proof (induction ctxt arbitrary: t t')
    case Hole
    thus ?case by simp
  next
    case (More f ts1 ctxt ts2)
    thus ?case
      using assms[unfolded compatible_with_ctxt_def, rule_format]
      by blast
  qed
qed

lemma compatible_with_ctxt_rtrancl:
  assumes "compatible_with_ctxt I"
  shows "compatible_with_ctxt (I\<^sup>*)"
  unfolding compatible_with_ctxt_def
proof (intro allI impI)
  fix t t' ctxt
  assume "(t, t') \<in> I\<^sup>*"
  thus "(ctxt\<langle>t\<rangle>, ctxt\<langle>t'\<rangle>) \<in> I\<^sup>*"
  proof (induction t' rule: rtrancl_induct)
    case base
    show ?case
      by simp
  next
    case (step y z)
    thus ?case
      using assms[unfolded compatible_with_ctxt_def, rule_format]
      by (meson rtrancl.rtrancl_into_rtrancl)
  qed
qed

lemma compatible_with_ctxt_relcomp:
  assumes "compatible_with_ctxt I1" and "compatible_with_ctxt I2"
  shows "compatible_with_ctxt (I1 O I2)"
  unfolding compatible_with_ctxt_def
proof (intro allI impI)
  fix t t'' ctxt
  assume "(t, t'') \<in> I1 O I2"
  then obtain t' where "(t, t') \<in> I1" and "(t', t'') \<in> I2"
    by auto

  have "(ctxt\<langle>t\<rangle>, ctxt\<langle>t'\<rangle>) \<in> I1"
    using \<open>(t, t') \<in> I1\<close> assms(1) compatible_with_ctxtD by blast
  moreover have "(ctxt\<langle>t'\<rangle>, ctxt\<langle>t''\<rangle>) \<in> I2"
    using \<open>(t', t'') \<in> I2\<close> assms(2) compatible_with_ctxtD by blast
  ultimately show "(ctxt\<langle>t\<rangle>, ctxt\<langle>t''\<rangle>) \<in> I1 O I2"
    by auto
qed

lemma compatible_with_ctxt_join:
  assumes "compatible_with_ctxt I"
  shows "compatible_with_ctxt (I\<^sup>\<down>)"
  using assms
  by (simp_all add: join_def compatible_with_ctxt_relcomp compatible_with_ctxt_rtrancl
      compatible_with_ctxt_converse)

lemma compatible_with_ctxt_conversion:
  assumes "compatible_with_ctxt I"
  shows "compatible_with_ctxt (I\<^sup>\<leftrightarrow>\<^sup>*)"
  by (simp add: assms compatible_with_ctxt_rtrancl compatible_with_ctxt_symcl conversion_def)

definition rewrite_inside_ctxt where
  "rewrite_inside_ctxt E = {(ctxt\<langle>s\<rangle>, ctxt\<langle>t\<rangle>) | ctxt s t. (s, t) \<in> E}"

lemma compatible_with_ctxt_rewrite_inside_ctxt[simp]: "compatible_with_ctxt (rewrite_inside_ctxt E)"
  unfolding compatible_with_ctxt_def rewrite_inside_ctxt_def
  unfolding mem_Collect_eq
  by (metis Pair_inject ctxt_ctxt)

lemma subset_rewrite_inside_ctxt[simp]: "E \<subseteq> rewrite_inside_ctxt E"
proof (rule Set.subsetI)
  fix e assume "e \<in> E"
  moreover obtain s t where "e = (s, t)"
    by fastforce
  ultimately show "e \<in> rewrite_inside_ctxt E"
    unfolding rewrite_inside_ctxt_def
    by (metis (mono_tags, lifting) ctxt_apply_term.simps(1) mem_Collect_eq)
qed

lemma wf_converse_rewrite_inside_ctxt:
  fixes E :: "('f, 'v) term rel"
  assumes
    wfP_R: "wfP R" and
    R_compatible_with_ctxt: "\<And>ctxt t t'. R t t' \<Longrightarrow> R ctxt\<langle>t\<rangle> ctxt\<langle>t'\<rangle>" and
    equations_subset_R: "\<And>x y. (x, y) \<in> E \<Longrightarrow> R y x"
  shows "wf ((rewrite_inside_ctxt E)\<inverse>)"
proof (rule wf_subset)
  from wfP_R show "wf {(x, y). R x y}"
    by (simp add: wfP_def)
next
  show "(rewrite_inside_ctxt E)\<inverse> \<subseteq> {(x, y). R x y}"
  proof (rule Set.subsetI)
    fix e assume "e \<in> (rewrite_inside_ctxt E)\<inverse>"
    then obtain ctxt s t where e_def: "e = (ctxt\<langle>s\<rangle>, ctxt\<langle>t\<rangle>)" and "(t, s) \<in> E"
      by (smt (verit) Pair_inject converseE mem_Collect_eq rewrite_inside_ctxt_def)
    hence "R s t"
      using equations_subset_R by simp
    hence "R ctxt\<langle>s\<rangle> ctxt\<langle>t\<rangle>"
      using R_compatible_with_ctxt by simp
    then show "e \<in> {(x, y). R x y}"
      by (simp add: e_def)
  qed
qed

(* lemma
  assumes "WCR E"
  shows "WCR (rewrite_inside_ctxt E)"
  (* using assms *)
  unfolding WCR_defs
proof (intro ballI allI impI, elim conjE)
  fix x y z
  assume "(x, y) \<in> rewrite_inside_ctxt E" and "(x, z) \<in> rewrite_inside_ctxt E"
  then obtain ctxt1 ctxt2 tx1 tx2 ty tz where
    "x = ctxt1\<langle>tx1\<rangle>" and "y = ctxt1\<langle>ty\<rangle>" and "(tx1, ty) \<in> E" and
    "x = ctxt2\<langle>tx2\<rangle>" and "z = ctxt2\<langle>tz\<rangle>" and "(tx2, tz) \<in> E"
    unfolding rewrite_inside_ctxt_def by blast
  then show "(y, z) \<in> (rewrite_inside_ctxt E)\<^sup>\<down>"
    unfolding join_def relcomp.simps
    apply simp
    find_theorems "WCR _" *)

end