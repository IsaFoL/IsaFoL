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

lemma compatible_with_ctxt_rewrite_inside_ctxt: "compatible_with_ctxt (rewrite_inside_ctxt E)"
  unfolding compatible_with_ctxt_def rewrite_inside_ctxt_def
  unfolding mem_Collect_eq
  by (metis Pair_inject ctxt_ctxt)
    

end