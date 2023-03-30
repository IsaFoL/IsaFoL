theory Term_Rewrite_System
  imports
    (* Theories from the AFP *)
    "Knuth_Bendix_Order.Subterm_and_Context"
begin

text \<open>This is for ground terms only!\<close>

definition compatible_with_ctxt :: "(('f, 'v) term \<times> ('f, 'v) term) set \<Rightarrow> bool" where
  "compatible_with_ctxt I \<longleftrightarrow> (\<forall>ctxt t t'. (t, t') \<in> I \<longrightarrow> (ctxt\<langle>t\<rangle>, ctxt\<langle>t'\<rangle>) \<in> I)"

lemma compatible_with_ctxtD:
  "compatible_with_ctxt I \<Longrightarrow> (t, t') \<in> I \<Longrightarrow> (ctxt\<langle>t\<rangle>, ctxt\<langle>t'\<rangle>) \<in> I"
  by (simp add: compatible_with_ctxt_def)

lemma compatible_with_ctxt_symcl:
  assumes "compatible_with_ctxt I"
  shows "compatible_with_ctxt (I\<^sup>\<leftrightarrow>)"
  unfolding compatible_with_ctxt_def
proof (intro allI impI)
  fix ctxt t t'
  assume "(t, t') \<in> I\<^sup>\<leftrightarrow>"
  then show "(ctxt\<langle>t\<rangle>, ctxt\<langle>t'\<rangle>) \<in> I\<^sup>\<leftrightarrow>"
  proof (induction ctxt arbitrary: t t')
    case Hole
    then show ?case by simp
  next
    case (More f ts1 ctxt ts2)
    then show ?case
      using assms[unfolded compatible_with_ctxt_def, rule_format]
      by blast
  qed
qed

lemma compatible_with_ctxt_rtrancl:
  assumes "compatible_with_ctxt I"
  shows "compatible_with_ctxt (I\<^sup>*)"
  unfolding compatible_with_ctxt_def
proof (intro allI impI)
  fix ctxt t t'
  assume "(t, t') \<in> I\<^sup>*"
  then show "(ctxt\<langle>t\<rangle>, ctxt\<langle>t'\<rangle>) \<in> I\<^sup>*"
  proof (induction t' rule: rtrancl_induct)
    case base
    then show ?case
      by simp
  next
    case (step y z)
    then show ?case
      using assms[unfolded compatible_with_ctxt_def, rule_format]
      by (meson rtrancl.rtrancl_into_rtrancl)
  qed
qed
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