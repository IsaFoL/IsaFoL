theory Abstract_Rewriting_Extra
  imports
    "Transitive_Closure_Extra"
    "Abstract-Rewriting.Abstract_Rewriting"
begin

lemma mem_join_union_iff_mem_join_lhs:
  assumes
    "\<And>z. (x, z) \<in> A\<^sup>* \<Longrightarrow> z \<notin> Domain B" and
    "\<And>z. (y, z) \<in> A\<^sup>* \<Longrightarrow> z \<notin> Domain B"
  shows "(x, y) \<in> (A \<union> B)\<^sup>\<down> \<longleftrightarrow> (x, y) \<in> A\<^sup>\<down>"
proof (rule iffI)
  assume "(x, y) \<in> (A \<union> B)\<^sup>\<down>"
  then obtain z where
    "(x, z) \<in> (A \<union> B)\<^sup>*" and "(y, z) \<in> (A \<union> B)\<^sup>*"
    by auto

  show "(x, y) \<in> A\<^sup>\<down>"
  proof (rule joinI)
    from assms(1) show "(x, z) \<in> A\<^sup>*"
      using \<open>(x, z) \<in> (A \<union> B)\<^sup>*\<close> mem_rtrancl_union_iff_mem_rtrancl_lhs[of x A B z] by simp
  next
    from assms(2) show "(y, z) \<in> A\<^sup>*"
      using \<open>(y, z) \<in> (A \<union> B)\<^sup>*\<close> mem_rtrancl_union_iff_mem_rtrancl_lhs[of y A B z] by simp
  qed
next
  show "(x, y) \<in> A\<^sup>\<down> \<Longrightarrow> (x, y) \<in> (A \<union> B)\<^sup>\<down>"
    by (metis UnCI join_mono subset_Un_eq sup.left_idem)
qed

lemma mem_join_union_iff_mem_join_rhs:
  assumes
    "\<And>z. (x, z) \<in> B\<^sup>* \<Longrightarrow> z \<notin> Domain A" and
    "\<And>z. (y, z) \<in> B\<^sup>* \<Longrightarrow> z \<notin> Domain A"
  shows "(x, y) \<in> (A \<union> B)\<^sup>\<down> \<longleftrightarrow> (x, y) \<in> B\<^sup>\<down>"
  using mem_join_union_iff_mem_join_lhs
  by (metis assms(1) assms(2) sup_commute)

lemma refl_join: "refl (r\<^sup>\<down>)"
  by (simp add: joinI_right reflI)

lemma trans_join:
  assumes strongly_norm: "SN r" and confluent: "WCR r"
  shows "trans (r\<^sup>\<down>)"
proof -
  from confluent strongly_norm have "CR r"
    using Newman by metis
  hence "r\<^sup>\<leftrightarrow>\<^sup>* = r\<^sup>\<down>"
    using CR_imp_conversionIff_join by metis
  thus ?thesis
    using conversion_trans by metis
qed

end