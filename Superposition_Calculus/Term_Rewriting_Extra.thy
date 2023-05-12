theory Term_Rewriting_Extra
  imports "TRS.Term_Rewriting"
begin

lemma rstep_insert: "rstep (insert r R) = rstep {r} \<union> rstep R"
  using rstep_union[of "{r}" R, simplified] .

lemma rhs_lt_lhs_if_rule_in_rstep:
  fixes less_trm :: "('f, 'a) term \<Rightarrow> ('f, 'a) term \<Rightarrow> bool" (infix "\<prec>\<^sub>t" 50)
  assumes
    rule_in: "(t1, t2) \<in> rstep R" and
    ball_R_rhs_lt_lhs: "\<And>t1 t2. (t1, t2) \<in> R \<Longrightarrow> t2 \<prec>\<^sub>t t1" and
    closed_unter_subst_strong: "\<And>t1 t2 \<sigma>. (t1, t2) \<in> R \<Longrightarrow> t2 \<prec>\<^sub>t t1 \<Longrightarrow> t2 \<cdot> \<sigma> \<prec>\<^sub>t t1 \<cdot> \<sigma>" and
    compatible_with_ctxt: "\<And>t1 t2 ctxt. t2 \<prec>\<^sub>t t1 \<Longrightarrow> ctxt\<langle>t2\<rangle> \<prec>\<^sub>t ctxt\<langle>t1\<rangle>"
  shows "t2 \<prec>\<^sub>t t1"
proof -
  from rule_in obtain t1' t2' ctxt \<sigma> where
    "(t1', t2') \<in> R" and
    "t1 = ctxt\<langle>t1' \<cdot> \<sigma>\<rangle>" and
    "t2 = ctxt\<langle>t2' \<cdot> \<sigma>\<rangle>"
    by auto

  from ball_R_rhs_lt_lhs have "t2' \<prec>\<^sub>t t1'"
    using \<open>(t1', t2') \<in> R\<close> by simp

  with closed_unter_subst_strong have "t2' \<cdot> \<sigma> \<prec>\<^sub>t t1' \<cdot> \<sigma>"
    using \<open>(t1', t2') \<in> R\<close> by blast

  with compatible_with_ctxt have "ctxt\<langle>t2' \<cdot> \<sigma>\<rangle> \<prec>\<^sub>t ctxt\<langle>t1' \<cdot> \<sigma>\<rangle>"
    by metis

  thus ?thesis
    using \<open>t1 = ctxt\<langle>t1' \<cdot> \<sigma>\<rangle>\<close> \<open>t2 = ctxt\<langle>t2' \<cdot> \<sigma>\<rangle>\<close> by metis
qed

end