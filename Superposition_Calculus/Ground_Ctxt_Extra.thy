theory Ground_Ctxt_Extra
  imports "Regular_Tree_Relations.Ground_Ctxt"
begin

lemma le_size_gctxt: "size t \<le> size (C\<langle>t\<rangle>\<^sub>G)"
  by (induction C) simp_all

lemma lt_size_gctxt: "ctxt \<noteq> \<box>\<^sub>G \<Longrightarrow> size t < size ctxt\<langle>t\<rangle>\<^sub>G"
  by (induction ctxt) force+

lemma gctxt_ident_iff_eq_GHole[simp]: "ctxt\<langle>t\<rangle>\<^sub>G = t \<longleftrightarrow> ctxt = \<box>\<^sub>G"
proof (rule iffI)
  assume "ctxt\<langle>t\<rangle>\<^sub>G = t"
  hence "size (ctxt\<langle>t\<rangle>\<^sub>G) = size t"
    by argo
  thus "ctxt = \<box>\<^sub>G"
    using lt_size_gctxt[of ctxt t]
    by linarith
next
  show "ctxt = \<box>\<^sub>G \<Longrightarrow> ctxt\<langle>t\<rangle>\<^sub>G = t"
    by simp
qed

end