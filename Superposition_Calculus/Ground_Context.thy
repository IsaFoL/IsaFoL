theory Ground_Context
  imports "Regular_Tree_Relations.Ground_Terms"
begin

type_synonym 'f ground_context = "('f, 'f gterm) actxt"

abbreviation ctxt_apply_gterm (\<open>_\<langle>_\<rangle>\<^sub>G\<close> [1000, 0] 1000) where
  "C\<langle>s\<rangle>\<^sub>G \<equiv> GFun\<langle>C;s\<rangle>"

(* TODO: Names (Search everywhere for ctxt *)
lemma le_size_gctxt: "size t \<le> size (c\<langle>t\<rangle>\<^sub>G)"
  by (induction c) simp_all

lemma lt_size_gctxt: "ctxt \<noteq> \<box> \<Longrightarrow> size t < size ctxt\<langle>t\<rangle>\<^sub>G"
  by (induction ctxt) force+

lemma gctxt_ident_iff_eq_GHole[simp]: "ctxt\<langle>t\<rangle>\<^sub>G = t \<longleftrightarrow> ctxt = \<box>"
proof (rule iffI)
  assume "ctxt\<langle>t\<rangle>\<^sub>G = t"
  hence "size (ctxt\<langle>t\<rangle>\<^sub>G) = size t"
    by argo
  thus "ctxt = \<box>"
    using lt_size_gctxt[of ctxt t]
    by linarith
next
  show "ctxt = \<box> \<Longrightarrow> ctxt\<langle>t\<rangle>\<^sub>G = t"
    by simp
qed

end