theory WB_More_Sepref_LLVM
  imports
    Isabelle_LLVM.IICF
    WB_More_Refinement
begin


lemma refine_ASSERT_move_to_pre:
  assumes \<open>(uncurry g, uncurry h) \<in> [uncurry P]\<^sub>a A *\<^sub>a B \<rightarrow> x_assn\<close>
  shows
  \<open>(uncurry g, uncurry (\<lambda>N C. do {ASSERT (P N C); h N C}))
    \<in> A *\<^sub>a B \<rightarrow>\<^sub>a x_assn\<close>
  apply sepref_to_hoare
  apply vcg
  apply (subst POSTCOND_def hn_ctxt_def sep_conj_empty' pure_true_conv EXTRACT_def)+
  apply (auto simp: nofail_ASSERT_bind)
  apply (rule assms[to_hnr, simplified, unfolded hn_ctxt_def hn_refine_def htriple_def
    sep_conj_empty' pure_true_conv sep.add_assoc, rule_format])
  apply auto
  done

lemma refine_ASSERT_move_to_pre0:
  assumes \<open>(g, h) \<in> [P]\<^sub>a A  \<rightarrow> x_assn\<close>
  shows
  \<open>(g, (\<lambda>N. do {ASSERT (P N); h N}))
    \<in> A \<rightarrow>\<^sub>a x_assn\<close>
  apply sepref_to_hoare
  apply vcg
  apply (subst POSTCOND_def hn_ctxt_def sep_conj_empty' pure_true_conv EXTRACT_def)+
  apply (auto simp: nofail_ASSERT_bind)
  apply (rule assms[to_hnr, simplified, unfolded hn_ctxt_def hn_refine_def htriple_def
    sep_conj_empty' pure_true_conv sep.add_assoc, rule_format])
  apply auto
  done

lemma refine_ASSERT_move_to_pre2:
  assumes \<open>(uncurry2 g, uncurry2 h) \<in> [uncurry2 P]\<^sub>a A *\<^sub>a B *\<^sub>a C \<rightarrow> x_assn\<close>
  shows
  \<open>(uncurry2 g, uncurry2 (\<lambda>N C D. do {ASSERT (P N C D); h N C D}))
    \<in> A *\<^sub>a B *\<^sub>a C \<rightarrow>\<^sub>a x_assn\<close>
  apply sepref_to_hoare
  apply vcg
  apply (subst POSTCOND_def hn_ctxt_def sep_conj_empty' pure_true_conv EXTRACT_def)+
  apply (auto simp: nofail_ASSERT_bind)
  apply (rule assms[to_hnr, simplified, unfolded hn_ctxt_def hn_refine_def htriple_def
    sep_conj_empty' pure_true_conv sep.add_assoc, rule_format])
  apply auto
  done
end
