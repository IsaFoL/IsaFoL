theory Cancelation
imports Main "~~/src/HOL/Library/Multiset_Order"
begin

named_theorems cancelation_simproc_before \<open>These theorems are here to normalise the term. Special
  handling of constructors should be here.\<close>

named_theorems cancelation_delsimproc_before \<open>These theorems are here to normalise the term. Special
  handling of constructors should be here.\<close>

named_theorems cancelation_simproc_after \<open>These theorems are here to normalise the term. Special
  back to a normal Isabelle representation should be here.\<close>


definition iterate_add :: \<open>nat \<Rightarrow> 'a::cancel_comm_monoid_add \<Rightarrow> 'a\<close> where
  \<open>iterate_add n a = ((op + a) ^^n) 0\<close>

lemma iterate_add_simps[simp]:
  \<open>iterate_add 0 a = 0\<close>
  \<open>iterate_add (Suc n) a = a + iterate_add n a\<close>
  unfolding iterate_add_def by auto

lemma iterate_add_empty[simp]:
  \<open>iterate_add n 0 = 0\<close>
  unfolding iterate_add_def by (induction n) auto

lemma iterate_add_distrib[simp]:
  \<open>iterate_add(m+n) a = iterate_add m a + iterate_add n a\<close>
  by (induction n) (auto simp: ac_simps)

lemma repeat_mset_iterate_add: \<open>repeat_mset n M = iterate_add n M\<close>
  unfolding iterate_add_def
  by (induction n) auto

thm numeral_One
lemma iterate_add_eq_add_iff1:\<open>i \<le> j \<Longrightarrow> (iterate_add j u + m = iterate_add i u + n) = (iterate_add (j - i) u + m = n)\<close>
  by (auto dest!: le_Suc_ex add_right_imp_eq simp: ab_semigroup_add_class.add_ac(1))

lemma iterate_add_eq_add_iff2: \<open>i \<le> j \<Longrightarrow> (iterate_add i u + m = iterate_add j u + n) = (m = iterate_add (j - i) u + n)\<close>
  by (auto dest!: le_Suc_ex add_right_imp_eq simp: ab_semigroup_add_class.add_ac(1))


lemma add_mset_replicate_mset_safe[cancelation_simproc_before]: \<open>NO_MATCH {#} M \<Longrightarrow> add_mset a M = {#a#} + M\<close>
  by simp

declare union_mset_add_mset_left[cancelation_delsimproc_before]
declare repeat_mset_iterate_add[cancelation_simproc_before]
declare Suc_eq_plus1[cancelation_simproc_before]
declare iterate_add_distrib[cancelation_simproc_before]
declare repeat_mset_iterate_add[symmetric, cancelation_simproc_after]

ML \<open>simpset_of\<close>
ML \<open>Simplifier.full_rewrite (@{context} addsimps @{thms add_mset_replicate_mset_safe}
  delsimps @{thms cancelation_delsimproc_before})
  @{cterm \<open>add_mset a(add_mset b M) = add_mset b M'\<close>}\<close>
ML \<open>Simplifier.full_rewrite\<close>
ML \<open>Thm.cprop_of\<close>
ML_file \<open>cancel_numerals_generalised.ML\<close>
ML_file \<open>cancelation_simprocs_util.ML\<close>
ML_file \<open>cancelation_simprocs.ML\<close>
declare[[simp_trace(* , show_sorts *), simp_trace_depth_limit = 5]]

ML \<open>@{simproc NO_MATCH}\<close>

ML \<open>Comm_Monoid_add_Simprocs.eq_cancel_msets @{context} @{cterm \<open>(a::'a::cancel_comm_monoid_add) = a + b\<close>}\<close>
ML \<open>Simplifier.full_rewrite ((* empty_simpset *) (clear_simpset (Simplifier.del_cong @{thm NO_MATCH_cong} @{context}))
  delsimps @{thms cancelation_delsimproc_before} 
  delsimprocs [@{simproc mseteq_cancel_numerals}, @{simproc HOL.NO_MATCH}]
  addsimps @{thms cancelation_simproc_before}
  addsimprocs [@{simproc NO_MATCH}]
 )
  @{cterm \<open>add_mset a(add_mset b M) = add_mset b M'\<close>}
\<close>
ML \<open>Comm_Monoid_add_Simprocs.eq_cancel_msets @{context} @{cterm \<open>add_mset a(add_mset b M) = add_mset b M'\<close>}\<close>
ML \<open>Comm_Monoid_add_Simprocs.eq_cancel_msets @{context} @{cterm \<open>Suc n = n\<close>}\<close>
ML \<open>Comm_Monoid_add_Simprocs.eq_cancel_msets @{context} @{cterm \<open>repeat_mset 3 M = repeat_mset 1 M\<close>}\<close>

end