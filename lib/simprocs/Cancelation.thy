theory Cancelation
imports Main "~~/src/HOL/Library/Multiset_Order"
begin

named_theorems cancelation_simproc_before \<open>These theorems are here to normalise the term. Special
  handling of constructors should be here. Remark that only the simproc @{term NO_MATCH} is also
  included.\<close>

named_theorems cancelation_simproc_after \<open>These theorems are here to normalise the term, after the
  cancelation simproc. Normalisation of \<^term>\<open>iterate_add\<close> back to the normale representation
  should be put here.\<close>


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
  \<open>iterate_add (m+n) a = iterate_add m a + iterate_add n a\<close>
  by (induction n) (auto simp: ac_simps)

lemma iterate_add_eq_add_iff1:\<open>i \<le> j \<Longrightarrow> (iterate_add j u + m = iterate_add i u + n) = (iterate_add (j - i) u + m = n)\<close>
  by (auto dest!: le_Suc_ex add_right_imp_eq simp: ab_semigroup_add_class.add_ac(1))

lemma iterate_add_eq_add_iff2: \<open>i \<le> j \<Longrightarrow> (iterate_add i u + m = iterate_add j u + n) = (m = iterate_add (j - i) u + n)\<close>
  by (auto dest!: le_Suc_ex add_right_imp_eq simp: ab_semigroup_add_class.add_ac(1))

lemma iterate_add_less_iff1:
  "j \<le> (i::nat) \<Longrightarrow> (iterate_add i (u:: 'a :: {cancel_comm_monoid_add, ordered_ab_semigroup_add_imp_le}) + m < iterate_add j u + n) = (iterate_add (i-j) u + m < n)"
  by (auto dest!: le_Suc_ex add_right_imp_eq simp: ab_semigroup_add_class.add_ac(1))

lemma iterate_add_less_iff2:
  "i \<le> (j::nat) \<Longrightarrow> (iterate_add i (u:: 'a :: {cancel_comm_monoid_add, ordered_ab_semigroup_add_imp_le}) + m < iterate_add j u + n) = (m <iterate_add (j - i) u + n)"
  by (auto dest!: le_Suc_ex add_right_imp_eq simp: ab_semigroup_add_class.add_ac(1))

lemma iterate_add_less_eq_iff1:
  "j \<le> (i::nat) \<Longrightarrow> (iterate_add i (u:: 'a :: {cancel_comm_monoid_add, ordered_ab_semigroup_add_imp_le}) + m \<le> iterate_add j u + n) = (iterate_add (i-j) u + m \<le> n)"
  by (auto dest!: le_Suc_ex add_right_imp_eq simp: ab_semigroup_add_class.add_ac(1))

lemma iterate_add_less_eq_iff2:
  "i \<le> (j::nat) \<Longrightarrow> (iterate_add i (u:: 'a :: {cancel_comm_monoid_add, ordered_ab_semigroup_add_imp_le}) + m \<le> iterate_add j u + n) = (m \<le> iterate_add (j - i) u + n)"
  by (auto dest!: le_Suc_ex add_right_imp_eq simp: ab_semigroup_add_class.add_ac(1))

lemma iterate_add_add_eq1:
  "j \<le> (i::nat) \<Longrightarrow> ((iterate_add i u + m) - (iterate_add j u + n)) = ((iterate_add (i-j) u + m) - n)"
  by (auto dest!: le_Suc_ex add_right_imp_eq simp: ab_semigroup_add_class.add_ac(1))

lemma iterate_add_diff_add_eq2:
  "i \<le> (j::nat) \<Longrightarrow> ((iterate_add i u + m) - (iterate_add j u + n)) = (m - (iterate_add (j-i) u + n))"
  by (auto dest!: le_Suc_ex add_right_imp_eq simp: ab_semigroup_add_class.add_ac(1))


subsection \<open>Multiset set-up\<close>

lemma repeat_mset_iterate_add: \<open>repeat_mset n M = iterate_add n M\<close>
  unfolding iterate_add_def by (induction n) auto

lemma add_mset_replicate_mset_safe[cancelation_simproc_before]: \<open>NO_MATCH {#} M \<Longrightarrow> add_mset a M = {#a#} + M\<close>
  by simp

declare repeat_mset_iterate_add[cancelation_simproc_before]

declare iterate_add_distrib[cancelation_simproc_before]
declare repeat_mset_iterate_add[symmetric, cancelation_simproc_after]


subsection \<open>Nat set-up\<close>

lemma iterate_add_mult: \<open>iterate_add n (m::nat) = n * m\<close>
  by (induction n) auto

declare Suc_eq_plus1[cancelation_simproc_before]
declare iterate_add_mult[cancelation_simproc_before]
declare iterate_add_mult[symmetric, cancelation_simproc_after]


subsection \<open>Simproc Set-Up\<close>

ML_file "cancel_numerals_generalised.ML"
ML_file "cancelation_simprocs_util.ML"
ML_file "cancelation_simprocs.ML"

simproc_setup comm_monoid_cancel_numerals
  ("(l::'a::cancel_comm_monoid_add) + m = n" | "l = m + n") =
  \<open>fn phi => Comm_Monoid_add_Simprocs.eq_cancel\<close>

text \<open>Can we reduce the sorts?\<close>
simproc_setup comm_monoid_cancel_less_numerals
  ("(l::'a::{cancel_comm_monoid_add, ordered_ab_semigroup_add_imp_le}) + m < n" | "l < m + n") =
  \<open>fn phi => Comm_Monoid_add_Simprocs.less_cancel\<close>

simproc_setup comm_monoid_cancel_less_eq_numerals
  ("(l::'a::{cancel_comm_monoid_add, ordered_ab_semigroup_add_imp_le}) + m \<le> n" | "l \<le> m + n") =
  \<open>fn phi => Comm_Monoid_add_Simprocs.less_eq_cancel\<close>

simproc_setup comm_monoid_cancel_cancel_numerals
  ("((l::'a :: cancel_comm_monoid_add) + m) - n" | "l - (m + n)" ) =
  \<open>fn phi => Comm_Monoid_add_Simprocs.diff_cancel\<close>


end