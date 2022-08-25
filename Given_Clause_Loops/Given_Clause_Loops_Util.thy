(* Title:        Utilities for Given Clause Loops
   Authors:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2022
   Maintainer:   Jasmin Blanchette <j.c.blanchette at vu.nl>, 2022
*)

section \<open>Utilities for Given Clause Loops\<close>

theory Given_Clause_Loops_Util
  imports
    "HOL-Library.Multiset"
    Ordered_Resolution_Prover.Lazy_List_Chain
    Weighted_Path_Order.Multiset_Extension_Pair
begin


hide_const (open) Seq.chain

hide_fact (open) Abstract_Rewriting.chain_mono

instance bool :: wellorder
proof
  fix P and b :: bool
  assume "(\<And>y. y < b \<Longrightarrow> P y) \<Longrightarrow> P b" for b :: bool
  hence "\<And>q. q \<le> b \<Longrightarrow> P q"
    using less_bool_def by presburger
  then show "P b"
    by auto
qed

lemma finite_imp_set_eq:
  assumes fin: "finite A"
  shows "\<exists>xs. set xs = A"
  using fin
proof (induct A rule: finite_induct)
  case empty
  then show ?case
    by auto
next
  case (insert x B)
  then obtain xs :: "'a list" where
    "set xs = B"
    by blast
  then have "set (x # xs) = insert x B"
    by auto
  then show ?case
    by blast
qed

lemma singletons_in_mult1: "(x, y) \<in> R \<Longrightarrow> ({#x#}, {#y#}) \<in> mult1 R"
  by (metis add_mset_add_single insert_DiffM mult1I single_eq_add_mset)

lemma singletons_in_mult: "(x, y) \<in> R \<Longrightarrow> ({#x#}, {#y#}) \<in> mult R"
  by (simp add: mult_def singletons_in_mult1 trancl.intros(1))

lemma Liminf_llist_subset:
  assumes
    "llength Xs = llength Ys" and
    "\<forall>i < llength Xs. lnth Xs i \<subseteq> lnth Ys i"
  shows "Liminf_llist Xs \<subseteq> Liminf_llist Ys"
  unfolding Liminf_llist_def using assms
  by (smt INT_iff SUP_mono mem_Collect_eq subsetD subsetI)

lemma countable_imp_lset:
  assumes count: "countable A"
  shows "\<exists>as. lset as = A"
proof (cases "finite A")
  case fin: True
  have "\<exists>as. set as = A"
    by (simp add: fin finite_imp_set_eq)
  thus ?thesis
    by (meson lset_llist_of)
next
  case inf: False

  let ?as = "inf_llist (from_nat_into A)"

  have "lset ?as = A"
    by (simp add: inf infinite_imp_nonempty count)
  thus ?thesis
    by blast
qed

end
