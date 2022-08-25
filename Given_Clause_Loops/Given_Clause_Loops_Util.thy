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

lemma full_chain_lmap_left_total:
  assumes
    r_r': "\<forall>x y. R x y \<longrightarrow> R' (f x) (f y)" and
    r'_r: "\<forall>x y. R' x y \<longrightarrow> (\<forall>a. f a = x \<longrightarrow> (\<exists>b. f b = y \<and> R a b))" and
    full: "full_chain R xs"
  shows "full_chain R' (lmap f xs)"
proof -
  have chain: "chain R xs"
    using full full_chain_iff_chain by blast
  hence chain': "chain R' (lmap f xs)"
    using chain_lmap r_r' by metis

  have "lfinite xs \<longrightarrow> (\<forall>y. \<not> R (llast xs) y)"
    using full unfolding full_chain_iff_chain by blast
  hence "lfinite (lmap f xs) \<longrightarrow> (\<forall>y. \<not> R' (llast (lmap f xs)) y)"
    by (metis chain chain_not_lnull lfinite_lmap llast_lmap r'_r)
  thus ?thesis
    using chain' unfolding full_chain_iff_chain by blast
qed

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
