(* Title:        Utilities for Given Clause Loops
   Authors:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2022-2023
   Maintainer:   Jasmin Blanchette <j.c.blanchette at vu.nl>
*)

section \<open>Utilities for Given Clause Loops\<close>

text \<open>This section contains various lemmas used by the rest of the formalization
of given clause procedures.\<close>

theory Given_Clause_Loops_Util
  imports
    "HOL-Library.FSet"
    "HOL-Library.Multiset"
    Ordered_Resolution_Prover.Lazy_List_Chain
    Weighted_Path_Order.Multiset_Extension_Pair
    Lambda_Free_RPOs.Lambda_Free_Util
begin

hide_const (open) Seq.chain

hide_fact (open) Abstract_Rewriting.chain_mono

declare fset_of_list.rep_eq [simp]

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

lemma Union_Setcompr_member_mset_mono:
  assumes sub: "P \<subseteq># Q"
  shows "\<Union> {f x |x. x \<in># P} \<subseteq> \<Union> {f x |x. x \<in># Q}"
proof -
  have "{f x |x. x \<in># P} \<subseteq> {f x |x. x \<in># Q}"
    by (rule Collect_mono) (metis sub mset_subset_eqD)
  thus ?thesis
    by (simp add: Sup_subset_mono)
qed

lemma singletons_in_mult1: "(x, y) \<in> R \<Longrightarrow> ({#x#}, {#y#}) \<in> mult1 R"
  by (metis add_mset_add_single insert_DiffM mult1I single_eq_add_mset)

lemma singletons_in_mult: "(x, y) \<in> R \<Longrightarrow> ({#x#}, {#y#}) \<in> mult R"
  by (simp add: mult_def singletons_in_mult1 trancl.intros(1))

lemma multiset_union_diff_assoc:
  fixes A B C :: "'a multiset"
  assumes "A \<inter># C = {#}"
  shows "A + B - C = A + (B - C)"
  by (metis assms multiset_union_diff_commute union_commute)

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

lemma distinct_imp_notin_set_drop_Suc:
  assumes
    "distinct xs"
    "i < length xs"
    "xs ! i = x"
  shows "x \<notin> set (drop (Suc i) xs)"
  by (metis Cons_nth_drop_Suc assms distinct.simps(2) distinct_drop)

lemma distinct_set_drop_removeAll_hd:
  assumes
    "distinct xs"
    "xs \<noteq> []"
  shows "set (drop n (removeAll (hd xs) xs)) = set (drop (Suc n) xs)"
  using assms
  by (metis distinct.simps(2) drop_Suc list.exhaust_sel removeAll.simps(2) removeAll_id)

lemma set_drop_removeAll: "set (drop n (removeAll y xs)) \<subseteq> set (drop n xs)"
proof (induct n arbitrary: xs)
  case 0
  then show ?case
    by auto
next
  case (Suc n)
  then show ?case
  proof (cases xs)
    case Nil
    then show ?thesis
      by auto
  next
    case (Cons x xs')
    then show ?thesis
      by (metis Suc Suc_n_not_le_n drop_Suc_Cons nat_le_linear removeAll.simps(2)
          set_drop_subset_set_drop subset_code(1))
  qed
qed

lemma set_drop_fold_removeAll: "set (drop k (fold removeAll ys xs)) \<subseteq> set (drop k xs)"
proof (induct ys arbitrary: xs)
  case (Cons y ys)
  note ih = this(1)

  have "set (drop k (fold removeAll ys (removeAll y xs))) \<subseteq> set (drop k (removeAll y xs))"
    using ih[of "removeAll y xs"] .
  also have "... \<subseteq> set (drop k xs)"
    by (meson set_drop_removeAll)
  finally show ?case
    by simp
qed simp

lemma set_drop_append_subseteq: "set (drop n (xs @ ys)) \<subseteq> set (drop n xs) \<union> set ys"
  by (metis drop_append set_append set_drop_subset sup.idem sup.orderI sup_mono)

lemma distinct_fold_removeAll:
  assumes dist: "distinct xs"
  shows "distinct (fold removeAll ys xs)"
  using dist
proof (induct ys arbitrary: xs)
  case Nil
  then show ?case
    using dist by simp
next
  case (Cons y ys)
  note ih = this(1) and dist_xs = this(2)

  have dist_yxs: "distinct (removeAll y xs)"
    using dist_xs by (simp add: distinct_removeAll)

  show ?case
    by simp (rule ih[OF dist_yxs])
qed

lemma set_drop_append_cons: "set (drop n (xs @ ys)) \<subseteq> set (drop n (xs @ y # ys))"
proof (induct n arbitrary: xs)
  case 0
  then show ?case
    by auto
next
  case (Suc n)
  note ih = this(1)

  show ?case
  proof (cases xs)
    case Nil
    then show ?thesis
      using set_drop_subset_set_drop[of n "Suc n"] by force
  next
    case (Cons x xs')
    note xs = this(1)

    have "set (drop n (xs' @ ys)) \<subseteq> set (drop n (xs' @ y # ys))"
      using ih .
    thus ?thesis
      unfolding xs by auto
  qed
qed

lemma chain_ltl: "chain R sts \<Longrightarrow> \<not> lnull (ltl sts) \<Longrightarrow> chain R (ltl sts)"
  by (metis chain.simps eq_LConsD lnull_def)

end
