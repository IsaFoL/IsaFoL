(*  Title:       Liminf of Lazy Lists
    Author:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2014, 2017
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2014
    Maintainer:  Jasmin Blanchette <j.c.blanchette at vu.nl>
*)

section \<open>Liminf of Lazy Lists\<close>

theory Lazy_List_Liminf
  imports Coinductive.Coinductive_List
begin

text \<open>
Lazy lists, as defined in the \emph{Archive of Formal Proofs}, provide finite and infinite lists in
one type, defined coinductively. The present theory introduces the concept of the union of all
elements of a lazy list of sets and the limit of such a lazy list. The definitions are stated more
generally in terms of lattices. The basis for this theory is Section 4.1 (``Theorem Proving
Processes'') of Bachmair and Ganzinger's chapter.
\<close>

definition Sup_llist :: "'a set llist \<Rightarrow> 'a set" where
  "Sup_llist Xs = (\<Union>i \<in> {i. enat i < llength Xs}. lnth Xs i)"

lemma lnth_subset_Sup_llist: "enat i < llength xs \<Longrightarrow> lnth xs i \<subseteq> Sup_llist xs"
  unfolding Sup_llist_def by auto

lemma Sup_llist_LNil[simp]: "Sup_llist LNil = {}"
  unfolding Sup_llist_def by auto

lemma Sup_llist_LCons[simp]: "Sup_llist (LCons X Xs) = X \<union> Sup_llist Xs"
  unfolding Sup_llist_def
proof (intro subset_antisym subsetI)
  fix x
  assume "x \<in> (\<Union>i \<in> {i. enat i < llength (LCons X Xs)}. lnth (LCons X Xs) i)"
  then obtain i where len: "enat i < llength (LCons X Xs)" and nth: "x \<in> lnth (LCons X Xs) i"
    by blast
  from nth have "x \<in> X \<or> i > 0 \<and> x \<in> lnth Xs (i - 1)"
    by (metis lnth_LCons' neq0_conv)
  then have "x \<in> X \<or> (\<exists>i. enat i < llength Xs \<and> x \<in> lnth Xs i)"
    by (metis len Suc_pred' eSuc_enat iless_Suc_eq less_irrefl llength_LCons not_less order_trans)
  then show "x \<in> X \<union> (\<Union>i \<in> {i. enat i < llength Xs}. lnth Xs i)"
    by blast
qed ((auto)[], metis i0_lb lnth_0 zero_enat_def, metis Suc_ile_eq lnth_Suc_LCons)

lemma lhd_subset_Sup_llist: "\<not> lnull Xs \<Longrightarrow> lhd Xs \<subseteq> Sup_llist Xs"
  by (cases Xs) simp_all

definition Sup_upto_llist :: "'a set llist \<Rightarrow> nat \<Rightarrow> 'a set" where
  "Sup_upto_llist Xs j = (\<Union>i \<in> {i. enat i < llength Xs \<and> i \<le> j}. lnth Xs i)"

lemma Sup_upto_llist_mono: "j \<le> k \<Longrightarrow> Sup_upto_llist Xs j \<subseteq> Sup_upto_llist Xs k"
  unfolding Sup_upto_llist_def by auto

lemma Sup_upto_llist_subset_Sup_llist: "j \<le> k \<Longrightarrow> Sup_upto_llist Xs j \<subseteq> Sup_llist Xs"
  unfolding Sup_llist_def Sup_upto_llist_def by auto

lemma elem_Sup_llist_imp_Sup_upto_llist: "x \<in> Sup_llist Xs \<Longrightarrow> \<exists>j. x \<in> Sup_upto_llist Xs j"
  unfolding Sup_llist_def Sup_upto_llist_def by blast

lemma finite_Sup_llist_imp_Sup_upto_llist:
  assumes "finite X" and "X \<subseteq> Sup_llist Xs"
  shows "\<exists>k. X \<subseteq> Sup_upto_llist Xs k"
  using assms
proof induct
  case (insert x X)
  hence x: "x \<in> Sup_llist Xs" and X: "X \<subseteq> Sup_llist Xs"
    by simp+
  from x obtain k where k: "x \<in> Sup_upto_llist Xs k"
    using elem_Sup_llist_imp_Sup_upto_llist by fast
  from X obtain k' where k': "X \<subseteq> Sup_upto_llist Xs k'"
    using insert.hyps(3) by fast
  have "insert x X \<subseteq> Sup_upto_llist Xs (max k k')"
    using k k'
    by (metis insert_absorb insert_subset Sup_upto_llist_mono max.cobounded2 max.commute
        order.trans)
  then show ?case
    by fast
qed simp

definition Liminf_llist :: "'a set llist \<Rightarrow> 'a set" where
  "Liminf_llist Xs =
   (\<Union>i \<in> {i. enat i < llength Xs}. \<Inter>j \<in> {j. i \<le> j \<and> enat j < llength Xs}. lnth Xs j)"

lemma Liminf_llist_subset_Sup_llist: "Liminf_llist Xs \<subseteq> Sup_llist Xs"
  unfolding Liminf_llist_def Sup_llist_def by fast

end
