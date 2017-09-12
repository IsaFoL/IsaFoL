(*  Title:       Limits of Lazy Lists
    Author:      Jasmin Blanchette <jasmin.blanchette at inria.fr>, 2014
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2014
    Maintainer:  Jasmin Blanchette <jasmin.blanchette at inria.fr>
*)

section \<open>Limits of Lazy Lists\<close>

theory Lazy_List_Limit
  imports "$AFP/Coinductive/Coinductive_List"
begin

text \<open>
Lazy lists, as defined in the \emph{Archive of Formal Proofs}, provide finite and infinite lists in
one type, defined coinductively. The present theory introduces the concept of the union of all
elements of a lazy list of sets and the limit of such a lazy list. The definitions are stated more
generally in terms of lattices. The basis for this theory is Section 4.1 (``Theorem Proving
Processes'') of Bachmair and Ganzinger's chapter.
\<close>

definition Sup_llist :: "('a::complete_distrib_lattice) llist \<Rightarrow> 'a" where
  "Sup_llist As = (\<Squnion>i \<in> {i. enat i < llength As}. lnth As i)"

lemma lnth_subset_Sup_llist: "enat i < llength xs \<Longrightarrow> lnth xs i \<subseteq> Sup_llist xs"
  unfolding Sup_llist_def by auto

lemma Sup_llist_LNil[simp]: "Sup_llist LNil = {}"
  unfolding Sup_llist_def by auto

lemma Sup_llist_LCons[simp]: "Sup_llist (LCons A As) = A \<union> Sup_llist As"
  unfolding Sup_llist_def
proof (intro subset_antisym subsetI)
  fix x
  assume "x \<in> (\<Squnion>i \<in> {i. enat i < llength (LCons A As)}. lnth (LCons A As) i)"
  then obtain i where len: "enat i < llength (LCons A As)" and nth: "x \<in> lnth (LCons A As) i"
    by blast
  from nth have "x \<in> A \<or> i > 0 \<and> x \<in> lnth As (i - 1)"
    by (metis lnth_LCons' neq0_conv)
  hence "x \<in> A \<or> (\<exists>i. enat i < llength As \<and> x \<in> lnth As i)"
    by (metis len Suc_pred' eSuc_enat iless_Suc_eq less_irrefl llength_LCons not_less order_trans)
  thus "x \<in> A \<union> (\<Squnion>i \<in> {i. enat i < llength As}. lnth As i)"
    by blast
qed ((auto)[], metis i0_lb lnth_0 zero_enat_def, metis Suc_ile_eq lnth_Suc_LCons)

lemma lhd_subset_Sup_llist: "\<not> lnull As \<Longrightarrow> lhd As \<subseteq> Sup_llist As"
  by (cases As) simp_all

definition Sup_upto_llist :: "('a::Sup) llist \<Rightarrow> nat \<Rightarrow> 'a" where
  "Sup_upto_llist As j = (\<Squnion>i \<in> {i. enat i < llength As \<and> i \<le> j}. lnth As i)"

lemma Sup_upto_llist_mono: "j \<le> k \<Longrightarrow> Sup_upto_llist As j \<subseteq> Sup_upto_llist As k"
  unfolding Sup_upto_llist_def by auto

lemma Sup_upto_llist_subset_Sup_llist: "j \<le> k \<Longrightarrow> Sup_upto_llist As j \<subseteq> Sup_llist As"
  unfolding Sup_llist_def Sup_upto_llist_def by auto

lemma elem_Sup_llist_imp_Sup_upto_llist: "x \<in> Sup_llist As \<Longrightarrow> \<exists>j. x \<in> Sup_upto_llist As j"
  unfolding Sup_llist_def Sup_upto_llist_def by blast

lemma finite_Sup_llist_imp_Sup_upto_llist:
  assumes "finite A" and "A \<subseteq> Sup_llist As"
  shows "\<exists>k. A \<subseteq> Sup_upto_llist As k"
  using assms
proof induct
  case empty
  thus ?case
    by simp
next
  case (insert x A)
  from insert.prems have x: "x \<in> Sup_llist As" and a: "A \<subseteq> Sup_llist As"
    by simp_all
  from x obtain k where k: "x \<in> Sup_upto_llist As k"
    using elem_Sup_llist_imp_Sup_upto_llist by fast
  from a obtain k' where k': "A \<subseteq> Sup_upto_llist As k'"
    using insert.hyps(3) by fast
  have "insert x A \<subseteq> Sup_upto_llist As (max k k')"
    using k k'
    by (metis insert_absorb insert_subset Sup_upto_llist_mono max.cobounded2 max.commute order_trans)
  thus ?case
    by fast
qed

text \<open>
\begin{nit}
The chapter does not specify the range of $i$ and $j$. Clearly, $j$ must be bounded by the length of
the list, but it is less obvious that $i$ also must be bounded, to avoid the inner intersection to
expand to be the universal set for values of $i$ beyond the length of a finite list.
\end{nit}
\<close>

definition limit_llist :: "('a::{Inf,Sup}) llist \<Rightarrow> 'a" where
  "limit_llist As = (\<Squnion>i \<in> {i. enat i < llength As}. \<Sqinter>j \<in> {j. i \<le> j \<and> enat j < llength As}. lnth As j)"

lemma limit_llist_subset_Sup_llist: "limit_llist As \<subseteq> Sup_llist As"
  unfolding limit_llist_def Sup_llist_def by fast

end
