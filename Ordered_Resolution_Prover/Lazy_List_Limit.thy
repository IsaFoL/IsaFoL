(*  Title:       Limits of Lazy Lists
    Author:      Jasmin Blanchette <jasmin.blanchette at inria.fr>, 2014
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2014
    Maintainer:  Jasmin Blanchette <jasmin.blanchette at inria.fr>
*)

section {* Limits of Lazy Lists *}

theory Lazy_List_Limit
imports "$AFP/Coinductive/Coinductive_List"
begin

text {*
Lazy lists, as defined in the \emph{Archive of Formal Proofs}, provide finite and infinite lists in
one type, defined coinductively. The present theory introduces the concept of the union of all
elements of a lazy list of sets and the limit of such a lazy list. The definitions are stated more
generally in terms of lattices. The basis for this theory is Section 4.1 (``Theorem Proving
Processes'') of Bachmair and Ganzinger's chapter.
*}

lemma enat_0_le[simp]: "enat 0 \<le> n"  -- "belongs elsewhere"
  by (cases n) auto

definition lSup :: "('a::complete_distrib_lattice) llist \<Rightarrow> 'a" where
  "lSup As = (\<Squnion>i \<in> {i. enat i < llength As}. lnth As i)"

lemma lnth_subset_lSup: "enat i < llength xs \<Longrightarrow> lnth xs i \<subseteq> lSup xs"
  unfolding lSup_def by auto

lemma lSup_LNil[simp]: "lSup LNil = {}"
  unfolding lSup_def by auto

lemma lSup_LCons[simp]: "lSup (LCons A As) = A \<union> lSup As"
unfolding lSup_def
proof (intro subset_antisym subsetI)
  fix x
  assume "x \<in> (\<Squnion>i \<in> {i. enat i < llength (LCons A As)}. lnth (LCons A As) i)"
  then obtain i where len: "enat i < llength (LCons A As)" and nth: "x \<in> lnth (LCons A As) i"
    by blast
  from nth have "x \<in> A \<or> i > 0 \<and> x \<in> lnth As (i - 1)"
    by (metis lnth_LCons' neq0_conv)
  hence "x \<in> A \<or> (\<exists>i. enat i < llength As \<and> x \<in> lnth As i)"
    using len
    by (metis Suc_pred' eSuc_enat iless_Suc_eq less_irrefl llength_LCons not_less order_trans)
  thus "x \<in> A \<union> (\<Squnion>i \<in> {i. enat i < llength As}. lnth As i)"
    by blast
next
  fix x
  assume "x \<in> A \<union> (\<Squnion>i \<in> {i. enat i < llength As}. lnth As i)"
  thus "x \<in> (\<Squnion>i \<in> {i. enat i < llength (LCons A As)}. lnth (LCons A As) i)"
    by auto (metis i0_lb lnth_0 zero_enat_def, metis Suc_ile_eq lnth_Suc_LCons)
qed

lemma lhd_subset_lSup: "\<not> lnull As \<Longrightarrow> lhd As \<subseteq> lSup As"
  by (cases As) simp_all

definition lSup_upto :: "('a::Sup) llist \<Rightarrow> nat \<Rightarrow> 'a" where
  "lSup_upto As j = (\<Squnion>i \<in> {i. enat i < llength As \<and> i \<le> j}. lnth As i)"

lemma lSup_upto_mono: "j \<le> k \<Longrightarrow> lSup_upto As j \<subseteq> lSup_upto As k"
  unfolding lSup_upto_def by auto

lemma lSup_upto_subset_lSup: "j \<le> k \<Longrightarrow> lSup_upto As j \<subseteq> lSup As"
  unfolding lSup_def lSup_upto_def by auto

lemma elem_lSup_imp_lSup_upto: "x \<in> lSup As \<Longrightarrow> \<exists>j. x \<in> lSup_upto As j"
  unfolding lSup_def lSup_upto_def by blast

lemma finite_lSup_imp_lSup_upto:
  assumes "finite A" and "A \<subseteq> lSup As"
  shows "\<exists>k. A \<subseteq> lSup_upto As k"
using assms
proof induct
  case empty
  thus ?case
    by simp
next
  case (insert x A)
  from insert.prems have x: "x \<in> lSup As" and a: "A \<subseteq> lSup As"
    by simp_all
  from x obtain k where k: "x \<in> lSup_upto As k"
    using elem_lSup_imp_lSup_upto by fast
  from a obtain k' where k': "A \<subseteq> lSup_upto As k'"
    using insert.hyps(3) by fast
  have "insert x A \<subseteq> lSup_upto As (max k k')"
    using k k'
    by (metis insert_absorb insert_subset lSup_upto_mono max.cobounded2 max.commute order_trans)
  thus ?case
    by fast
qed

text {*
\begin{nit}
The chapter does not specify the range of $i$ and $j$. Clearly, $j$ must be bounded by the length of
the list, but it is less obvious that $i$ also must be bounded, to avoid the inner intersection to
expand to be the universal set for values of $i$ beyond the length of a finite list.
\end{nit}
*}

definition llimit :: "('a::{Inf,Sup}) llist \<Rightarrow> 'a" where
  "llimit As = (\<Squnion>i \<in> {i. enat i < llength As}. \<Sqinter>j \<in> {j. i \<le> j \<and> enat j < llength As}. lnth As j)"

lemma llimit_subset_lSup: "llimit As \<subseteq> lSup As"
  unfolding llimit_def lSup_def by fast

end
