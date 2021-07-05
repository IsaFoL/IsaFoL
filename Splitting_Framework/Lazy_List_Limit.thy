(*  Title:       Limit Points of Lazy Lists
    Author:      Asta Halkjær From <ahfrom at dtu.dk>, 2021
*)

section \<open>Limit Points of Lazy Lists\<close>

theory Lazy_List_Limit
  imports Lazy_List_Limsup Ordered_Resolution_Prover.Lazy_List_Liminf
begin

subsection \<open>Homeomorphic embedding\<close>

text \<open>Lemmas inspired by the Sublist theory on finite lists\<close>

definition llist_emb :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a llist \<Rightarrow> 'a llist \<Rightarrow> bool"
  where "llist_emb P xs ys \<equiv>
    \<exists>f. (\<forall>i j. i < j \<longrightarrow> f i < f j)
      \<and> (\<forall>i. enat i < llength xs \<longrightarrow> enat (f i) < llength ys \<and> P (lnth xs i) (lnth ys (f i)))"

lemma llist_emb_mono:
  assumes "\<And>x y. P x y \<longrightarrow> Q x y"
  shows "llist_emb P xs ys \<longrightarrow> llist_emb Q xs ys"
  unfolding llist_emb_def by (meson assms)

lemma list_emb'_Nil2 [simp]:
  assumes "llist_emb P xs LNil" shows "xs = LNil"
  using assms unfolding llist_emb_def
  by (metis i0_less llength_eq_0 lnull_def not_less_zero zero_enat_def)

lemma llist_emb_refl:
  assumes "\<And>x. x \<in> lset xs \<Longrightarrow> P x x"
  shows "llist_emb P xs xs"
  using assms unfolding llist_emb_def by (meson in_lset_conv_lnth)

lemma llist_emb_Cons_Nil [simp]: "llist_emb P (LCons x xs) LNil = False"
  using list_emb'_Nil2 by blast

lemma llist_emb_append2 [intro]:
  assumes "llist_emb P xs ys" "lfinite zs"
  shows "llist_emb P xs (lappend zs ys)"
proof -
  obtain f where *:
    \<open>\<forall>i j. i < j \<longrightarrow> f i < f j\<close>
    \<open>\<forall>i. enat i < llength xs \<longrightarrow> enat (f i) < llength ys \<and> P (lnth xs i) (lnth ys (f i))\<close>
    using assms unfolding llist_emb_def by blast

  obtain n where n: \<open>enat n = llength zs\<close>
    using assms(2) length_list_of by blast

  let ?f = \<open>\<lambda>i. f i + n\<close>

  have \<open>\<forall>i j. i < j \<longrightarrow> ?f i < ?f j\<close>
    using *(1) by simp
  moreover have \<open>\<forall>i. enat i < llength xs \<longrightarrow>
      enat (?f i) < llength (lappend zs ys) \<and> P (lnth xs i) (lnth (lappend zs ys) (?f i))\<close>
    using *(2) by (metis n add.commute add_diff_cancel_right' enat_less_enat_plusI2 le_add2
        llength_lappend lnth_lappend2)
  ultimately show ?thesis
    unfolding llist_emb_def by meson
qed

lemma llist_emb_prefix [intro]:
  assumes "llist_emb P xs ys"
  shows "llist_emb P xs (lappend ys zs)"
proof -
  obtain f where *:
    \<open>\<forall>i j. i < j \<longrightarrow> f i < f j\<close>
    \<open>\<forall>i. enat i < llength xs \<longrightarrow> enat (f i) < llength ys \<and> P (lnth xs i) (lnth ys (f i))\<close>
    using assms unfolding llist_emb_def by blast
  then have \<open>\<forall>i. enat i < llength xs \<longrightarrow>
      enat (f i) < llength (lappend ys zs) \<and> P (lnth xs i) (lnth (lappend ys zs) (f i))\<close>
    by (metis enat_le_plus_same(1) le_less_trans llength_lappend lprefix_lappend
        lprefix_lnthD not_le)
  then show ?thesis
    using *(1) unfolding llist_emb_def by meson
qed

lemma llist_emb_tail:
  assumes \<open>llist_emb P (LCons x xs) ys\<close>
  shows \<open>llist_emb P xs ys\<close>
proof -
  obtain f where *:
    \<open>\<forall>i j. i < j \<longrightarrow> f i < f j\<close>
    \<open>\<forall>i. enat i < llength (LCons x xs) \<longrightarrow>
      enat (f i) < llength ys \<and> P (lnth (LCons x xs) i) (lnth ys (f i))\<close>
    using assms unfolding llist_emb_def by blast

  let ?f = \<open>\<lambda>i. f (i + 1)\<close>

  have \<open>\<forall>i j. i < j \<longrightarrow> ?f i < ?f j\<close>
    using *(1) by simp
  moreover have \<open>\<forall>i. enat i < llength xs \<longrightarrow>
      enat (?f i) < llength ys \<and> P (lnth xs i) (lnth ys (?f i))\<close>
    using *(2) by (metis add.commute enat_less_enat_plusI2 eq_LConsD llength_LCons llist.disc(2)
        lnth_ltl one_enat_def plus_1_eSuc(1) plus_1_eq_Suc)
  ultimately show ?thesis
    unfolding llist_emb_def by meson
qed

lemma llist_emb_LCons_True:
  assumes \<open>llist_emb P (LCons x xs) (LCons y ys)\<close> \<open>P x y\<close>
  shows \<open>llist_emb P xs ys\<close>
  sorry (* TODO: how to show this? *)

lemma llist_emb_LCons_False:
  assumes \<open>llist_emb P (LCons x xs) (LCons y ys)\<close> \<open>\<not> P x y\<close>
  shows \<open>llist_emb P (LCons x xs) ys\<close>
  oops (* TODO: how to show this? *)

lemma llength_takeWhile:
  assumes \<open>i < llength (ltakeWhile P ys)\<close>
  shows \<open>P (lnth ys i)\<close>
  using assms by (metis in_lset_conv_lnth lset_ltakeWhileD ltakeWhile_nth)

lemma llist_emb_ldropWhile:
  assumes \<open>llist_emb P (LCons x xs) ys\<close>
  shows \<open>llist_emb P (LCons x xs) (ldropWhile (\<lambda>y. \<not> P x y) ys)\<close> (is \<open>llist_emb P ?xs ?ys\<close>)
proof -
  obtain f where *:
    \<open>\<forall>i j. i < j \<longrightarrow> f i < f j\<close>
    \<open>\<forall>i. enat i < llength ?xs \<longrightarrow> enat (f i) < llength ys \<and> P (lnth ?xs i) (lnth ys (f i))\<close>
    using assms unfolding llist_emb_def by blast

  obtain n where n: \<open>enat n = llength (ltakeWhile (\<lambda>y. \<not> P x y) ys)\<close>
    using *(2) by (metis "*"(2) in_lset_conv_lnth lfinite_llength_enat
        llength_ltakeWhile_eq_infinity lset_intros(1) lset_ltakeWhileD ltakeWhile_K_True)

  have \<open>P x (lnth ys (f 0))\<close>
    using *(2) by (metis eSuc_ne_0 gr_zeroI llength_LCons lnth_0 zero_enat_def)
  then have fi: \<open>\<forall>i. n \<le> f i\<close>
    using n *(1) by (metis enat_ord_simps(2) le_zero_eq llength_takeWhile nat_less_le
        not_le_imp_less order_trans)

  let ?f = \<open>\<lambda>i. f i - n\<close>

  have \<open>\<forall>i j. i < j \<longrightarrow> ?f i < ?f j\<close>
    using *(1) fi using diff_less_mono by presburger
  moreover have \<open>P x (lnth ?ys (?f 0))\<close>
    using \<open>P x (lnth ys (f 0))\<close> fi n
    by (metis lappend_ltakeWhile_ldropWhile lnth_lappend2)
  have \<open>\<forall>i. enat i < llength ?xs \<longrightarrow>
      enat (?f i) < llength ?ys \<and> P (lnth ?xs i) (lnth ?ys (?f i))\<close>
    using *(2) fi n
    by (metis lappend_ltakeWhile_ldropWhile ldropn_Suc_conv_ldropn ldropn_eq_LConsD ldropn_lappend2
        lnth_lappend2 of_nat_eq_enat of_nat_le_iff the_enat.simps)
  ultimately show ?thesis
    unfolding llist_emb_def by meson
qed

lemma llist_emb_ConsD:
  assumes "llist_emb P (LCons x xs) ys"
  shows "\<exists>us v vs. ys = lappend us (LCons v vs) \<and> P x v \<and> llist_emb P xs vs"
proof -
  obtain f where *:
    \<open>\<forall>i j. i < j \<longrightarrow> f i < f j\<close>
    \<open>\<forall>i. enat i < llength (LCons x xs) \<longrightarrow>
      enat (f i) < llength ys \<and> P (lnth (LCons x xs) i) (lnth ys (f i))\<close>
    using assms unfolding llist_emb_def by blast

  let ?us = \<open>ltakeWhile (\<lambda>y. \<not> P x y) ys\<close>
  let ?vvs = \<open>ldropWhile (\<lambda>y. \<not> P x y) ys\<close>

  have ys: \<open>ys = lappend ?us ?vvs\<close>
    by simp

  show ?thesis
  proof (cases ?vvs)
    case LNil
    then have False
      by (metis assms llist_emb_Cons_Nil llist_emb_ldropWhile)
    then show ?thesis ..
  next
    case (LCons v vs)
    then have \<open>ys = lappend ?us (LCons v vs)\<close>
      using ys by simp
    moreover have \<open>P x v\<close>
      by (metis LCons eq_LConsD lhd_ldropWhile_conv_lnth llength_ltakeWhile_lt_iff llist.disc(2)
          lnth_llength_ltakeWhile lnull_ldropWhile)
    moreover from this have \<open>llist_emb P xs vs\<close>
      by (metis LCons assms llist_emb_LCons_True llist_emb_ldropWhile)
    ultimately show ?thesis
      by blast
  qed
qed

lemma llist_emb_appendD:
  assumes "llist_emb P (lappend xs ys) zs"
  shows "\<exists>us vs. zs = lappend us vs \<and> llist_emb P xs us \<and> llist_emb P ys vs"
  using assms oops (* TODO *)

lemma llist_emb_length:
  assumes "llist_emb P xs ys"
  shows "llength xs \<le> llength ys"
  using assms oops (* TODO *)

lemma llist_emb_set:
  assumes "llist_emb P xs ys" and "x \<in> lset xs"
  obtains y where "y \<in> lset ys" and "P x y"
  using assms oops (* TODO *)

lemma llist_emb_Cons_iff1 [simp]:
  assumes "P x y"
  shows "llist_emb P (LCons x xs) (LCons y ys) \<longleftrightarrow> llist_emb P xs ys"
  using assms oops (* TODO *)

lemma llist_emb_Cons_iff2 [simp]:
  assumes "\<not> P x y"
  shows "llist_emb P (LCons x xs) (LCons y ys) \<longleftrightarrow> llist_emb P (LCons x xs) ys"
  using assms oops (* TODO *)

subsection \<open>Limit Points\<close>

abbreviation lsubseq :: "'a llist \<Rightarrow> 'a llist \<Rightarrow> bool"
  where "lsubseq xs ys \<equiv> llist_emb (=) xs ys"

definition limit_point :: \<open>'a set \<Rightarrow> 'a set llist \<Rightarrow> bool\<close> where
  \<open>limit_point X Xs \<equiv> \<exists>Xs'. lsubseq Xs' Xs \<and> X = Limsup_llist Xs' \<and> X = Liminf_llist Xs'\<close>

end