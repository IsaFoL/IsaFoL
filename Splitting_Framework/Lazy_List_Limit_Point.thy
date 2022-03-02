(*  Title:       Limit Points of Lazy Lists
    Author:      Asta Halkjær From <ahfrom at dtu.dk>, 2021
*)

section \<open>Limit Points of Lazy Lists\<close>

theory Lazy_List_Limit_Point
  imports Lazy_List_Limsup Ordered_Resolution_Prover.Lazy_List_Liminf
begin

subsection \<open>Library\<close>

lemma lnth_ldrop':
  assumes \<open>enat i < llength xs\<close>
  shows \<open>lnth xs (i + k) = lnth (ldrop i xs) k\<close>
  using assms by (metis diff_add_inverse lappend_ltake_ldrop le_add1 llength_ltake lnth_lappend2
      min_def order.strict_implies_order)

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
  obtain f where f:
    \<open>\<forall>i j. i < j \<longrightarrow> f i < f j\<close>
    \<open>\<forall>i. enat i < llength xs \<longrightarrow> enat (f i) < llength ys \<and> P (lnth xs i) (lnth ys (f i))\<close>
    using assms unfolding llist_emb_def by blast

  obtain n where n: \<open>enat n = llength zs\<close>
    using assms(2) length_list_of by blast

  let ?f = \<open>\<lambda>i. f i + n\<close>

  have \<open>\<forall>i j. i < j \<longrightarrow> ?f i < ?f j\<close>
    using f(1) by simp
  moreover have \<open>\<forall>i. enat i < llength xs \<longrightarrow>
      enat (?f i) < llength (lappend zs ys) \<and> P (lnth xs i) (lnth (lappend zs ys) (?f i))\<close>
    using f(2) by (metis n add.commute add_diff_cancel_right' enat_less_enat_plusI2 le_add2
        llength_lappend lnth_lappend2)
  ultimately show ?thesis
    unfolding llist_emb_def by meson
qed

lemma llist_emb_prefix [intro]:
  assumes "llist_emb P xs ys"
  shows "llist_emb P xs (lappend ys zs)"
proof -
  obtain f where f:
    \<open>\<forall>i j. i < j \<longrightarrow> f i < f j\<close>
    \<open>\<forall>i. enat i < llength xs \<longrightarrow> enat (f i) < llength ys \<and> P (lnth xs i) (lnth ys (f i))\<close>
    using assms unfolding llist_emb_def by blast
  then have \<open>\<forall>i. enat i < llength xs \<longrightarrow>
      enat (f i) < llength (lappend ys zs) \<and> P (lnth xs i) (lnth (lappend ys zs) (f i))\<close>
    by (metis enat_le_plus_same(1) le_less_trans llength_lappend lprefix_lappend
        lprefix_lnthD not_le)
  then show ?thesis
    using f(1) unfolding llist_emb_def by meson
qed

lemma llist_emb_LCons:
  assumes \<open>llist_emb P xs ys\<close> \<open>P x y\<close>
  shows \<open>llist_emb P (LCons x xs) (LCons y ys)\<close>
proof -
  obtain f where f:
    \<open>\<forall>i j. i < j \<longrightarrow> f i < f j\<close>
    \<open>\<forall>i. enat i < llength xs \<longrightarrow> enat (f i) < llength ys \<and> P (lnth xs i) (lnth ys (f i))\<close>
    using assms unfolding llist_emb_def by blast

  let ?f = \<open>\<lambda>i. if i = 0 then 0 else f (i - 1) + 1\<close>

  have \<open>\<forall>i j. i < j \<longrightarrow> ?f i < ?f j\<close>
    using f(1) by simp
  moreover have \<open>\<forall>i. enat i < llength (LCons x xs) \<longrightarrow>
      enat (?f i) < llength (LCons y ys) \<and> P (lnth (LCons x xs) i) (lnth (LCons y ys) (?f i))\<close>
    using f(2) \<open>P x y\<close>
    by (smt (z3) Suc_ile_eq add.commute add_diff_inverse_nat iless_Suc_eq less_one llength_LCons
        llength_eq_0 llist.disc(2) lnth_0 lnth_Suc_LCons not_gr_zero plus_1_eq_Suc zero_enat_def)
  ultimately show ?thesis
    unfolding llist_emb_def using exI[where x=\<open>?f\<close>] by simp
qed

lemma llist_emb_tail:
  assumes \<open>llist_emb P (LCons x xs) ys\<close>
  shows \<open>llist_emb P xs ys\<close>
proof -
  obtain f where f:
    \<open>\<forall>i j. i < j \<longrightarrow> f i < f j\<close>
    \<open>\<forall>i. enat i < llength (LCons x xs) \<longrightarrow>
      enat (f i) < llength ys \<and> P (lnth (LCons x xs) i) (lnth ys (f i))\<close>
    using assms unfolding llist_emb_def by blast

  let ?f = \<open>\<lambda>i. f (i + 1)\<close>

  have \<open>\<forall>i j. i < j \<longrightarrow> ?f i < ?f j\<close>
    using f(1) by simp
  moreover have \<open>\<forall>i. enat i < llength xs \<longrightarrow>
      enat (?f i) < llength ys \<and> P (lnth xs i) (lnth ys (?f i))\<close>
    using f(2) by (metis add.commute enat_less_enat_plusI2 eq_LConsD llength_LCons llist.disc(2)
        lnth_ltl one_enat_def plus_1_eSuc(1) plus_1_eq_Suc)
  ultimately show ?thesis
    unfolding llist_emb_def by meson
qed

lemma llist_emb_tail2:
  assumes \<open>llist_emb P (LCons x xs) (LCons y ys)\<close>
  shows \<open>llist_emb P xs ys\<close>
proof -
  obtain f where f:
    \<open>\<forall>i j. i < j \<longrightarrow> f i < f j\<close>
    \<open>\<forall>i. enat i < llength (LCons x xs) \<longrightarrow>
      enat (f i) < llength (LCons y ys) \<and> P (lnth (LCons x xs) i) (lnth (LCons y ys) (f i))\<close>
    using assms unfolding llist_emb_def by blast

  let ?f = \<open>\<lambda>i. f (i + 1) - 1\<close>

  have \<open>\<forall>i j. i < j \<longrightarrow> ?f i < ?f j\<close>
    using f(1) by (metis add.commute add_less_cancel_left diff_less_mono less_nat_zero_code
        less_one not_le_imp_less)
  moreover have \<open>\<forall>i. enat i < llength xs \<longrightarrow> enat (?f i) < llength ys \<and> P (lnth xs i) (lnth ys (?f i))\<close>
    using f(2) by simp (metis One_nat_def Suc_diff_1 Suc_ile_eq Suc_n_not_le_n f(1) le_less_linear
        lnth_Suc_LCons nat_neq_iff not_less0)
  ultimately show ?thesis
    unfolding llist_emb_def by meson
qed

lemma llist_emb_LCons_False:
  assumes \<open>llist_emb P (LCons x xs) (LCons y ys)\<close> \<open>\<not> P x y\<close>
  shows \<open>llist_emb P (LCons x xs) ys\<close>
proof -
  obtain f where f:
    \<open>\<forall>i j. i < j \<longrightarrow> f i < f j\<close>
    \<open>\<forall>i. enat i < llength (LCons x xs) \<longrightarrow>
      enat (f i) < llength (LCons y ys) \<and> P (lnth (LCons x xs) i) (lnth (LCons y ys) (f i))\<close>
    using assms unfolding llist_emb_def by blast

  let ?f = \<open>\<lambda>i. f i - 1\<close>

  have \<open>f 0 > 0\<close>
    using f(2) assms(2) unfolding llist_emb_def
    by (metis eSuc_ne_0 gr_zeroI llength_LCons lnth_0 zero_enat_def)
  then have \<open>\<forall>i j. i < j \<longrightarrow> ?f i < ?f j\<close>
    using f(1) by (metis diff_less_mono less_nat_zero_code less_one neq0_conv not_le_imp_less)
  moreover have \<open>\<forall>i. enat i < llength (LCons x xs) \<longrightarrow>
      enat (?f i) < llength ys \<and> P (lnth (LCons x xs) i) (lnth ys (?f i))\<close>
    using f \<open>0 < f 0\<close> by (metis Suc_diff_1 Suc_ile_eq iless_Suc_eq llength_LCons lnth_LCons'
        not_less0 not_less_iff_gr_or_eq)
  ultimately show ?thesis
    unfolding llist_emb_def by meson
qed

lemma llength_takeWhile:
  assumes \<open>i < llength (ltakeWhile P ys)\<close>
  shows \<open>P (lnth ys i)\<close>
  using assms by (metis in_lset_conv_lnth lset_ltakeWhileD ltakeWhile_nth)

lemma llist_emb_ldropWhile:
  assumes \<open>llist_emb P (LCons x xs) ys\<close>
  shows \<open>llist_emb P (LCons x xs) (ldropWhile (\<lambda>y. \<not> P x y) ys)\<close> (is \<open>llist_emb P ?xs ?ys\<close>)
proof -
  obtain f where f:
    \<open>\<forall>i j. i < j \<longrightarrow> f i < f j\<close>
    \<open>\<forall>i. enat i < llength ?xs \<longrightarrow> enat (f i) < llength ys \<and> P (lnth ?xs i) (lnth ys (f i))\<close>
    using assms unfolding llist_emb_def by blast

  obtain n where n: \<open>enat n = llength (ltakeWhile (\<lambda>y. \<not> P x y) ys)\<close>
    using f(2) by (metis f(2) in_lset_conv_lnth lfinite_llength_enat
        llength_ltakeWhile_eq_infinity lset_intros(1) lset_ltakeWhileD ltakeWhile_K_True)

  have \<open>P x (lnth ys (f 0))\<close>
    using f(2) by (metis eSuc_ne_0 gr_zeroI llength_LCons lnth_0 zero_enat_def)
  then have fi: \<open>\<forall>i. n \<le> f i\<close>
    using n f(1) by (metis enat_ord_simps(2) le_zero_eq llength_takeWhile nat_less_le
        not_le_imp_less order_trans)

  let ?f = \<open>\<lambda>i. f i - n\<close>

  have \<open>\<forall>i j. i < j \<longrightarrow> ?f i < ?f j\<close>
    using f(1) fi using diff_less_mono by presburger
  moreover have \<open>P x (lnth ?ys (?f 0))\<close>
    using \<open>P x (lnth ys (f 0))\<close> fi n
    by (metis lappend_ltakeWhile_ldropWhile lnth_lappend2)
  have \<open>\<forall>i. enat i < llength ?xs \<longrightarrow>
      enat (?f i) < llength ?ys \<and> P (lnth ?xs i) (lnth ?ys (?f i))\<close>
    using f(2) fi n
    by (metis lappend_ltakeWhile_ldropWhile ldropn_Suc_conv_ldropn ldropn_eq_LConsD ldropn_lappend2
        lnth_lappend2 of_nat_eq_enat of_nat_le_iff the_enat.simps)
  ultimately show ?thesis
    unfolding llist_emb_def by meson
qed

lemma llist_emb_ConsD:
  assumes "llist_emb P (LCons x xs) ys"
  shows "\<exists>us v vs. ys = lappend us (LCons v vs) \<and> P x v \<and> llist_emb P xs vs"
proof -
  obtain f where f:
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
      by (metis LCons assms llist_emb_tail2 llist_emb_ldropWhile)
    ultimately show ?thesis
      by blast
  qed
qed

lemma llist_emb_appendD:
  assumes "llist_emb P (lappend xs ys) zs" "lfinite xs"
  shows "\<exists>us vs. zs = lappend us vs \<and> llist_emb P xs us \<and> llist_emb P ys vs"
proof -
  obtain f where f:
    \<open>\<forall>i j. i < j \<longrightarrow> f i < f j\<close>
    \<open>\<forall>i. enat i < llength (lappend xs ys) \<longrightarrow>
      enat (f i) < llength zs \<and> P (lnth (lappend xs ys) i) (lnth zs (f i))\<close>
    using assms unfolding llist_emb_def by blast

  have xs_ys: \<open>llength (lappend xs ys) = llength xs + llength ys\<close>
    by simp

  obtain nxs where nxs: \<open>llength xs = enat nxs\<close>
    using \<open>lfinite xs\<close> lfinite_llength_enat by blast

  let ?n = \<open>f nxs\<close>

  let ?us = \<open>ltake ?n zs\<close>
  let ?vs = \<open>ldrop ?n zs\<close>

  have us_vs: \<open>lappend ?us ?vs = zs\<close>
    by (simp add: lappend_ltake_ldrop)

  have \<open>\<forall>i. enat i < llength xs \<longrightarrow> enat (f i) < llength zs \<and> P (lnth xs i) (lnth zs (f i))\<close>
    using f(2) using nxs xs_ys by (metis enat_less_enat_plusI enat_ord_simps(2) lnth_lappend1)
  moreover have \<open>\<forall>i. enat i < llength xs \<longrightarrow> f i < ?n\<close>
    using f(1) nxs by simp
  ultimately have \<open>\<forall>i. enat i < llength xs \<longrightarrow>
      enat (f i) < llength ?us \<and> P (lnth xs i) (lnth ?us (f i))\<close>
    by (simp add: lnth_ltake)
  then have xs: \<open>llist_emb P xs ?us\<close>
    using f(1) unfolding llist_emb_def by blast

  let ?f = \<open>\<lambda>i. f (nxs + i) - ?n\<close>

  have \<open>\<forall>i. enat i < llength ys \<longrightarrow> enat (?f i) < llength ?vs \<and> P (lnth ys i) (lnth ?vs (?f i))\<close>
    using f nxs xs_ys us_vs by (smt (verit, ccfv_SIG) add_diff_cancel_left' antisym_conv2
        dual_order.strict_implies_order enat_le_plus_same(1) enat_less_enat_plusI2
        enat_llength_ldropn ldrop_enat le_add1 le_add_diff_inverse2 llength_lappend llength_ltake
        lnth_lappend2 min_def not_le plus_enat_simps(1))
  moreover have \<open>\<forall>i j. i < j \<longrightarrow> ?f i < ?f j\<close>
    using f(1) by (metis add.right_neutral diff_less_mono dual_order.strict_implies_order
        less_nat_zero_code nat_add_left_cancel_less nat_neq_iff not_le)
  ultimately have ys: \<open>llist_emb P ys ?vs\<close>
    unfolding llist_emb_def by meson

  from xs ys us_vs show ?thesis
    by metis
qed

lemma llist_emb_length:
  assumes "llist_emb P xs ys"
  shows "llength xs \<le> llength ys"
  using assms unfolding llist_emb_def
  by (metis add.commute add.right_neutral add_leE enat_ord_code(3) enat_ord_simps(2)
      length_list_of llength_eq_infty_conv_lfinite mono_nat_linear_lb not_le not_le_imp_less)

lemma llist_emb_set:
  assumes "llist_emb P xs ys" and "x \<in> lset xs"
  obtains y where "y \<in> lset ys" and "P x y"
  using assms unfolding llist_emb_def by (metis in_lset_conv_lnth)

lemma llist_emb_Cons_iff1 [simp]:
  assumes "P x y"
  shows "llist_emb P (LCons x xs) (LCons y ys) \<longleftrightarrow> llist_emb P xs ys"
  using assms by (meson llist_emb_LCons llist_emb_tail2)

lemma llist_emb_Cons_iff2 [simp]:
  assumes "\<not> P x y"
  shows "llist_emb P (LCons x xs) (LCons y ys) \<longleftrightarrow> llist_emb P (LCons x xs) ys"
  using assms by (metis lappend_code(1-2) lfinite.simps llist_emb_LCons_False llist_emb_append2)

lemma llist_emb_lfinite:
  assumes \<open>llist_emb P xs ys\<close> \<open>lfinite ys\<close>
  shows \<open>lfinite xs\<close>
  using assms llist_emb_length by (metis enat_ile lfinite_conv_llength_enat)

lemma llist_emb_ldrop:
  fixes i :: nat
  assumes \<open>llist_emb P xs ys\<close>
  shows \<open>llist_emb P (ldrop i xs) (ldrop i ys)\<close>
proof -
  obtain f where f:
    \<open>\<forall>i j. i < j \<longrightarrow> f i < f j\<close>
    \<open>\<forall>i. enat i < llength xs \<longrightarrow> enat (f i) < llength ys \<and> P (lnth xs i) (lnth ys (f i))\<close>
    using assms unfolding llist_emb_def by blast

  let ?f = \<open>\<lambda>j. f (j + i) - i\<close>

  have \<open>\<forall>i j. i < j \<longrightarrow> ?f i < ?f j\<close>
    using f(1)
    by (metis add_diff_cancel_right' add_leE diff_less_mono less_diff_conv mono_nat_linear_lb)
  moreover have \<open>\<forall>j. enat j < llength (ldrop i xs) \<longrightarrow>
      enat (?f j) < llength (ldrop i ys) \<and> P (lnth (ldrop i xs) j) (lnth (ldrop i ys) (?f j))\<close>
    using f by (smt (verit, best) add.commute add_leE ldrop_enat ldropn_Suc_conv_ldropn
        ldropn_eq_LConsD ldropn_ldropn le_add_diff_inverse lnth_ldropn mono_nat_linear_lb)
  ultimately show ?thesis
    unfolding llist_emb_def by meson
qed

subsection \<open>Intersection from a point and onwards\<close>

definition Inter_from :: \<open>'a set llist \<Rightarrow> nat \<Rightarrow> 'a set\<close> where
  \<open>Inter_from xs i \<equiv> \<Inter>j \<in> {j. i \<le> j \<and> enat j < llength xs}. lnth xs j\<close>

lemma Inter_from_0: \<open>Inter_from xs 0 = \<Inter>(lset xs)\<close>
  unfolding Inter_from_def by (smt (verit, best) Collect_cong INT_iff Inf_set_def Inter_iff
      in_lset_conv_lnth le0 mem_Collect_eq)

lemma Inter_from_llength:
  assumes \<open>llength xs \<le> i\<close>
  shows \<open>Inter_from xs i = UNIV\<close>
  unfolding Inter_from_def using assms
  using enat_ord_simps(1) image_is_empty order_subst1 by fastforce

lemma Inter_from_Suc:
  assumes \<open>enat i < llength xs\<close>
  shows \<open>Inter_from xs i = lnth xs i \<inter> Inter_from xs (Suc i)\<close>
proof -
  have \<open>Inter_from xs i = \<Inter>(lnth xs ` {j. i \<le> j \<and> enat j < llength xs})\<close>
    unfolding Inter_from_def by blast
  also have \<open>\<dots> = \<Inter>(lnth xs ` ({i} \<union> {j. Suc i \<le> j \<and> enat j < llength xs}))\<close>
    using assms by fastforce
  also have \<open>\<dots> = lnth xs i \<inter> \<Inter>(lnth xs ` {j. Suc i \<le> j \<and> enat j < llength xs})\<close>
    by simp
  finally show ?thesis
    unfolding Inter_from_def .
qed

lemma Inter_from_ldrop:
  assumes \<open>enat i < llength xs\<close>
  shows \<open>Inter_from xs (i + j) = Inter_from (ldrop i xs) j\<close>
proof (cases \<open>llength xs\<close>)
  case (enat n)
  have \<open>{k. i + j \<le> k \<and> k < n} = {i+j..<n}\<close>
    by auto
  also have \<open>\<dots> = (\<lambda>k. i + k) ` {j..<n-i}\<close>
    by auto
  also have \<open>\<dots> = (\<lambda>k. i + k) ` {k. j \<le> k \<and> k < n - i}\<close>
    by fastforce
  finally have *: \<open>{k. i + j \<le> k \<and> k < n} = (\<lambda>k. i + k) ` {k. j \<le> k \<and> k < n - i}\<close> .

  have \<open>Inter_from xs (i + j) = \<Inter>(lnth xs ` {k. i + j \<le> k \<and> k < n})\<close>
    unfolding Inter_from_def using enat by simp
  also have \<open>\<dots> = \<Inter>((\<lambda>k. lnth xs (i + k)) ` {k. j \<le> k \<and> k < n - i})\<close>
    using * by simp
  also have \<open>\<dots> = \<Inter>((\<lambda>k. lnth (ldrop i xs) k) ` {k. j \<le> k \<and> k < n - i})\<close>
    using lnth_ldrop' assms by fast
  also have \<open>\<dots> = \<Inter>((\<lambda>k. lnth (ldrop i xs) k) ` {k. j \<le> k \<and> k < llength (ldrop i xs)})\<close>
    using enat by (simp add: ldrop_enat)
  also have \<open>\<dots> = Inter_from (ldrop i xs) j\<close>
    unfolding Inter_from_def by blast
  finally show ?thesis .
next
  case infinity
    (* TODO: can we unify these two cases? *)
  have \<open>{k. i + j \<le> k \<and> k < \<infinity>} = {i+j..}\<close>
    by auto
  also have \<open>\<dots> = (\<lambda>k. i + k) ` {j..}\<close>
    by auto
  also have \<open>\<dots> = (\<lambda>k. i + k) ` {k. j \<le> k \<and> k < \<infinity>}\<close>
    by fastforce
  finally have *: \<open>{k. i + j \<le> k \<and> k < \<infinity>} = (\<lambda>k. i + k) ` {k. j \<le> k \<and> k < \<infinity>}\<close> .

  have \<open>Inter_from xs (i + j) = \<Inter>(lnth xs ` {k. i + j \<le> k \<and> k < \<infinity>})\<close>
    unfolding Inter_from_def using infinity by simp
  also have \<open>\<dots> = \<Inter>((\<lambda>k. lnth xs (i + k)) ` {k. j \<le> k \<and> k < \<infinity>})\<close>
    using * by simp
  also have \<open>\<dots> = \<Inter>((\<lambda>k. lnth (ldrop i xs) k) ` {k. j \<le> k \<and> k < \<infinity>})\<close>
    using lnth_ldrop' assms by fast
  also have \<open>\<dots> = \<Inter>((\<lambda>k. lnth (ldrop i xs) k) ` {k. j \<le> k \<and> k < llength (ldrop i xs)})\<close>
    using infinity by (simp add: ldrop_enat)
  also have \<open>\<dots> = Inter_from (ldrop i xs) j\<close>
    unfolding Inter_from_def by blast
  finally show ?thesis .
qed

lemma Inter_from_lset: \<open>Inter_from xs i = \<Inter>(lset (ldrop i xs))\<close>
  using Inter_from_0 Inter_from_ldrop Inter_from_llength
  by (metis add.right_neutral ldrop_0 ldrop_eq_LNil not_le zero_enat_def)

subsection \<open>Union from a point and onwards\<close>

definition Union_from :: \<open>'a set llist \<Rightarrow> nat \<Rightarrow> 'a set\<close> where
  \<open>Union_from xs i \<equiv> \<Union>j \<in> {j. i \<le> j \<and> enat j < llength xs}. lnth xs j\<close>

lemma Union_from_0: \<open>Union_from xs 0 = \<Union>(lset xs)\<close>
  unfolding Union_from_def by (smt (verit, ccfv_threshold) SUP_eqI Sup_least Sup_upper
      bot_nat_0.extremum in_lset_conv_lnth mem_Collect_eq)

lemma Union_from_llength:
  assumes \<open>llength xs \<le> i\<close>
  shows \<open>Union_from xs i = {}\<close>
  unfolding Union_from_def using assms
  using enat_ord_simps(1) image_is_empty order_subst1 by fastforce

lemma Union_from_Suc:
  assumes \<open>enat i < llength xs\<close>
  shows \<open>Union_from xs i = lnth xs i \<union> Union_from xs (Suc i)\<close>
proof -
  have *: \<open>{j. i \<le> j \<and> enat j < llength xs} = {i} \<union> {j. Suc i \<le> j \<and> enat j < llength xs}\<close>
    using assms by auto

  have \<open>Union_from xs i = \<Union>(lnth xs ` {j. i \<le> j \<and> enat j < llength xs})\<close>
    unfolding Union_from_def by blast
  also have \<open>\<dots> = \<Union>(lnth xs ` ({i} \<union> {j. Suc i \<le> j \<and> enat j < llength xs}))\<close>
    using * by simp
  also have \<open>\<dots> = lnth xs i \<union> \<Union>(lnth xs ` {j. Suc i \<le> j \<and> enat j < llength xs})\<close>
    by simp
  finally show ?thesis
    unfolding Union_from_def .
qed

lemma Union_from_ldrop:
  assumes \<open>enat i < llength xs\<close>
  shows \<open>Union_from xs (i + j) = Union_from (ldrop i xs) j\<close>
    (* TODO: this proof is exactly Inter_from_ldrop but with \<Union> instead of \<Inter> *)
proof (cases \<open>llength xs\<close>)
  case (enat n)
  have \<open>{k. i + j \<le> k \<and> k < n} = {i+j..<n}\<close>
    by auto
  also have \<open>\<dots> = (\<lambda>k. i + k) ` {j..<n-i}\<close>
    by auto
  also have \<open>\<dots> = (\<lambda>k. i + k) ` {k. j \<le> k \<and> k < n - i}\<close>
    by fastforce
  finally have *: \<open>{k. i + j \<le> k \<and> k < n} = (\<lambda>k. i + k) ` {k. j \<le> k \<and> k < n - i}\<close> .

  have \<open>Union_from xs (i + j) = \<Union>(lnth xs ` {k. i + j \<le> k \<and> k < n})\<close>
    unfolding Union_from_def using enat by simp
  also have \<open>\<dots> = \<Union>((\<lambda>k. lnth xs (i + k)) ` {k. j \<le> k \<and> k < n - i})\<close>
    using * by simp
  also have \<open>\<dots> = \<Union>((\<lambda>k. lnth (ldrop i xs) k) ` {k. j \<le> k \<and> k < n - i})\<close>
    using lnth_ldrop' assms by fast
  also have \<open>\<dots> = \<Union>((\<lambda>k. lnth (ldrop i xs) k) ` {k. j \<le> k \<and> k < llength (ldrop i xs)})\<close>
    using enat by (simp add: ldrop_enat)
  also have \<open>\<dots> = Union_from (ldrop i xs) j\<close>
    unfolding Union_from_def by blast
  finally show ?thesis .
next
  case infinity
  have \<open>{k. i + j \<le> k \<and> k < \<infinity>} = {i+j..}\<close>
    by auto
  also have \<open>\<dots> = (\<lambda>k. i + k) ` {j..}\<close>
    by auto
  also have \<open>\<dots> = (\<lambda>k. i + k) ` {k. j \<le> k \<and> k < \<infinity>}\<close>
    by fastforce
  finally have *: \<open>{k. i + j \<le> k \<and> k < \<infinity>} = (\<lambda>k. i + k) ` {k. j \<le> k \<and> k < \<infinity>}\<close> .

  have \<open>Union_from xs (i + j) = \<Union>(lnth xs ` {k. i + j \<le> k \<and> k < \<infinity>})\<close>
    unfolding Union_from_def using infinity by simp
  also have \<open>\<dots> = \<Union>((\<lambda>k. lnth xs (i + k)) ` {k. j \<le> k \<and> k < \<infinity>})\<close>
    using * by simp
  also have \<open>\<dots> = \<Union>((\<lambda>k. lnth (ldrop i xs) k) ` {k. j \<le> k \<and> k < \<infinity>})\<close>
    using lnth_ldrop' assms by fast
  also have \<open>\<dots> = \<Union>((\<lambda>k. lnth (ldrop i xs) k) ` {k. j \<le> k \<and> k < llength (ldrop i xs)})\<close>
    using infinity by (simp add: ldrop_enat)
  also have \<open>\<dots> = Union_from (ldrop i xs) j\<close>
    unfolding Union_from_def by blast
  finally show ?thesis .
qed

lemma Union_from_lset: \<open>Union_from xs i = \<Union>(lset (ldrop i xs))\<close>
  using Union_from_0 Union_from_ldrop Union_from_llength
  by (metis add.right_neutral ldrop_0 ldrop_eq_LNil not_le zero_enat_def)

subsection \<open>Subsequences\<close>

abbreviation lsubseq :: "'a llist \<Rightarrow> 'a llist \<Rightarrow> bool"
  where "lsubseq xs ys \<equiv> llist_emb (=) xs ys"

lemma lsubseq_lset:
  assumes \<open>lsubseq xs ys\<close>
  shows \<open>lset xs \<subseteq> lset ys\<close>
  using assms unfolding llist_emb_def
  by (metis in_lset_conv_lnth subsetI)

lemma lsubseq_Inter_from:
  assumes \<open>lsubseq xs ys\<close>
  shows \<open>Inter_from ys i \<subseteq> Inter_from xs i\<close>
  using assms by (simp add: Inter_from_lset llist_emb_ldrop Inter_anti_mono lsubseq_lset)

(* "It is obvious by definition that the limit inferior of
    a subsequence must be a superset of the limit inferior of the original sequence"

  This means that a "subsequence" as used in the report must be infinite by definition.
*)

lemma lsubseq_Liminf:
  assumes \<open>lsubseq xs ys\<close> \<open>\<not> lfinite xs\<close>
  shows \<open>Liminf_llist ys \<subseteq> Liminf_llist xs\<close>
  using assms
proof -
  have \<open>\<forall>i. enat i < llength ys \<longrightarrow> (\<exists>j. j < llength xs \<and> Inter_from ys i \<subseteq> Inter_from xs j)\<close>
    using assms lsubseq_Inter_from by (metis enat_ord_code(4) llength_eq_infty_conv_lfinite)
  moreover have \<open>Liminf_llist ys = (\<Union>i \<in> {i. enat i < llength ys}. Inter_from ys i)\<close>
    unfolding Liminf_llist_def Inter_from_def by blast
  moreover have \<open>Liminf_llist xs = (\<Union>i \<in> {i. enat i < llength xs}. Inter_from xs i)\<close>
    unfolding Liminf_llist_def Inter_from_def by blast
  ultimately show ?thesis
    unfolding Liminf_llist_def Inter_from_def by fastforce
qed

lemma lsubseq_Union_from:
  assumes \<open>lsubseq xs ys\<close>
  shows \<open>Union_from xs i \<subseteq> Union_from ys i\<close>
  using assms by (simp add: Union_from_lset llist_emb_ldrop Union_mono lsubseq_lset)

lemma lsubseq_Limsup:
  assumes \<open>lsubseq xs ys\<close> \<open>\<not> lfinite xs\<close>
  shows \<open>Limsup_llist xs \<subseteq> Limsup_llist ys\<close>
  using assms
proof -
  have \<open>\<forall>i. enat i < llength ys \<longrightarrow> (\<exists>j. j < llength xs \<and> Union_from xs j \<subseteq> Union_from ys i)\<close>
    using assms lsubseq_Union_from by (metis enat_ord_code(4) llength_eq_infty_conv_lfinite)
  moreover have \<open>Limsup_llist xs = (\<Inter>i \<in> {i. enat i < llength xs}. Union_from xs i)\<close>
    unfolding Limsup_llist_def Union_from_def by blast
  moreover have \<open>Limsup_llist ys = (\<Inter>i \<in> {i. enat i < llength ys}. Union_from ys i)\<close>
    unfolding Limsup_llist_def Union_from_def by blast
  ultimately show ?thesis
    unfolding Limsup_llist_def Union_from_def
    by (smt (z3) le_INF_iff mem_Collect_eq order_refl order_trans)
qed

subsection \<open>Limit Points\<close>

definition limit_point :: \<open>'a set \<Rightarrow> 'a set llist \<Rightarrow> bool\<close> where
  \<open>limit_point X Xs \<equiv> \<exists>Xs'.
    lsubseq Xs' Xs \<and> \<not> lfinite Xs' \<and>
    X = Limsup_llist Xs' \<and> X = Liminf_llist Xs'\<close>


(* Splitting report Lemma 31 *)
lemma limit_point_bounds:
  assumes \<open>limit_point X Xs\<close> \<open>\<not> lfinite Xs\<close>
  shows \<open>Liminf_llist Xs \<subseteq> X\<close> \<open>X \<subseteq> Limsup_llist Xs\<close>
  using assms unfolding limit_point_def
  using lsubseq_Liminf lsubseq_Limsup by blast+

end