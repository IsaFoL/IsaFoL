(*  Title:       Limsup of Lazy Lists
    Author:      Asta Halkjær From <ahfrom at dtu.dk>, 2021

    Modelled on Ordered_Resolution_Prover.Lazy_List_Liminf
*)

section \<open>Limsup of Lazy Lists\<close>

theory Lazy_List_Limsup
  imports Coinductive.Coinductive_List
begin

subsection \<open>Library\<close>

(* TODO: import this from Ordered_Resolution_Prover.Lazy_List_Liminf? *)
lemma less_llength_ltake: "i < llength (ltake k Xs) \<longleftrightarrow> i < k \<and> i < llength Xs"
  by simp

subsection \<open>Infimum\<close>

definition Inf_llist :: \<open>'a set llist \<Rightarrow> 'a set\<close> where
  \<open>Inf_llist Xs = (\<Inter>i \<in> {i. enat i < llength Xs}. lnth Xs i)\<close>

lemma Inf_llist_subset_lnth: \<open>enat i < llength Xs \<Longrightarrow> Inf_llist Xs \<subseteq> lnth Xs i\<close>
  unfolding Inf_llist_def by fast

lemma Inf_llist_imp_exists_index:
  assumes \<open>\<not> lnull Xs\<close>
  shows \<open>x \<in> Inf_llist Xs \<Longrightarrow> \<exists>i. enat i < llength Xs \<and> x \<in> lnth Xs i\<close>
  unfolding Inf_llist_def using assms
  by (metis INT_E i0_less llength_eq_0 mem_Collect_eq zero_enat_def)

lemma Inf_llist_imp_all_index: \<open>x \<in> Inf_llist Xs \<Longrightarrow> \<forall>i. enat i < llength Xs \<longrightarrow> x \<in> lnth Xs i\<close>
  unfolding Inf_llist_def by blast

lemma all_index_imp_Inf_llist: \<open>\<forall>i. enat i < llength Xs \<longrightarrow> x \<in> lnth Xs i \<Longrightarrow> x \<in> Inf_llist Xs\<close>
  unfolding Inf_llist_def by auto

lemma Inf_llist_LNil[simp]: \<open>Inf_llist LNil = UNIV\<close>
  unfolding Inf_llist_def by auto

lemma Inf_llist_LCons[simp]: \<open>Inf_llist (LCons X Xs) = X \<inter> Inf_llist Xs\<close>
  unfolding Inf_llist_def
proof (intro subset_antisym subsetI)
  fix x
  assume \<open>x \<in> (\<Inter>i \<in> {i. enat i < llength (LCons X Xs)}. lnth (LCons X Xs) i)\<close>
  then have \<open>enat i < llength (LCons X Xs) \<longrightarrow> x \<in> lnth (LCons X Xs) i\<close> for i
    by blast
  then have \<open>x \<in> X \<and> (\<forall>i. enat i < llength Xs \<longrightarrow> x \<in> lnth Xs i)\<close>
    by (metis Suc_ile_eq iless_Suc_eq llength_LCons lnth_0 lnth_Suc_LCons zero_enat_def zero_le)
  then show \<open>x \<in> X \<inter> (\<Inter>i \<in> {i. enat i < llength Xs}. lnth Xs i)\<close>
    by blast
next
  fix x
  assume \<open>x \<in> X \<inter> \<Inter> (lnth Xs ` {i. enat i < llength Xs})\<close>
  then have \<open>x \<in> X \<and> (\<forall>i. enat i < llength Xs \<longrightarrow> x \<in> lnth Xs i)\<close>
    by simp
  then have \<open>\<forall>i. enat i \<le> llength Xs \<longrightarrow> x \<in> lnth (LCons X Xs) i\<close>
    by (metis Suc_diff_1 Suc_ile_eq lnth_0 lnth_Suc_LCons neq0_conv)
  then show \<open>x \<in> \<Inter> (lnth (LCons X Xs) ` {i. enat i < llength (LCons X Xs)})\<close>
    by simp
qed

lemma lhd_subset_Inf_llist: \<open>\<not> lnull Xs \<Longrightarrow> Inf_llist Xs \<subseteq> lhd Xs\<close>
  by (cases Xs) simp_all

subsection \<open>Infimum up-to\<close>

definition Inf_upto_llist :: \<open>'a set llist \<Rightarrow> enat \<Rightarrow> 'a set\<close> where
  \<open>Inf_upto_llist Xs j = (\<Inter>i \<in> {i. enat i < llength Xs \<and> enat i \<le> j}. lnth Xs i)\<close>

lemma Inf_upto_llist_eq_Inf_llist_ltake: \<open>Inf_upto_llist Xs j = Inf_llist (ltake (eSuc j) Xs)\<close>
  unfolding Inf_upto_llist_def Inf_llist_def
  by (smt (verit, best) Collect_cong Sup.SUP_cong iless_Suc_eq less_llength_ltake lnth_ltake
      mem_Collect_eq)

lemma Inf_upto_llist_enat_0[simp]:
  \<open>Inf_upto_llist Xs (enat 0) = (if lnull Xs then UNIV else lhd Xs)\<close>
  unfolding Inf_upto_llist_def image_def
  by (cases \<open>lnull Xs\<close>) (auto simp: lhd_conv_lnth enat_0 enat_0_iff)

lemma Inf_upto_llist_Suc[simp]:
  \<open>Inf_upto_llist Xs (enat (Suc j)) =
   Inf_upto_llist Xs (enat j) \<inter> (if enat (Suc j) < llength Xs then lnth Xs (Suc j) else UNIV)\<close>
  unfolding Inf_upto_llist_def image_def by (auto intro: le_SucI elim: le_SucE)

lemma Inf_upto_llist_infinity[simp]: \<open>Inf_upto_llist Xs \<infinity> = Inf_llist Xs\<close>
  unfolding Inf_upto_llist_def Inf_llist_def by simp

lemma Inf_upto_llist_0[simp]: \<open>Inf_upto_llist Xs 0 = (if lnull Xs then UNIV else lhd Xs)\<close>
  unfolding zero_enat_def by (rule Inf_upto_llist_enat_0)

lemma Inf_upto_llist_eSuc[simp]:
  \<open>Inf_upto_llist Xs (eSuc j) =
   (case j of
      enat k \<Rightarrow> Inf_upto_llist Xs (enat (Suc k))
    | \<infinity> \<Rightarrow> Inf_llist Xs)\<close>
  by (auto simp: eSuc_enat split: enat.split)

lemma Inf_upto_llist_anti[simp]: \<open>j \<le> k \<Longrightarrow> Inf_upto_llist Xs k \<subseteq> Inf_upto_llist Xs j\<close>
  unfolding Inf_upto_llist_def by auto

lemma Inf_llist_subset_Inf_upto_llist: \<open>Inf_llist Xs \<subseteq> Inf_upto_llist Xs j\<close>
  unfolding Inf_llist_def Inf_upto_llist_def by auto

lemma elem_Inf_llist_imp_Inf_upto_llist:
  \<open>x \<in> Inf_llist Xs \<Longrightarrow> x \<in> Inf_upto_llist Xs (enat j)\<close>
  unfolding Inf_llist_def Inf_upto_llist_def by blast

lemma Inf_upto_llist_subset_lnth: \<open>j < llength Xs \<Longrightarrow> Inf_upto_llist Xs j \<subseteq> lnth Xs j\<close>
  unfolding Inf_upto_llist_def by auto

lemma Inf_llist_imp_Inf_upto_llist:
  assumes \<open>X \<subseteq> Inf_llist Xs\<close>
  shows \<open>X \<subseteq> Inf_upto_llist Xs (enat k)\<close>
  using assms elem_Inf_llist_imp_Inf_upto_llist by fast

subsection \<open>Limsup\<close>

definition Limsup_llist :: \<open>'a set llist \<Rightarrow> 'a set\<close> where
  \<open>Limsup_llist Xs =
   (\<Inter>i \<in> {i. enat i < llength Xs}. \<Union>j \<in> {j. i \<le> j \<and> enat j < llength Xs}. lnth Xs j)\<close>

lemma Limsup_llist_LNil[simp]: \<open>Limsup_llist LNil = UNIV\<close>
  unfolding Limsup_llist_def by simp

lemma Limsup_llist_LCons:
  \<open>Limsup_llist (LCons X Xs) = (if lnull Xs then X else Limsup_llist Xs)\<close> (is \<open>?lhs = ?rhs\<close>)
proof (cases "lnull Xs")
  case nnull: False
  show ?thesis
  proof
    {
      fix x
      assume \<open>\<forall>i. enat i \<le> llength Xs \<longrightarrow> (\<exists>j \<ge> i. enat j \<le> llength Xs \<and> x \<in> lnth (LCons X Xs) j)\<close>
      then have \<open>\<forall>i. enat i < llength Xs \<longrightarrow> (\<exists>j \<ge> i. enat j < llength Xs \<and> x \<in> lnth Xs j)\<close>
        by (metis Suc_ile_eq Suc_le_D Suc_le_mono lnth_Suc_LCons)
    }
    then show \<open>?lhs \<subseteq> ?rhs\<close>
      by (auto simp: Limsup_llist_def nnull)

    {
      fix x
      assume \<open>\<forall>i. enat i < llength Xs \<longrightarrow> (\<exists>j \<ge> i. enat j < llength Xs \<and> x \<in> lnth Xs j)\<close>
      then have \<open>\<forall>i. enat i \<le> llength Xs \<longrightarrow>
          (\<exists>j \<ge> i. enat j \<le> llength Xs \<and> x \<in> lnth (LCons X Xs) j)\<close>
        by (metis Suc_ile_eq Suc_le_D iless_Suc_eq llength_LCons lnth_Suc_LCons nat_le_linear
            nnull not_less_eq_eq not_lnull_conv zero_enat_def zero_le)
    }
    then show "?rhs \<subseteq> ?lhs"
      by (auto simp: Limsup_llist_def nnull)
  qed
qed (simp add: Limsup_llist_def enat_0_iff(1))

lemma lfinite_Limsup_llist: \<open>lfinite Xs \<Longrightarrow> Limsup_llist Xs = (if lnull Xs then UNIV else llast Xs)\<close>
proof (induction rule: lfinite_induct)
  case (LCons xs)
  then obtain y ys where xs: \<open>xs = LCons y ys\<close>
    by (meson not_lnull_conv)
  show ?case
    unfolding xs by (simp add: Limsup_llist_LCons LCons.IH[unfolded xs, simplified] llast_LCons)
qed (simp add: Limsup_llist_def)

lemma Limsup_llist_ltl: \<open>\<not> lnull (ltl Xs) \<Longrightarrow> Limsup_llist Xs = Limsup_llist (ltl Xs)\<close>
  by (metis Limsup_llist_LCons lhd_LCons_ltl lnull_ltlI)

lemma Inf_llist_subset_Limsup_llist: \<open>Inf_llist Xs \<subseteq> Limsup_llist Xs\<close>
  unfolding Limsup_llist_def Inf_llist_def by fast

lemma image_Limsup_llist_subset: \<open>f ` Limsup_llist Ns \<subseteq> Limsup_llist (lmap ((`) f) Ns)\<close>
  unfolding Limsup_llist_def by fastforce

lemma Limsup_llist_imp_exists_index:
  assumes \<open>\<not> lnull Xs\<close>
  shows \<open>x \<in> Limsup_llist Xs \<Longrightarrow> \<exists>i. enat i < llength Xs \<and> x \<in> lnth Xs i\<close>
  unfolding Limsup_llist_def using assms
  by simp (metis i0_less llength_eq_0 zero_enat_def)

(*
  For Liminf, the lemma below shows:
    \<open>\<exists>i. enat i < llength Xs \<and> X \<subseteq> (\<Inter>j \<in> {j. i \<le> j \<and> enat j < llength Xs}. lnth Xs j)\<close>
 
  This does not hold for Limsup. Take:

  Xs = {1, 2}, {2, 3}, {1, 2}, {2, 3}, ...

  The unions are: {1, 2, 3}, {1, 2, 3}, ...
  So the Limsup is: {1, 2, 3}

  No matter what i we pick, the intersection of the remaining sequence is going to be {2}.
  So if we pick, say, X = {1, 2, 3}, then the lemma does not hold.

  I don't know how it should look for Limsup.
  Below is a version where \<exists> \<rightarrow> \<forall> and \<Inter> \<rightarrow> \<Union>.
*)
 
lemma finite_subset_Limsup_llist_imp_exists_index:
  assumes
    nnil: \<open>\<not> lnull Xs\<close> and
    fin: \<open>finite X\<close> and
    in_sup: \<open>X \<subseteq> Limsup_llist Xs\<close>
  shows \<open>\<forall>i. enat i < llength Xs \<longrightarrow> X \<subseteq> (\<Union>j \<in> {j. i \<le> j \<and> enat j < llength Xs}. lnth Xs j)\<close>
  using assms unfolding Limsup_llist_def by blast

lemma Limsup_llist_lmap_image:
  (* The f_inj assumption isn't strong enough since Inf is a subset of the Limsup,
      not the other way around as for Sup and Liminf.
     I'm not sure what shape this lemma should have. *)
  assumes f_inj: \<open>inj_on f (Inf_llist (lmap g xs))\<close>
  shows \<open>Limsup_llist (lmap (\<lambda>x. f ` g x) xs) = f ` Limsup_llist (lmap g xs)\<close> (is \<open>?lhs = ?rhs\<close>)
  oops

lemma Limsup_llist_lmap_union:
  assumes \<open>\<forall>x \<in> lset xs. \<forall>y \<in> lset xs. g x \<inter> h y = {}\<close>
  shows \<open>Limsup_llist (lmap (\<lambda>x. g x \<union> h x) xs) =
    Limsup_llist (lmap g xs) \<union> Limsup_llist (lmap h xs)\<close> (is \<open>?lhs = ?rhs\<close>)
proof (intro equalityI subsetI)
  fix x
  assume x_in: \<open>x \<in> ?lhs\<close>
  then have \<open>\<forall>i. enat i < llength xs \<longrightarrow> (\<exists>j \<ge> i. enat j < llength xs \<and>
      (x \<in> g (lnth xs j) \<or> x \<in> h (lnth xs j)))\<close>
    unfolding Limsup_llist_def by auto
  then have \<open>(\<forall>i'. enat i' < llength xs \<longrightarrow> (\<exists>j \<ge> i'. enat j < llength xs \<and> x \<in> g (lnth xs j)))
     \<or> (\<forall>i'. enat i' < llength xs \<longrightarrow> (\<exists>j \<ge> i'. enat j < llength xs \<and> x \<in> h (lnth xs j)))\<close>
    using assms[unfolded disjoint_iff_not_equal] by (metis in_lset_conv_lnth)
  then show \<open>x \<in> ?rhs\<close>
    unfolding Limsup_llist_def by simp
next
  fix x
  show \<open>x \<in> ?rhs \<Longrightarrow> x \<in> ?lhs\<close>
    using assms unfolding Limsup_llist_def by auto
qed

lemma Limsup_set_filter_commute:
  assumes \<open>\<not> lnull Xs\<close>
  shows \<open>Limsup_llist (lmap (\<lambda>X. {x \<in> X. p x}) Xs) = {x \<in> Limsup_llist Xs. p x}\<close> (is \<open>?lhs = ?rhs\<close>)
proof (intro equalityI subsetI)
  fix x
  assume \<open>x \<in> ?lhs\<close>
  then show \<open>x \<in> ?rhs\<close>
    unfolding Limsup_llist_def
    by simp (metis assms i0_less llength_eq_0 zero_enat_def)
qed (simp add: Limsup_llist_def)

subsection \<open>Limsup up-to\<close>

definition Limsup_upto_llist :: \<open>'a set llist \<Rightarrow> enat \<Rightarrow> 'a set\<close> where
  \<open>Limsup_upto_llist Xs k =
   (\<Inter>i \<in> {i. enat i < llength Xs \<and> enat i \<le> k}.
      \<Union>j \<in> {j. i \<le> j \<and> enat j < llength Xs \<and> enat j \<le> k}. lnth Xs j)\<close>

lemma Limsup_upto_llist_eq_Limsup_llist_ltake:
  \<open>Limsup_upto_llist Xs j = Limsup_llist (ltake (eSuc j) Xs)\<close>
  unfolding Limsup_upto_llist_def Limsup_llist_def
  by (smt Collect_cong Sup.SUP_cong iless_Suc_eq lnth_ltake less_llength_ltake mem_Collect_eq)

lemma Limsup_upto_llist_enat[simp]:
  \<open>Limsup_upto_llist Xs (enat k) =
   (if enat k < llength Xs then lnth Xs k else if lnull Xs then UNIV else llast Xs)\<close>
proof (cases \<open>enat k < llength Xs\<close>)
  case True
  then show ?thesis
    unfolding Limsup_upto_llist_def by force
next
  case k_ge: False
  show ?thesis
proof (cases \<open>lnull Xs\<close>)
  case nil: True
  then show ?thesis
    unfolding Limsup_upto_llist_def by simp
next
  case nnil: False
  then obtain j where
    j: \<open>eSuc (enat j) = llength Xs\<close>
    using k_ge by (metis eSuc_enat_iff enat_ile le_less_linear lhd_LCons_ltl llength_LCons)

  have fin: \<open>lfinite Xs\<close>
    using k_ge not_lfinite_llength by fastforce
  have le_k: \<open>enat i < llength Xs \<and> i \<le> k \<longleftrightarrow> enat i < llength Xs\<close> for i
    using k_ge linear order_le_less_subst2 by fastforce
  have \<open>Limsup_upto_llist Xs (enat k) = llast Xs\<close>
    using j nnil lfinite_Limsup_llist[OF fin] nnil
    unfolding Limsup_upto_llist_def Limsup_llist_def using llast_conv_lnth[OF j[symmetric]]
    by (simp add: le_k)
  then show ?thesis
    using k_ge nnil by simp
  qed
qed

lemma Limsup_upto_llist_infinity[simp]: \<open>Limsup_upto_llist Xs \<infinity> = Limsup_llist Xs\<close>
  unfolding Limsup_upto_llist_def Limsup_llist_def by simp

lemma Limsup_upto_llist_0[simp]:
  \<open>Limsup_upto_llist Xs 0 = (if lnull Xs then UNIV else lhd Xs)\<close>
  unfolding Limsup_upto_llist_def image_def
  by (simp add: enat_0[symmetric]) (simp add: enat_0 lnth_0_conv_lhd)

lemma Limsup_upto_llist_eSuc[simp]:
  \<open>Limsup_upto_llist Xs (eSuc j) =
   (case j of
      enat k \<Rightarrow> Limsup_upto_llist Xs (enat (Suc k))
    | \<infinity> \<Rightarrow> Limsup_llist Xs)\<close>
  by (auto simp: eSuc_enat split: enat.split)

lemma Liminf_upto_llist_imp_elem_Limsup_llist:
  assumes \<open>\<exists>i < llength Xs. \<forall>j \<ge> i. j < llength Xs \<longrightarrow> x \<in> Limsup_upto_llist Xs (enat j)\<close>
  shows \<open>x \<in> Limsup_llist Xs\<close>
  using assms by (simp add: Limsup_llist_def Limsup_upto_llist_def)
    (metis dual_order.strict_implies_order enat_iless enat_less_imp_le enat_ord_simps(1) not_less)

end