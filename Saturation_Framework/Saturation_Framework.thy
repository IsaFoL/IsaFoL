(*  Title:       Saturation Framework
    Author:      Sophie Tourret <stourret at mpi-inf.mpg.de>, 2018
*)

section \<open>Saturation Framework\<close>

theory Saturation_Framework
  imports Ordered_Resolution_Prover.Herbrand_Interpretation
    Ordered_Resolution_Prover.Lazy_List_Liminf
    Ordered_Resolution_Prover.Lazy_List_Chain
begin

text \<open>
TODO
\<close>

subsection \<open>Preliminaries\<close>

text \<open>
Inferences have one distinguished main premise, any number of side premises, and a conclusion.
\<close>

type_synonym 'f formulas = "'f set"

locale consequence_relation =
  fixes
    Bot_F :: "'f set" and
    entails :: "'f formulas \<Rightarrow> 'f formulas \<Rightarrow> bool" (infix "|=" 50)
  assumes
    bot_implies_all: "\<forall>B \<in> Bot_F. {B} |= N1" and
    subset_entailed: "N2 \<subseteq> N1 \<Longrightarrow> N1 |= N2" and
    all_formulas_entailed: "(\<forall>C \<in> N2. N1 |= {C}) \<Longrightarrow> N1 |= N2" and
    transitive_entails: "(N1 |= N2 \<and> N2 |= N3) \<Longrightarrow> N1 |= N3"
begin

lemma easy1: "(N1 |= N2) \<longleftrightarrow> (\<forall>C \<in> N2. N1 |= {C})"
by (meson all_formulas_entailed empty_subsetI insert_subset subset_entailed transitive_entails)

lemma easy2: "(N |= N1 \<and> N |= N2) \<longleftrightarrow> N |= (N1 \<union> N2)"
  apply (subst easy1)
  apply (subst (2) easy1)
  apply (subst (3) easy1)
  by auto

(*lemma easy3: \<open>\<forall>C \<in> N1. {C} |= N2 \<Longrightarrow> N1 |= N2\<close>
*)




end

datatype 'f inference =
  Infer (prems_of: "'f list") (concl_of: "'f ")

abbreviation concls_of :: "'f inference set \<Rightarrow> 'f set" where
  "concls_of \<iota> \<equiv> concl_of ` \<iota>"

locale inference_system = consequence_relation +
  fixes 
    I :: "'f inference set" and
    Red_I :: "'f formulas \<Rightarrow> 'f inference set" and
    Red_F :: "'f formulas \<Rightarrow> 'f formulas"
  assumes
    Red_I_to_I: "Red_I N \<in> Pow I" and
    Red_F_Bot_F: "B \<in> Bot_F \<Longrightarrow> N |= {B} \<Longrightarrow> N - Red_F N |= {B}" and
    Red_F_of_subset: "N \<subseteq> N' \<Longrightarrow> Red_F N \<subseteq> Red_F N'" and
    Red_I_of_subset: "N \<subseteq> N' \<Longrightarrow> Red_I N \<subseteq> Red_I N'" and
    Red_F_of_Red_F_subset: "N' \<subseteq> Red_F N \<Longrightarrow> Red_F N \<subseteq> Red_F (N - N')" and
    Red_I_of_Red_F_subset: "N' \<subseteq> Red_F N \<Longrightarrow> Red_I N \<subseteq> Red_I (N - N')" and
    Red_I_of_I_to_N: "\<iota> \<in> I \<and> concl_of \<iota> \<in> N \<Longrightarrow> \<iota> \<in> Red_I N" and
    same_with_other_syntax: "{\<iota> \<in> I. (concl_of \<iota> \<in> N)} \<subseteq> Red_I N"
begin

definition Inf :: "'f formulas  \<Rightarrow> 'f inference set" where
  "Inf N = {\<iota> \<in> I. set (prems_of \<iota>) \<subseteq> N}"


lemma red_concl_to_red_inf: 
  assumes 
    i: "\<iota> \<in> I" and
    concl: "concl_of \<iota> \<in> Red_F N"
  shows "\<iota> \<in> Red_I N"
proof -
  have i2: "\<iota> \<in> Red_I (Red_F N)" by (simp add: Red_I_of_I_to_N i concl)
  then have i3: "\<iota> \<in> Red_I (N \<union> Red_F N)" by (simp add: Red_I_of_I_to_N concl i)
  also have red_n_subs: "Red_F N \<subseteq> Red_F (N \<union> Red_F N)" by (simp add: Red_F_of_subset)
  then have "\<iota> \<in> Red_I ((N \<union> Red_F N) - (Red_F N - N))" using Red_I_of_Red_F_subset i3
    by (meson Diff_subset subsetCE subset_trans)
  then show ?thesis by (metis Diff_cancel Diff_subset Un_Diff Un_Diff_cancel contra_subsetD 
    inference_system.Red_I_of_subset inference_system_axioms sup_bot.right_neutral)
qed

inductive "derive" :: "'f formulas \<Rightarrow> 'f formulas \<Rightarrow> bool" (infix "\<turnstile>" 50) where
  unsat_preserving_derive: "(B \<in> Bot_F \<Longrightarrow> N |= {B} \<Longrightarrow> M |= {B}) \<Longrightarrow> M - N \<subseteq> Red_F N \<Longrightarrow> M \<turnstile> N"

definition saturated :: "'f formulas \<Rightarrow> bool" where 
  "saturated N \<equiv> Inf N \<subseteq> Red_I N"

definition Sup_Red_I_llist :: "'f formulas llist \<Rightarrow> 'f inference set" where
    "Sup_Red_I_llist D = (\<Union>i \<in> {i. enat i < llength D}. (Red_I (lnth D i)))"

lemma Sup_Red_I_unit: "Sup_Red_I_llist (LCons X LNil) = Red_I X" 
  using Sup_Red_I_llist_def enat_0_iff(1) by simp

definition fair :: "'f formulas llist \<Rightarrow> bool" where
  "fair D \<equiv> Inf (Liminf_llist D) \<subseteq> Sup_Red_I_llist D"

text \<open>TODO: replace in Lazy_List_Liminf\<close>
lemma (in-) elem_Sup_llist_imp_Sup_upto_llist': "x \<in> Sup_llist Xs \<Longrightarrow> \<exists>j < llength Xs. x \<in> Sup_upto_llist Xs j"
  unfolding Sup_llist_def Sup_upto_llist_def by blast 

lemma gt_Max_notin: \<open>finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> x > Max A \<Longrightarrow> x \<notin> A\<close> by auto

lemma equiv_Sup_Liminf:
  assumes 
    in_Sup: "C \<in> Sup_llist D" and
    not_in_Liminf: "C \<notin> Liminf_llist D"
  shows
    "\<exists> i \<in> {i. enat (Suc i) < llength D}. C \<in> (lnth D i) - (lnth D (Suc i))"
proof -
  obtain i where C_D_i: "C \<in> Sup_upto_llist D i" and "i < llength D" 
    using elem_Sup_llist_imp_Sup_upto_llist' in_Sup by fast
  then obtain j where j: "j \<ge> i \<and> enat j < llength D \<and> C \<notin> lnth D j" using not_in_Liminf   
    unfolding Sup_llist_def chain_def Liminf_llist_def by auto
  obtain k where k: "C \<in> (lnth D k)" "enat k < llength D" "k \<le> i" using C_D_i 
    unfolding Sup_upto_llist_def by auto
  let ?S = "{i. i < j \<and> i \<ge> k \<and> C \<in> (lnth D i)}"
  define l where "l \<equiv> Max ?S"
  have \<open>k \<in> {i. i < j \<and> k \<le> i \<and> C \<in> lnth D i}\<close> using k j by (auto simp: order.order_iff_strict)
  then have nempty: "{i. i < j \<and> k \<le> i \<and> C \<in> lnth D i} \<noteq> {}" by auto 
  then have l_prop: "l < j \<and> l \<ge> k \<and> C \<in> (lnth D l)" using Max_in[of ?S, OF _ nempty] unfolding l_def by auto 
  then have "C \<in> (lnth D l) - (lnth D (Suc l))" using j gt_Max_notin[OF _ nempty, of "Suc l"] 
    unfolding l_def[symmetric] by (auto intro: Suc_lessI)
  then show ?thesis apply (rule bexI[of _ l]) using l_prop j 
    apply auto 
    by (metis Suc_leI dual_order.order_iff_strict enat_ord_simps(2) less_trans)
qed

text \<open>lemma 2 in Uwe's notes\<close>
lemma Red_in_Sup: 
  assumes deriv: "chain (\<turnstile>) D"
  shows "Sup_llist D - Liminf_llist D \<subseteq> Red_F (Sup_llist D)"
proof
  fix C
  assume C_in_subset: "C \<in> Sup_llist D - Liminf_llist D"
  {
    fix C i
    assume 
      in_ith_elem: "C \<in> (lnth D i) - (lnth D (Suc i))" and
      i: "enat (Suc i) < llength D"
    have "(lnth D i) \<turnstile> (lnth D (Suc i))" using i deriv in_ith_elem chain_lnth_rel by auto
    then have "C \<in> Red_F (lnth D (Suc i))" using in_ith_elem derive.cases by blast
    then have "C \<in> Red_F (Sup_llist D)" using Red_F_of_subset 
      by (meson contra_subsetD i lnth_subset_Sup_llist)
  }
  then show "C \<in> Red_F (Sup_llist D)" using equiv_Sup_Liminf[of C] C_in_subset by fast
qed

text \<open>lemma 3 in Uwe's notes part 1/2\<close>
lemma Red_I_subset_Liminf: 
  assumes deriv: \<open>chain (\<turnstile>) D\<close> and
    i: \<open>enat i < llength D\<close>
  shows \<open>Red_I (lnth D i) \<subseteq> Red_I (Liminf_llist D)\<close>
proof -
  have Sup_in_diff: \<open>Red_I (Sup_llist D) \<subseteq> Red_I ((Sup_llist D) - ((Sup_llist D) - (Liminf_llist D)))\<close> 
    using Red_I_of_Red_F_subset[OF Red_in_Sup] deriv by auto
  also have \<open>(Sup_llist D) - ((Sup_llist D) - (Liminf_llist D)) = Liminf_llist D\<close> 
    by (simp add: Liminf_llist_subset_Sup_llist double_diff)
  then have Red_I_Sup_in_Liminf: \<open>Red_I (Sup_llist D) \<subseteq> Red_I (Liminf_llist D)\<close> using Sup_in_diff by auto
  have \<open>(lnth D i) \<subseteq> (Sup_llist D)\<close> unfolding Sup_llist_def using i by blast
  then have "Red_I (lnth D i) \<subseteq> Red_I (Sup_llist D)" using Red_I_of_subset 
    unfolding Sup_llist_def by auto 
  then show ?thesis using Red_I_Sup_in_Liminf by auto
qed

text \<open>lemma 3 in Uwe's notes part 2/2\<close>
lemma Red_F_subset_Liminf:
 assumes deriv: \<open>chain (\<turnstile>) D\<close> and
    i: \<open>enat i < llength D\<close>
  shows \<open>Red_F (lnth D i) \<subseteq> Red_F (Liminf_llist D)\<close>
proof -
  have Sup_in_diff: \<open>Red_F (Sup_llist D) \<subseteq> Red_F ((Sup_llist D) - ((Sup_llist D) - (Liminf_llist D)))\<close> 
    using Red_F_of_Red_F_subset[OF Red_in_Sup] deriv by auto
  also have \<open>(Sup_llist D) - ((Sup_llist D) - (Liminf_llist D)) = Liminf_llist D\<close> 
    by (simp add: Liminf_llist_subset_Sup_llist double_diff)
  then have Red_F_Sup_in_Liminf: \<open>Red_F (Sup_llist D) \<subseteq> Red_F (Liminf_llist D)\<close>
    using Sup_in_diff by auto
  have \<open>(lnth D i) \<subseteq> (Sup_llist D)\<close> unfolding Sup_llist_def using i by blast
  then have "Red_F (lnth D i) \<subseteq> Red_F (Sup_llist D)" using Red_F_of_subset 
    unfolding Sup_llist_def by auto 
  then show ?thesis using Red_F_Sup_in_Liminf by auto
qed

text \<open>lemma 4 in Uwe's notes\<close>
lemma i_in_Liminf_or_Red_F:
  assumes 
    deriv: \<open>chain (\<turnstile>) D\<close> and
    i: \<open>enat i < llength D\<close>
  shows \<open>(lnth D i) \<subseteq> (Red_F (Liminf_llist D)) \<union> (Liminf_llist D)\<close>
proof (rule,rule)
  fix C
  assume C: \<open>C \<in> (lnth D i)\<close>
  and C_not_Liminf: \<open>C \<notin> (Liminf_llist D)\<close>
  have \<open>C \<in> Sup_llist D\<close> unfolding Sup_llist_def using C i by auto
  then obtain j where j: \<open>C \<in> (lnth D j) - (lnth D (Suc j))\<close> \<open>enat (Suc j) < llength D\<close> 
    using equiv_Sup_Liminf[of C D] C_not_Liminf by auto
  then have \<open>C \<in> Red_F (lnth D (Suc j))\<close> 
    using deriv by (meson chain_lnth_rel contra_subsetD derive.cases)
  then show \<open>C \<in> Red_F (Liminf_llist D)\<close> using Red_F_subset_Liminf[of D "Suc j"] deriv j(2) by blast
qed

text \<open>lemma 5 in Uwe's notes\<close>
lemma fair_implies_Liminf_saturated:
  assumes 
    deriv: \<open>chain (\<turnstile>) D\<close> and
    fair: \<open>fair D\<close>
  shows \<open>Inf (Liminf_llist D) \<subseteq> Red_I (Liminf_llist D)\<close>
proof
  fix \<iota>
  assume \<iota>: \<open>\<iota> \<in> Inf (Liminf_llist D)\<close>
  have \<open>\<iota> \<in> Sup_Red_I_llist D\<close> using fair \<iota> unfolding fair_def by auto
  then obtain i where i: \<open>enat i < llength D\<close> \<open>\<iota> \<in> Red_I (lnth D i)\<close>
    unfolding Sup_Red_I_llist_def by auto
  then show \<open>\<iota> \<in> Red_I (Liminf_llist D)\<close> 
    using deriv i_in_Liminf_or_Red_F[of D i] Red_I_subset_Liminf by blast
qed

end

locale static_refutational_complete_inference_system = inference_system +
  assumes
    static_refutational_complete: "B \<in> Bot_F \<Longrightarrow> saturated N \<and> N |= {B} \<Longrightarrow> \<exists>B'\<in>Bot_F. B' \<in> N"
begin

end


locale dynamic_refutational_complete_inference_system = inference_system +
  assumes
    dynamic_refutational_complete: "B \<in> Bot_F \<Longrightarrow> \<not> lnull D \<Longrightarrow> chain (\<turnstile>) D \<Longrightarrow> fair D 
      \<Longrightarrow> (lnth D 0) |= {B} \<Longrightarrow> \<exists>i \<in> {i. enat i < llength D}. \<exists>B'\<in>Bot_F. B' \<in> (lnth D i)"
begin

text \<open>not in Uwe's notes, personal addition for practice\<close>
sublocale static_refutational_complete_inference_system
proof
  fix B N
  assume 
    bot_elem: \<open>B \<in> Bot_F\<close> and
    saturated_N: "saturated N \<and> N |= {B}"
  define D where "D = LCons N LNil"
  have[simp]: \<open>\<not> lnull D\<close> by (auto simp: D_def)
  have deriv_D: \<open>chain (\<turnstile>) D\<close> by (simp add: chain.chain_singleton D_def)
  have liminf_is_N: "Liminf_llist D = N" by (simp add: D_def Liminf_llist_LCons)
  have head_D: "N = lnth D 0" by (simp add: D_def)
  have "Sup_Red_I_llist D = Red_I N" by (simp add: D_def Sup_Red_I_unit)
  then have fair_D: "fair D" using saturated_N by (simp add: fair_def saturated_def liminf_is_N)  
  obtain i B' where B'_is_bot: \<open>B' \<in> Bot_F\<close> and B'_in: "B' \<in> (lnth D i)" and \<open>i < llength D\<close>
    using dynamic_refutational_complete[of B D] bot_elem fair_D head_D saturated_N deriv_D
    by auto
  then have "i = 0"
    by (auto simp: D_def enat_0_iff)
  show \<open>\<exists>B'\<in>Bot_F. B' \<in> N\<close>
    using B'_is_bot B'_in unfolding \<open>i = 0\<close> head_D[symmetric] by auto
qed


end

text \<open>lemma 6 in Uwe's notes\<close>
text \<open>The assumption that the derivation is not the empty derivation had to be added to the 
  hypotheses of dynamic_refutational_complete for the proof of lemma 6 to work. Otherwise, 
  (lnth D 0) is undefined and the first 'have' can't be proven.\<close>
sublocale static_refutational_complete_inference_system \<subseteq> dynamic_refutational_complete_inference_system
proof
  fix B D
  assume
    bot_elem: \<open>B \<in> Bot_F\<close> and
    deriv: \<open>chain (\<turnstile>) D\<close> and
    fair: \<open>fair D\<close> and
    unsat: \<open>(lnth D 0) |= {B}\<close> and
    non_empty: \<open>\<not> lnull D\<close>
    have subs: \<open>(lnth D 0) \<subseteq> Sup_llist D\<close>
      using lhd_subset_Sup_llist[of D] non_empty by (simp add: lhd_conv_lnth)
    have \<open>Sup_llist D |= {B}\<close> 
      using unsat subset_entailed[OF subs] transitive_entails[of "Sup_llist D" "lnth D 0"] by auto
    then have Sup_no_Red: \<open>Sup_llist D - Red_F (Sup_llist D) |= {B}\<close>
      using bot_elem Red_F_Bot_F by auto
    have Sup_no_Red_in_Liminf: \<open>Sup_llist D - Red_F (Sup_llist D) \<subseteq> Liminf_llist D\<close>
      using deriv Red_in_Sup by auto
    have Liminf_entails_Bot_F: \<open>Liminf_llist D |= {B}\<close>
      using Sup_no_Red subset_entailed[OF Sup_no_Red_in_Liminf] transitive_entails by blast
    have \<open>saturated (Liminf_llist D)\<close> 
      using deriv fair fair_implies_Liminf_saturated unfolding saturated_def by auto
    then have \<open>\<exists>B'\<in>Bot_F. B' \<in> (Liminf_llist D)\<close> 
      using bot_elem static_refutational_complete Liminf_entails_Bot_F by auto
    then show \<open>\<exists>i\<in>{i. enat i < llength D}. \<exists>B'\<in>Bot_F. B' \<in> lnth D i\<close>
      unfolding Liminf_llist_def by auto
qed

end
