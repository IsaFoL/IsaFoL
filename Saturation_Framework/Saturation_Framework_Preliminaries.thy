(*  Title:       Saturation Framework Preliminaries
    Author:      Sophie Tourret <stourret at mpi-inf.mpg.de>, 2018
*)

section \<open>Preliminaries\<close>


theory Saturation_Framework_Preliminaries
  imports
    Ordered_Resolution_Prover.Lazy_List_Liminf
    Ordered_Resolution_Prover.Lazy_List_Chain
    (* abbrevs ">t" = ">\<^sub>t" and "\<ge>t" = "\<ge>\<^sub>t" *)
begin

paragraph \<open>
This theory corresponds to the section 2 of the technical report "A Comprehensive Framework for Saturation-Based Theorem Proving"
\<close>

locale consequence_relation =
  fixes
    Bot :: "'f set" and
    entails :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" (infix "\<Turnstile>" 50)
  assumes
    bot_not_empty: "Bot \<noteq> {}" and
    bot_implies_all: "B \<in> Bot \<Longrightarrow> {B} \<Turnstile> N1" and
    subset_entailed: "N2 \<subseteq> N1 \<Longrightarrow> N1 \<Turnstile> N2" and
    all_formulas_entailed: "(\<forall>C \<in> N2. N1 \<Turnstile> {C}) \<Longrightarrow> N1 \<Turnstile> N2" and
    entails_trans [trans]: "N1 \<Turnstile> N2 \<Longrightarrow> N2 \<Turnstile> N3 \<Longrightarrow> N1 \<Turnstile> N3"
begin

lemma entail_set_all_formulas: "N1 \<Turnstile> N2 \<longleftrightarrow> (\<forall>C \<in> N2. N1 \<Turnstile> {C})"
  by (meson all_formulas_entailed empty_subsetI insert_subset subset_entailed entails_trans)

lemma entail_union: "N \<Turnstile> N1 \<and> N \<Turnstile> N2 \<longleftrightarrow> N \<Turnstile> N1 \<union> N2"
  apply (subst entail_set_all_formulas)
  apply (subst (2) entail_set_all_formulas)
  apply (subst (3) entail_set_all_formulas)
  by auto

lemma entail_unions: "(\<forall>i \<in> I. N \<Turnstile> Ni i) \<longleftrightarrow> N \<Turnstile> UNION I Ni"
  apply (subst entail_set_all_formulas)
  apply (subst (2) entail_set_all_formulas)
  apply (rule Complete_Lattices.UN_ball_bex_simps(2)[of Ni I "\<lambda>C. N \<Turnstile> {C}", symmetric]) 
  done


lemma entail_all_bot: "(\<exists>B \<in> Bot. N \<Turnstile> {B}) \<Longrightarrow> (\<forall>B' \<in> Bot. N \<Turnstile> {B'})"
  using bot_implies_all entails_trans by blast

end

datatype 'f inference =
  Infer (prems_of: "'f list") (concl_of: "'f")

locale inference_system =
  fixes
    Inf :: \<open>'f inference set\<close>
begin

definition Inf_from :: "'f set  \<Rightarrow> 'f inference set" where
  "Inf_from N = {\<iota> \<in> Inf. set (prems_of \<iota>) \<subseteq> N}"

end

locale sound_inference_system = inference_system + consequence_relation +
  assumes
    soundness: \<open>\<iota> \<in> Inf \<Longrightarrow> set (prems_of \<iota>) \<Turnstile> {concl_of \<iota>}\<close>

locale calculus_with_red_crit = inference_system Inf + consequence_relation Bot entails
  for
    Bot :: "'f set" and
    Inf :: \<open>'f inference set\<close> and
    entails :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" (infix "\<Turnstile>" 50)
  + fixes 
    Red_Inf :: "'f set \<Rightarrow> 'f inference set" and
    Red_F :: "'f set \<Rightarrow> 'f set"
  assumes
    Red_Inf_to_Inf: "Red_Inf N \<subseteq> Inf" and
    Red_F_Bot: "B \<in> Bot \<Longrightarrow> N \<Turnstile> {B} \<Longrightarrow> N - Red_F N \<Turnstile> {B}" and
    Red_F_of_subset: "N \<subseteq> N' \<Longrightarrow> Red_F N \<subseteq> Red_F N'" and
    Red_Inf_of_subset: "N \<subseteq> N' \<Longrightarrow> Red_Inf N \<subseteq> Red_Inf N'" and
    Red_F_of_Red_F_subset: "N' \<subseteq> Red_F N \<Longrightarrow> Red_F N \<subseteq> Red_F (N - N')" and
    Red_Inf_of_Red_F_subset: "N' \<subseteq> Red_F N \<Longrightarrow> Red_Inf N \<subseteq> Red_Inf (N - N')" and
    Red_Inf_of_Inf_to_N: "\<iota> \<in> Inf \<Longrightarrow> concl_of \<iota> \<in> N \<Longrightarrow> \<iota> \<in> Red_Inf N"
begin

lemma Red_Inf_of_Inf_to_N_subset: "{\<iota> \<in> Inf. (concl_of \<iota> \<in> N)} \<subseteq> Red_Inf N"
  using Red_Inf_of_Inf_to_N by blast 

paragraph \<open>Lemma 1 from the technical report\<close>
lemma red_concl_to_red_inf: 
  assumes 
    i_in: "\<iota> \<in> Inf" and
    concl: "concl_of \<iota> \<in> Red_F N"
  shows "\<iota> \<in> Red_Inf N"
proof -
  have "\<iota> \<in> Red_Inf (Red_F N)" by (simp add: Red_Inf_of_Inf_to_N i_in concl)
  then have i_in_Red: "\<iota> \<in> Red_Inf (N \<union> Red_F N)" by (simp add: Red_Inf_of_Inf_to_N concl i_in)
  have red_n_subs: "Red_F N \<subseteq> Red_F (N \<union> Red_F N)" by (simp add: Red_F_of_subset)
  then have "\<iota> \<in> Red_Inf ((N \<union> Red_F N) - (Red_F N - N))" using Red_Inf_of_Red_F_subset i_in_Red
    by (meson Diff_subset subsetCE subset_trans)
  then show ?thesis by (metis Diff_cancel Diff_subset Un_Diff Un_Diff_cancel contra_subsetD 
    calculus_with_red_crit.Red_Inf_of_subset calculus_with_red_crit_axioms sup_bot.right_neutral)
qed

definition saturated :: "'f set \<Rightarrow> bool" where
  "saturated N \<equiv> Inf_from N \<subseteq> Red_Inf N"

lemma Red_Inf_without_redundant_clauses:
  "Red_Inf (N - Red_F N) = Red_Inf N"
  using Red_Inf_of_subset [of "N - Red_F N" N]
    and Red_Inf_of_Red_F_subset [of "Red_F N" N] by blast

lemma saturated_without_redundant_clauses:
  assumes saturated: "saturated N"
  shows "saturated (N - Red_F N)"
proof -
  have "Inf_from (N - Red_F N) \<subseteq> Inf_from N" unfolding Inf_from_def by auto
  also have "Inf_from N \<subseteq> Red_Inf N" using saturated unfolding saturated_def by auto
  also have "Red_Inf N \<subseteq> Red_Inf (N - Red_F N)" using Red_Inf_of_Red_F_subset by auto
  finally have "Inf_from (N - Red_F N) \<subseteq> Red_Inf (N - Red_F N)" by auto
  then show ?thesis unfolding saturated_def by auto
qed

end

locale static_refutational_complete_calculus = calculus_with_red_crit +
  assumes static_refutational_complete: "B \<in> Bot \<Longrightarrow> saturated N \<Longrightarrow> N \<Turnstile> {B} \<Longrightarrow> \<exists>B'\<in>Bot. B' \<in> N"

context calculus_with_red_crit
begin

definition Sup_Red_Inf_llist :: "'f set llist \<Rightarrow> 'f inference set" where
  "Sup_Red_Inf_llist D = (\<Union>i \<in> {i. enat i < llength D}. Red_Inf (lnth D i))"

lemma Sup_Red_Inf_unit: "Sup_Red_Inf_llist (LCons X LNil) = Red_Inf X" 
  using Sup_Red_Inf_llist_def enat_0_iff(1) by simp

definition fair :: "'f set llist \<Rightarrow> bool" where
  "fair D \<equiv> Inf_from (Liminf_llist D) \<subseteq> Sup_Red_Inf_llist D"
  
inductive "derive" :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" (infix "\<rhd>Red" 50) where
  derive: "M - N \<subseteq> Red_F N \<Longrightarrow> M \<rhd>Red N"

end

context calculus_with_red_crit
begin

text \<open>TODO: replace in \<^theory>\<open>Ordered_Resolution_Prover.Lazy_List_Liminf\<close>.\<close>
lemma (in-) elem_Sup_llist_imp_Sup_upto_llist':
  "x \<in> Sup_llist Xs \<Longrightarrow> \<exists>j < llength Xs. x \<in> Sup_upto_llist Xs j"
  unfolding Sup_llist_def Sup_upto_llist_def by blast 

lemma gt_Max_notin: \<open>finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> x > Max A \<Longrightarrow> x \<notin> A\<close> by auto

lemma equiv_Sup_Liminf:
  assumes 
    in_Sup: "C \<in> Sup_llist D" and
    not_in_Liminf: "C \<notin> Liminf_llist D"
  shows
    "\<exists> i \<in> {i. enat (Suc i) < llength D}. C \<in> lnth D i - lnth D (Suc i)"
proof -
  obtain i where C_D_i: "C \<in> Sup_upto_llist D i" and "i < llength D" 
    using elem_Sup_llist_imp_Sup_upto_llist' in_Sup by fast
  then obtain j where j: "j \<ge> i \<and> enat j < llength D \<and> C \<notin> lnth D j" using not_in_Liminf   
    unfolding Sup_llist_def chain_def Liminf_llist_def by auto
  obtain k where k: "C \<in> lnth D k" "enat k < llength D" "k \<le> i" using C_D_i 
    unfolding Sup_upto_llist_def by auto
  let ?S = "{i. i < j \<and> i \<ge> k \<and> C \<in> lnth D i}"
  define l where "l \<equiv> Max ?S"
  have \<open>k \<in> {i. i < j \<and> k \<le> i \<and> C \<in> lnth D i}\<close> using k j by (auto simp: order.order_iff_strict)
  then have nempty: "{i. i < j \<and> k \<le> i \<and> C \<in> lnth D i} \<noteq> {}" by auto 
  then have l_prop: "l < j \<and> l \<ge> k \<and> C \<in> (lnth D l)" using Max_in[of ?S, OF _ nempty] unfolding l_def by auto 
  then have "C \<in> lnth D l - lnth D (Suc l)" using j gt_Max_notin[OF _ nempty, of "Suc l"] 
    unfolding l_def[symmetric] by (auto intro: Suc_lessI)
  then show ?thesis apply (rule bexI[of _ l]) using l_prop j 
    apply auto 
    by (metis Suc_leI dual_order.order_iff_strict enat_ord_simps(2) less_trans)
qed

text \<open>lemma 2 from the technical report\<close>
lemma Red_in_Sup: 
  assumes deriv: "chain (\<rhd>Red) D"
  shows "Sup_llist D - Liminf_llist D \<subseteq> Red_F (Sup_llist D)"
proof
  fix C
  assume C_in_subset: "C \<in> Sup_llist D - Liminf_llist D"
  {
    fix C i
    assume 
      in_ith_elem: "C \<in> lnth D i - lnth D (Suc i)" and
      i: "enat (Suc i) < llength D"
    have "lnth D i \<rhd>Red lnth D (Suc i)" using i deriv in_ith_elem chain_lnth_rel by auto
    then have "C \<in> Red_F (lnth D (Suc i))" using in_ith_elem derive.cases by blast
    then have "C \<in> Red_F (Sup_llist D)" using Red_F_of_subset 
      by (meson contra_subsetD i lnth_subset_Sup_llist)
  }
  then show "C \<in> Red_F (Sup_llist D)" using equiv_Sup_Liminf[of C] C_in_subset by fast
qed

text \<open>lemma 3 from the technical report 1/2\<close>
lemma Red_Inf_subset_Liminf: 
  assumes deriv: \<open>chain (\<rhd>Red) D\<close> and
    i: \<open>enat i < llength D\<close>
  shows \<open>Red_Inf (lnth D i) \<subseteq> Red_Inf (Liminf_llist D)\<close>
proof -
  have Sup_in_diff: \<open>Red_Inf (Sup_llist D) \<subseteq> Red_Inf (Sup_llist D - (Sup_llist D - Liminf_llist D))\<close> 
    using Red_Inf_of_Red_F_subset[OF Red_in_Sup] deriv by auto
  also have \<open>Sup_llist D - (Sup_llist D - Liminf_llist D) = Liminf_llist D\<close> 
    by (simp add: Liminf_llist_subset_Sup_llist double_diff)
  then have Red_Inf_Sup_in_Liminf: \<open>Red_Inf (Sup_llist D) \<subseteq> Red_Inf (Liminf_llist D)\<close> using Sup_in_diff by auto
  have \<open>lnth D i \<subseteq> Sup_llist D\<close> unfolding Sup_llist_def using i by blast
  then have "Red_Inf (lnth D i) \<subseteq> Red_Inf (Sup_llist D)" using Red_Inf_of_subset 
    unfolding Sup_llist_def by auto 
  then show ?thesis using Red_Inf_Sup_in_Liminf by auto
qed

text \<open>lemma 3 from the technical report 2/2\<close>
lemma Red_F_subset_Liminf:
 assumes deriv: \<open>chain (\<rhd>Red) D\<close> and
    i: \<open>enat i < llength D\<close>
  shows \<open>Red_F (lnth D i) \<subseteq> Red_F (Liminf_llist D)\<close>
proof -
  have Sup_in_diff: \<open>Red_F (Sup_llist D) \<subseteq> Red_F (Sup_llist D - (Sup_llist D - Liminf_llist D))\<close> 
    using Red_F_of_Red_F_subset[OF Red_in_Sup] deriv by auto
  also have \<open>Sup_llist D - (Sup_llist D - Liminf_llist D) = Liminf_llist D\<close> 
    by (simp add: Liminf_llist_subset_Sup_llist double_diff)
  then have Red_F_Sup_in_Liminf: \<open>Red_F (Sup_llist D) \<subseteq> Red_F (Liminf_llist D)\<close>
    using Sup_in_diff by auto
  have \<open>lnth D i \<subseteq> Sup_llist D\<close> unfolding Sup_llist_def using i by blast
  then have "Red_F (lnth D i) \<subseteq> Red_F (Sup_llist D)" using Red_F_of_subset 
    unfolding Sup_llist_def by auto 
  then show ?thesis using Red_F_Sup_in_Liminf by auto
qed

text \<open>lemma 4 from the technical report\<close>
lemma i_in_Liminf_or_Red_F:
  assumes 
    deriv: \<open>chain (\<rhd>Red) D\<close> and
    i: \<open>enat i < llength D\<close>
  shows \<open>lnth D i \<subseteq> Red_F (Liminf_llist D) \<union> Liminf_llist D\<close>
proof (rule,rule)
  fix C
  assume C: \<open>C \<in> lnth D i\<close>
  and C_not_Liminf: \<open>C \<notin> Liminf_llist D\<close>
  have \<open>C \<in> Sup_llist D\<close> unfolding Sup_llist_def using C i by auto
  then obtain j where j: \<open>C \<in> lnth D j - lnth D (Suc j)\<close> \<open>enat (Suc j) < llength D\<close> 
    using equiv_Sup_Liminf[of C D] C_not_Liminf by auto
  then have \<open>C \<in> Red_F (lnth D (Suc j))\<close> 
    using deriv by (meson chain_lnth_rel contra_subsetD derive.cases)
  then show \<open>C \<in> Red_F (Liminf_llist D)\<close> using Red_F_subset_Liminf[of D "Suc j"] deriv j(2) by blast
qed

text \<open>lemma 5 from the technical report\<close>
lemma fair_implies_Liminf_saturated:
  assumes 
    deriv: \<open>chain (\<rhd>Red) D\<close> and
    fair: \<open>fair D\<close>
  shows \<open>Inf_from (Liminf_llist D) \<subseteq> Red_Inf (Liminf_llist D)\<close>
proof
  fix \<iota>
  assume \<iota>: \<open>\<iota> \<in> Inf_from (Liminf_llist D)\<close>
  have \<open>\<iota> \<in> Sup_Red_Inf_llist D\<close> using fair \<iota> unfolding fair_def by auto
  then obtain i where i: \<open>enat i < llength D\<close> \<open>\<iota> \<in> Red_Inf (lnth D i)\<close>
    unfolding Sup_Red_Inf_llist_def by auto
  then show \<open>\<iota> \<in> Red_Inf (Liminf_llist D)\<close> 
    using deriv i_in_Liminf_or_Red_F[of D i] Red_Inf_subset_Liminf by blast
qed

end

locale dynamic_refutational_complete_calculus = calculus_with_red_crit +
  assumes
    dynamic_refutational_complete: "B \<in> Bot \<Longrightarrow> \<not> lnull D \<Longrightarrow> chain (\<rhd>Red) D \<Longrightarrow> fair D 
      \<Longrightarrow> lnth D 0 \<Turnstile> {B} \<Longrightarrow> \<exists>i \<in> {i. enat i < llength D}. \<exists>B'\<in>Bot. B' \<in> lnth D i"
begin

text \<open>lemma 7 from the technical report\<close>
sublocale static_refutational_complete_calculus
proof
  fix B N
  assume 
    bot_elem: \<open>B \<in> Bot\<close> and
    saturated_N: "saturated N" and
    refut_N: "N \<Turnstile> {B}"
  define D where "D = LCons N LNil"
  have[simp]: \<open>\<not> lnull D\<close> by (auto simp: D_def)
  have deriv_D: \<open>chain (\<rhd>Red) D\<close> by (simp add: chain.chain_singleton D_def)
  have liminf_is_N: "Liminf_llist D = N" by (simp add: D_def Liminf_llist_LCons)
  have head_D: "N = lnth D 0" by (simp add: D_def)
  have "Sup_Red_Inf_llist D = Red_Inf N" by (simp add: D_def Sup_Red_Inf_unit)
  then have fair_D: "fair D" using saturated_N by (simp add: fair_def saturated_def liminf_is_N)  
  obtain i B' where B'_is_bot: \<open>B' \<in> Bot\<close> and B'_in: "B' \<in> (lnth D i)" and \<open>i < llength D\<close>
    using dynamic_refutational_complete[of B D] bot_elem fair_D head_D saturated_N deriv_D refut_N
    by auto
  then have "i = 0"
    by (auto simp: D_def enat_0_iff)
  show \<open>\<exists>B'\<in>Bot. B' \<in> N\<close>
    using B'_is_bot B'_in unfolding \<open>i = 0\<close> head_D[symmetric] by auto
qed

end

text \<open>lemma 6 from the technical report\<close>
text \<open>The assumption that the derivation is not the empty derivation had to be added to the 
  hypotheses of \<^text>\<open>dynamic_refutational_complete\<close> for the proof of lemma 10 to work. Otherwise,
  \<^term>\<open>lnth D 0\<close> is undefined and the first 'have' can't be proven.\<close>
sublocale static_refutational_complete_calculus \<subseteq> dynamic_refutational_complete_calculus
proof
  fix B D
  assume
    bot_elem: \<open>B \<in> Bot\<close> and
    deriv: \<open>chain (\<rhd>Red) D\<close> and
    fair: \<open>fair D\<close> and
    unsat: \<open>(lnth D 0) \<Turnstile> {B}\<close> and
    non_empty: \<open>\<not> lnull D\<close>
    have subs: \<open>(lnth D 0) \<subseteq> Sup_llist D\<close>
      using lhd_subset_Sup_llist[of D] non_empty by (simp add: lhd_conv_lnth)
    have \<open>Sup_llist D \<Turnstile> {B}\<close> 
      using unsat subset_entailed[OF subs] entails_trans[of "Sup_llist D" "lnth D 0"] by auto
    then have Sup_no_Red: \<open>Sup_llist D - Red_F (Sup_llist D) \<Turnstile> {B}\<close>
      using bot_elem Red_F_Bot by auto
    have Sup_no_Red_in_Liminf: \<open>Sup_llist D - Red_F (Sup_llist D) \<subseteq> Liminf_llist D\<close>
      using deriv Red_in_Sup by auto
    have Liminf_entails_Bot: \<open>Liminf_llist D \<Turnstile> {B}\<close>
      using Sup_no_Red subset_entailed[OF Sup_no_Red_in_Liminf] entails_trans by blast
    have \<open>saturated (Liminf_llist D)\<close> 
      using deriv fair fair_implies_Liminf_saturated unfolding saturated_def by auto

   then have \<open>\<exists>B'\<in>Bot. B' \<in> (Liminf_llist D)\<close> 
     using bot_elem static_refutational_complete Liminf_entails_Bot by auto
   then show \<open>\<exists>i\<in>{i. enat i < llength D}. \<exists>B'\<in>Bot. B' \<in> lnth D i\<close>
     unfolding Liminf_llist_def by auto
qed


end
