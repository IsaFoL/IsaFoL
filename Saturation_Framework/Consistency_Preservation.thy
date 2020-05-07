(*  Title:       Consistency Preservation Results
    Author:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2014, 2017, 2020
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2014
    Author:      Anders Schlichtkrull <andschl at dtu.dk>, 2017
    Maintainer:  Anders Schlichtkrull <andschl at dtu.dk>
*)

section \<open>Consistency Preservation Results\<close>

theory Consistency_Preservation
  imports
    Saturation_Framework.Calculi
    Open_Induction.Restricted_Predicates
begin


locale compact_consequence_relation = consequence_relation +
  assumes
    entails_compact: "CC \<Turnstile> {D} \<Longrightarrow> \<exists>CC' \<subseteq> CC. finite CC' \<and> CC' \<Turnstile> {D}"
begin

lemma chain_entails_derive_consist_preserving:
  assumes
    chain_ent: "chain (\<Turnstile>) Ns" and
    n0_sat: "\<not> lhd Ns \<Turnstile> Bot"
  shows "\<not> Sup_llist Ns \<Turnstile> Bot"
proof -
  have bot_sat: "\<not> {} \<Turnstile> Bot"
    using n0_sat by (meson empty_subsetI entails_trans subset_entailed)

  have ns0: "lnth Ns 0 = lhd Ns"
    using chain_ent by (metis chain_not_lnull lhd_conv_lnth)

  {
    fix DD
    assume fin: "finite DD" and sset_lun: "DD \<subseteq> Sup_llist Ns"
    then obtain k where dd_sset: "DD \<subseteq> Sup_upto_llist Ns k"
      using finite_Sup_llist_imp_Sup_upto_llist by blast
    have "\<not> Sup_upto_llist Ns k \<Turnstile> Bot"
    proof (induct k)
      case 0
      then show ?case
        using ns0 n0_sat bot_sat unfolding Sup_upto_llist_def by auto
    next
      case (Suc k)
      show ?case
      proof (cases "enat (Suc k) \<ge> llength Ns")
        case True
        then have "Sup_upto_llist Ns k = Sup_upto_llist Ns (Suc k)"
          unfolding Sup_upto_llist_def using le_Suc_eq not_less by blast
        then show ?thesis
          using Suc by simp
      next
        case False
        then have "lnth Ns k \<Turnstile> lnth Ns (Suc k)"
          using chain_ent chain_lnth_rel by fastforce
        show ?thesis
          apply (rule notI)
          unfolding Sup_upto_llist_Suc
          apply (drule entails_trans_strong[rotated])
          apply auto
          apply (meson False Suc_ile_eq \<open>lnth Ns k \<Turnstile> lnth Ns (Suc k)\<close> entails_trans le_cases lnth_subset_Sup_upto_llist subset_entailed)
          using False apply auto[1]
          by (simp add: Suc.hyps)
      qed
    qed
    then have "\<not> DD \<Turnstile> Bot"
      using dd_sset entails_trans subset_entailed unfolding Sup_upto_llist_def by blast
  }
  then show ?thesis
    using entails_compact by (metis bot_entails_all bot_sat entail_set_all_formulas entails_trans)
qed

end

locale consist_preserving_calculus_with_red_crit =
  calculus_with_red_crit + compact_consequence_relation
begin

text \<open>
This corresponds to Lemma 4.2:
\<close>

lemma
  assumes
    chain_ent: "chain (\<Turnstile>) Ns" and
    chain_red: "chain (\<rhd>Red) Ns"
  shows
    Red_F_Sup_subset_Red_F_Liminf: "Red_F (Sup_llist Ns) \<subseteq> Red_F (Liminf_llist Ns)" and
    Red_Inf_Sup_subset_Red_Inf_Liminf: "Red_Inf (Sup_llist Ns) \<subseteq> Red_Inf (Liminf_llist Ns)" and
    sat_limit_iff: "Liminf_llist Ns \<Turnstile> Bot \<longleftrightarrow> lhd Ns \<Turnstile> Bot"
proof -
  {
    fix C i j
    assume
      c_in: "C \<in> lnth Ns i" and
      c_ni: "C \<notin> Red_F (Sup_llist Ns)" and
      j: "j \<ge> i" and
      j': "enat j < llength Ns"
    from c_ni have c_ni': "\<And>i. enat i < llength Ns \<Longrightarrow> C \<notin> Red_F (lnth Ns i)"
      using Red_F_of_subset lnth_subset_Sup_llist by (metis subsetD)
    have "C \<in> lnth Ns j"
    using j j'
    proof (induct j)
      case 0
      then show ?case
        using c_in by blast
    next
      case (Suc k)
      then show ?case
      proof (cases "i < Suc k")
        case True
        have "i \<le> k"
          using True by linarith
        moreover have "enat k < llength Ns"
          using Suc.prems(2) Suc_ile_eq by (blast intro: dual_order.strict_implies_order)
        ultimately have "C \<in> lnth Ns k"
          using Suc.hyps by blast
        moreover have "lnth Ns k \<rhd>Red lnth Ns (Suc k)"
          using Suc.prems(2) chain_lnth_rel chain_red by blast
        ultimately show ?thesis
          by (meson DiffI Suc.prems(2) c_ni' derive.cases subset_eq)
      qed (use Suc c_in in auto)
    qed
  }
  then have lu_ll: "Sup_llist Ns - Red_F (Sup_llist Ns) \<subseteq> Liminf_llist Ns"
    unfolding Sup_llist_def Liminf_llist_def by blast
  have rf: "Red_F (Sup_llist Ns - Red_F (Sup_llist Ns)) \<subseteq> Red_F (Liminf_llist Ns)"
    using lu_ll by (simp add: Red_F_of_subset)
  have ri: "Red_Inf (Sup_llist Ns - Red_F (Sup_llist Ns)) \<subseteq> Red_Inf (Liminf_llist Ns)"
    using lu_ll by (simp add: Red_Inf_of_subset)
  show "Red_F (Sup_llist Ns) \<subseteq> Red_F (Liminf_llist Ns)"
    using rf Red_F_of_Red_F_subset by auto
  show "Red_Inf (Sup_llist Ns) \<subseteq> Red_Inf (Liminf_llist Ns)"
    using Red_Inf_without_red_F ri by auto

  show "Liminf_llist Ns \<Turnstile> Bot \<longleftrightarrow> lhd Ns \<Turnstile> Bot"
  proof
    assume "Liminf_llist Ns \<Turnstile> Bot"
    then have "Sup_llist Ns \<Turnstile> Bot"
      using Liminf_llist_subset_Sup_llist by (metis entails_trans subset_entailed)
    then show "lhd Ns \<Turnstile> Bot"
      using chain_ent chain_entails_derive_consist_preserving by blast
  next
    assume "lhd Ns \<Turnstile> Bot"
    then have "Sup_llist Ns \<Turnstile> Bot"
      by (meson chain_ent chain_not_lnull entails_trans lhd_subset_Sup_llist subset_entailed)
    then have "Sup_llist Ns - Red_F (Sup_llist Ns) \<Turnstile> Bot"
      using Red_F_Bot entail_set_all_formulas by blast
    then show "Liminf_llist Ns \<Turnstile> Bot"
      using entails_trans lu_ll subset_entailed by blast
  qed
qed

lemma
  assumes "chain (\<rhd>Red) Ns"
  shows
    Red_F_limit_Sup: "Red_F (Liminf_llist Ns) = Red_F (Sup_llist Ns)" and
    Red_Inf_limit_Sup: "Red_Inf (Liminf_llist Ns) = Red_Inf (Sup_llist Ns)"
  by (metis assms Liminf_llist_subset_Sup_llist Red_F_of_Red_F_subset Red_F_of_subset Red_in_Sup
      double_diff order_refl subset_antisym)
   (metis assms Liminf_llist_subset_Sup_llist Red_Inf_of_Red_F_subset Red_Inf_of_subset Red_in_Sup
     double_diff order_refl subset_antisym)

end

end
