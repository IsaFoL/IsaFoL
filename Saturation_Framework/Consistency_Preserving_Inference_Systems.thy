(*  Title:       Consistency-Preserving Inference Systems and Related Concepts
    Author:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2014, 2017, 2020
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2014
    Author:      Anders Schlichtkrull <andschl at dtu.dk>, 2017
    Maintainer:  Anders Schlichtkrull <andschl at dtu.dk>
*)

theory Consistency_Preserving_Inference_Systems
  imports
    Saturation_Framework.Calculi
    Open_Induction.Restricted_Predicates
begin


section \<open>Consistency-Preserving Inference Systems and Related Concepts\<close>

subsection \<open>Compact Consequence-like Relation''\<close>

locale compact_consequencelike_relation =
  fixes
    entails' :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" (infix "|\<approx>" 50)
  assumes
    entails'_trans[trans]: "N1 |\<approx> N2 \<Longrightarrow> N2 |\<approx> N3 \<Longrightarrow> N1 |\<approx> N3" and
    subset_entailed': "N2 \<subseteq> N1 \<Longrightarrow> N1 |\<approx> N2" and
    entails'_compact: "CC |\<approx> {D} \<Longrightarrow> \<exists>CC' \<subseteq> CC. finite CC' \<and> CC' |\<approx> {D}"
begin

lemma entails'_compact_union:
  assumes cd_ent: "CC \<union> DD |\<approx> {E}"
  shows "\<exists>CC' \<subseteq> CC. finite CC' \<and> CC' \<union> DD |\<approx> {E}"
proof -
  obtain CCDD' where
    cd1_fin: "finite CCDD'" and
    cd1_sub: "CCDD' \<subseteq> CC \<union> DD" and
    cd1_ent: "CCDD' |\<approx> {E}"
    using entails'_compact[OF cd_ent] by blast

  define CC' where
    "CC' = CCDD' - DD"
  have "CC' \<subseteq> CC"
    unfolding CC'_def using cd1_sub by blast
  moreover have "finite CC'"
    unfolding CC'_def using cd1_fin by blast
  moreover have "CC' \<union> DD |\<approx> {E}"
    unfolding CC'_def using cd1_ent
    by (metis Un_Diff_cancel2 Un_upper1 entails'_trans subset_entailed')
  ultimately show ?thesis
    by blast
qed

end


section \<open>Consistency-Preserving Inference Systems\<close>

locale consist_preserving_inference_system =
  calculus_with_red_crit + compact_consequencelike_relation +
  assumes
    entails'_bot: "N |\<approx> Bot \<longleftrightarrow> N \<Turnstile> Bot" and
    entails'_consist_preserv: "\<not> N1 \<Turnstile> Bot \<Longrightarrow> N1 |\<approx> N2 \<Longrightarrow> \<not> N2 \<Turnstile> Bot"
begin

lemma chain_entails_derive_consist_preserving:
  assumes
    chain_ent: "chain (|\<approx>) Ns" and
    chain_red: "chain (\<rhd>Red) Ns" and
    n0_sat: "\<not> lhd Ns \<Turnstile> Bot"
  shows "\<not> Sup_llist Ns \<Turnstile> Bot"
proof -
  have bot_sat: "\<not> {} \<Turnstile> Bot"
    by (meson empty_subsetI entails_trans n0_sat subset_entailed)

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
        then have "lnth Ns k \<rhd>Red lnth Ns (Suc k)"
          using chain_red chain_lnth_rel by fastforce
        then have "lnth Ns (Suc k) \<subseteq> lnth Ns k \<union> concl_of ` Inf_from (lnth Ns k)"
          sledgehammer
          by (rule derive_subset)
        moreover have "lnth Ns k \<subseteq> Sup_upto_llist Ns k"
          unfolding Sup_upto_llist_def using False Suc_ile_eq linear by blast
        ultimately have "lnth Ns (Suc k)
          \<subseteq> Sup_upto_llist Ns k \<union> concls_of (inferences_from (Sup_upto_llist Ns k))"
          by clarsimp (metis UnCI UnE image_Un inferences_from_mono le_iff_sup)
        moreover have "Sup_upto_llist Ns (Suc k) = Sup_upto_llist Ns k \<union> lnth Ns (Suc k)"
          unfolding Sup_upto_llist_def using False by (force elim: le_SucE)
        moreover have
          "satisfiable (Sup_upto_llist Ns k \<union> concls_of (inferences_from (Sup_upto_llist Ns k)))"
          using Suc \<Gamma>_sat_preserving unfolding sat_preserving_inference_system_def by simp
        ultimately show ?thesis
          by (metis le_iff_sup true_clss_union)
      qed
    qed
    then have "satisfiable DD"
      using dd_sset unfolding Sup_upto_llist_def by (blast intro: true_clss_mono)
  }
  then show ?thesis
    using ground_resolution_without_selection.clausal_logic_compact[THEN iffD1] by metis
qed

text \<open>
This corresponds to Lemma 4.2:
\<close>

lemma
  assumes
    chain_ent: "chain (|\<approx>) Ns" and
    chain_red: "chain (\<rhd>Red) Ns"
  shows
    Rf_Sup_subset_Rf_Liminf: "Red_F (Sup_llist Ns) \<subseteq> Red_F (Liminf_llist Ns)" and
    Ri_Sup_subset_Ri_Liminf: "Red_Inf (Sup_llist Ns) \<subseteq> Red_Inf (Liminf_llist Ns)" and
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
        ultimately have c_in_k: "C \<in> lnth Ns k"
          using Suc.hyps by blast
        have rel: "lnth Ns k \<rhd>Red lnth Ns (Suc k)"
          using Suc.prems chain_red by (auto simp: chain_lnth_rel)
        then show ?thesis
          using c_in_k c_ni' Suc.prems(2) by cases auto
      next
        case False
        then show ?thesis
          using Suc c_in by auto
      qed
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
      using chain_ent chain_entails_consist_preserving by blast
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
    Rf_limit_Sup: "Red_F (Liminf_llist Ns) = Red_F (Sup_llist Ns)" and
    Ri_limit_Sup: "Red_Inf (Liminf_llist Ns) = Red_Inf (Sup_llist Ns)"
  by (metis assms Liminf_llist_subset_Sup_llist Red_F_of_Red_F_subset Red_F_of_subset Red_in_Sup
      double_diff order_refl subset_antisym)
   (metis assms Liminf_llist_subset_Sup_llist Red_Inf_of_Red_F_subset Red_Inf_of_subset Red_in_Sup
     double_diff order_refl subset_antisym)

end

end
