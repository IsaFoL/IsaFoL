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

subsection \<open>Compact ``Preconsequence Relation''\<close>

locale compact_preconsequence_relation =
  fixes
    entails' :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" (infix "|\<approx>" 50)
  assumes
    entails'_trans[trans]: "N1 |\<approx> N2 \<Longrightarrow> N2 |\<approx> N3 \<Longrightarrow> N1 |\<approx> N3" and
    subset_entailed': "N2 \<subseteq> N1 \<Longrightarrow> N1 |\<approx> N2" and
    entails'_compact: "CC |\<approx> {D} \<Longrightarrow> \<exists>CC' \<subseteq> CC. finite CC' \<and> CC' |\<approx> {D}"
begin

lemma entails_compact_union:
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
  calculus_with_red_crit + compact_preconsequence_relation +
  assumes
    consist_preserv: \<open>\<not> N |\<approx> Bot \<Longrightarrow> \<not> N \<union> concl_of ` Inf_from N |\<approx> Bot\<close>
begin

lemma chain_entails_sat_preserving:
  assumes
    deriv: "chain (|\<approx>) Ns" and
    sat_n0: "\<not> lhd Ns |\<approx> Bot"
  shows "\<not> Sup_llist Ns |\<approx> Bot"
  unfolding Sup_llist_def image_def
  apply auto
  using entails'_compact



proof -

qed

text \<open>
This corresponds to Lemma 4.2:
\<close>

lemma
  assumes deriv: "chain (\<triangleright>) Ns"
  shows
    Rf_Sup_subset_Rf_Liminf: "Rf (Sup_llist Ns) \<subseteq> Rf (Liminf_llist Ns)" and
    Ri_Sup_subset_Ri_Liminf: "Ri (Sup_llist Ns) \<subseteq> Ri (Liminf_llist Ns)" and
    sat_limit_iff: "satisfiable (Liminf_llist Ns) \<longleftrightarrow> satisfiable (lhd Ns)"
proof -
  {
    fix C i j
    assume
      c_in: "C \<in> lnth Ns i" and
      c_ni: "C \<notin> Rf (Sup_llist Ns)" and
      j: "j \<ge> i" and
      j': "enat j < llength Ns"
    from c_ni have c_ni': "\<And>i. enat i < llength Ns \<Longrightarrow> C \<notin> Rf (lnth Ns i)"
      using Rf_mono lnth_subset_Sup_llist Sup_llist_def by (blast dest: contra_subsetD)
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
        have rel: "lnth Ns k \<triangleright> lnth Ns (Suc k)"
          using Suc.prems deriv by (auto simp: chain_lnth_rel)
        then show ?thesis
          using c_in_k c_ni' Suc.prems(2) by cases auto
      next
        case False
        then show ?thesis
          using Suc c_in by auto
      qed
    qed
  }
  then have lu_ll: "Sup_llist Ns - Rf (Sup_llist Ns) \<subseteq> Liminf_llist Ns"
    unfolding Sup_llist_def Liminf_llist_def by blast
  have rf: "Rf (Sup_llist Ns - Rf (Sup_llist Ns)) \<subseteq> Rf (Liminf_llist Ns)"
    using lu_ll Rf_mono by simp
  have ri: "Ri (Sup_llist Ns - Rf (Sup_llist Ns)) \<subseteq> Ri (Liminf_llist Ns)"
    using lu_ll Ri_mono by simp
  show "Rf (Sup_llist Ns) \<subseteq> Rf (Liminf_llist Ns)"
    using rf Rf_indep by blast
  show "Ri (Sup_llist Ns) \<subseteq> Ri (Liminf_llist Ns)"
    using ri Ri_indep by blast

  show "satisfiable (Liminf_llist Ns) \<longleftrightarrow> satisfiable (lhd Ns)"
  proof
    assume "satisfiable (lhd Ns)"
    then have "satisfiable (Sup_llist Ns)"
      using deriv deriv_sat_preserving by simp
    then show "satisfiable (Liminf_llist Ns)"
      using true_clss_mono[OF Liminf_llist_subset_Sup_llist] by blast
  next
    assume "satisfiable (Liminf_llist Ns)"
    then have "satisfiable (Sup_llist Ns - Rf (Sup_llist Ns))"
      using true_clss_mono[OF lu_ll] by blast
    then have "satisfiable (Sup_llist Ns)"
      using Rf_sat by blast
    then show "satisfiable (lhd Ns)"
      using deriv true_clss_mono lhd_subset_Sup_llist chain_not_lnull by metis
  qed
qed

lemma
  assumes "chain (\<triangleright>) Ns"
  shows
    Rf_limit_Sup: "Rf (Liminf_llist Ns) = Rf (Sup_llist Ns)" and
    Ri_limit_Sup: "Ri (Liminf_llist Ns) = Ri (Sup_llist Ns)"
  using assms
  by (auto simp: Rf_Sup_subset_Rf_Liminf Rf_mono Ri_Sup_subset_Ri_Liminf Ri_mono
      Liminf_llist_subset_Sup_llist subset_antisym)

end




end

end
