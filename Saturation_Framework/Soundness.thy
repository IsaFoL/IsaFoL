(*  Title:       Soundness
    Author:      Sophie Tourret <stourret at mpi-inf.mpg.de>, 2020
    Author:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2014, 2017, 2020
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2014
    Author:      Anders Schlichtkrull <andschl at dtu.dk>, 2017
*)

section \<open>Soundness\<close>

theory Soundness
  imports Saturation_Framework.Calculus
begin

text \<open>
Although consistency-preservation usually suffices, soundness is a more precise concept and is
sometimes useful.
\<close>

locale sound_inference_system = inference_system + consequence_relation +
  assumes
    sound: \<open>\<iota> \<in> Inf \<Longrightarrow> set (prems_of \<iota>) \<Turnstile> {concl_of \<iota>}\<close>
begin

lemma Inf_consist_preserving:
  assumes n_cons: "\<not> N \<Turnstile> Bot"
  shows "\<not> N \<union> concl_of ` Inf_from N \<Turnstile> Bot"
proof -
  have "N \<Turnstile> concl_of ` Inf_from N"
    using sound unfolding Inf_from_def image_def Bex_def mem_Collect_eq
    by (smt all_formulas_entailed entails_trans mem_Collect_eq subset_entailed)
  then show ?thesis
    using n_cons entails_trans_strong by blast
qed

end

text \<open>
Assuming compactness of the consequence relation, the limit of a derivation based on a redundancy
criterion is satisfiable if and only if the initial set is satisfiable. This material is partly
based on Section 4.1 of Bachmair and Ganzinger's \emph{Handbook} chapter, but adapted to the
saturation framework of Waldmann et al.
\<close>

locale compact_consequence_relation = consequence_relation +
  assumes
    entails_compact: "CC \<Turnstile> Bot \<Longrightarrow> \<exists>CC' \<subseteq> CC. finite CC' \<and> CC' \<Turnstile> Bot"
begin

lemma chain_entails_derive_consist_preserving:
  assumes
    ent: "chain (\<Turnstile>) Ns" and
    n0_sat: "\<not> lhd Ns \<Turnstile> Bot"
  shows "\<not> Sup_llist Ns \<Turnstile> Bot"
proof -
  have bot_sat: "\<not> {} \<Turnstile> Bot"
    using n0_sat by (meson empty_subsetI entails_trans subset_entailed)

  {
    fix DD
    assume fin: "finite DD" and sset_lun: "DD \<subseteq> Sup_llist Ns"
    then obtain k where
      dd_sset: "DD \<subseteq> Sup_upto_llist Ns (enat k)"
      using finite_Sup_llist_imp_Sup_upto_llist by blast
    have "\<not> Sup_upto_llist Ns (enat k) \<Turnstile> Bot"
    proof (induct k)
      case 0
      then show ?case
        unfolding Sup_upto_llist_def
        using lhd_conv_lnth[OF chain_not_lnull[OF ent], symmetric] n0_sat bot_sat by auto
    next
      case (Suc k)
      show ?case
      proof (cases "enat (Suc k) \<ge> llength Ns")
        case True
        then have "Sup_upto_llist Ns (enat k) = Sup_upto_llist Ns (enat (Suc k))"
          unfolding Sup_upto_llist_def using le_Suc_eq by auto
        then show ?thesis
          using Suc by simp
      next
        case False
        then have entail_succ: "lnth Ns k \<Turnstile> lnth Ns (Suc k)"
          using ent chain_lnth_rel by fastforce
        from False have lt: "enat (Suc k) < llength Ns \<and> enat k < llength Ns"
          by (meson Suc_ile_eq le_cases not_le)
        have "{i. enat i < llength Ns \<and> i \<le> Suc k} =
          {i. enat i < llength Ns \<and> i \<le> k} \<union> {i. enat i < llength Ns \<and> i = Suc k}" by auto
        then have "Sup_upto_llist Ns (enat (Suc k)) =
          Sup_upto_llist Ns (enat k) \<union> lnth Ns (Suc k)"
          using lt unfolding Sup_upto_llist_def enat_ord_code(1) by blast
        moreover have "Sup_upto_llist Ns k \<Turnstile> lnth Ns (Suc k)"
          using entail_succ subset_entailed [of "lnth Ns k" "Sup_upto_llist Ns k"] lt
          unfolding Sup_upto_llist_def by (simp add: entail_succ UN_upper entails_trans)
        ultimately have "Sup_upto_llist Ns k \<Turnstile> Sup_upto_llist Ns (Suc k)"
          using entail_union subset_entailed by fastforce
        then show ?thesis using Suc.hyps using entails_trans by blast
      qed
    qed
    then have "\<not> DD \<Turnstile> Bot"
      using dd_sset entails_trans subset_entailed unfolding Sup_upto_llist_def by blast
  }
  then show ?thesis
    using entails_compact by auto
qed

end

locale refutationally_compact_calculus = calculus + compact_consequence_relation
begin

text \<open>
The next three lemmas correspond to Lemma 4.2:
\<close>

lemma Red_F_Sup_subset_Red_F_Liminf:
  "chain (\<rhd>Red) Ns \<Longrightarrow> Red_F (Sup_llist Ns) \<subseteq> Red_F (Liminf_llist Ns)"
  by (metis Liminf_llist_subset_Sup_llist Red_in_Sup Un_absorb1 calculus.Red_F_of_Red_F_subset
      calculus_axioms double_diff sup_ge2)

lemma Red_I_Sup_subset_Red_I_Liminf:
  "chain (\<rhd>Red) Ns \<Longrightarrow> Red_I (Sup_llist Ns) \<subseteq> Red_I (Liminf_llist Ns)"
  by (metis Liminf_llist_subset_Sup_llist Red_I_of_Red_F_subset Red_in_Sup double_diff subset_refl)

lemma unsat_limit_iff:
  assumes
    chain_red: "chain (\<rhd>Red) Ns" and
    chain_ent: "chain (\<Turnstile>) Ns"
  shows "Liminf_llist Ns \<Turnstile> Bot \<longleftrightarrow> lhd Ns \<Turnstile> Bot"
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
    using entails_trans subset_entailed by (smt Diff_iff Red_in_Sup chain_red subset_eq)
qed

text \<open>Some easy consequences:\<close>

lemma Red_F_limit_Sup: "chain (\<rhd>Red) Ns \<Longrightarrow> Red_F (Liminf_llist Ns) = Red_F (Sup_llist Ns)"
  by (metis Liminf_llist_subset_Sup_llist Red_F_of_Red_F_subset Red_F_of_subset Red_in_Sup
      double_diff order_refl subset_antisym)

lemma Red_I_limit_Sup: "chain (\<rhd>Red) Ns \<Longrightarrow> Red_I (Liminf_llist Ns) = Red_I (Sup_llist Ns)"
  by (metis Liminf_llist_subset_Sup_llist Red_I_of_Red_F_subset Red_I_of_subset Red_in_Sup
      double_diff order_refl subset_antisym)

end

end
