(*  Title:       The Standard Redundancy Criterion (Revisited)
    Author:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2014, 2017
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2014
    Author:      Anders Schlichtkrull <andschl at dtu.dk>, 2017
    Maintainer:  Jasmin Blanchette <j.c.blanchette at vu.nl>
*)

section \<open>The Standard Redundancy Criterion (Revisited)\<close>

theory Standard_Redundancy
  imports
    Saturation_Framework.Calculi
    "HOL-Library.Multiset_Order"
begin

text \<open>
This material is partly based on Section 4.2.2 (``The Standard Redundancy Criterion'') of Bachmair
and Ganzinger's chapter, but adapted to the saturation framework of Waldmann et al.
\<close>

abbreviation main_prem_of :: "'f inference \<Rightarrow> 'f" where
  "main_prem_of \<iota> \<equiv> last (prems_of \<iota>)"

abbreviation side_prems_of :: "'f inference \<Rightarrow> 'f list" where
  "side_prems_of \<iota> \<equiv> butlast (prems_of \<iota>)"

locale calculus_with_std_red_crit = inference_system Inf + consequence_relation Bot entails
  for
    Bot :: "('f :: wellorder) set" and
    Inf :: \<open>'f inference set\<close> and
    entails :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" (infix "\<Turnstile>" 50) +
  assumes Inf_has_prem: "\<iota> \<in> Inf \<Longrightarrow> prems_of \<iota> \<noteq> []"
begin

definition redundant_infer :: "'f set \<Rightarrow> 'f inference \<Rightarrow> bool" where
  "redundant_infer N \<iota> \<longleftrightarrow>
   (\<exists>DD \<subseteq> N. finite DD \<and> (\<forall>I. I \<Turnstile> DD \<union> set (side_prems_of \<iota>) \<longrightarrow> I \<Turnstile> {concl_of \<iota>})
    \<and> (\<forall>D \<in> DD. D < main_prem_of \<iota>))"

definition Red_Inf :: "'f set \<Rightarrow> 'f inference set" where
"Red_Inf N = {\<iota> \<in> Inf. redundant_infer N \<iota>}"

definition Red_F :: "'f set \<Rightarrow> 'f set" where
"Red_F N = {C. (\<exists>DD \<subseteq> N. finite DD \<and> (\<forall>I. I \<Turnstile> DD \<longrightarrow> I \<Turnstile> {C}) \<and> (\<forall>D \<in> DD. D < C))}"

text \<open>
The following results correspond to Lemma 4.5. The lemma \<open>wlog_non_Red_F\<close> generalizes the core of
the argument.
\<close>

lemma Red_F_of_subset: "N \<subseteq> N' \<Longrightarrow> Red_F N \<subseteq> Red_F N'"
  unfolding Red_F_def by auto

lemma wlog_non_Red_F:
  assumes "DD0 \<subseteq> N" "finite DD0" "\<forall>I. I \<Turnstile> DD0 \<union> CC \<longrightarrow> I \<Turnstile> E" "\<forall>D' \<in> DD0. D' < D"
  shows "\<exists>DD \<subseteq> N - Red_F N. finite DD \<and> (\<forall>I. I \<Turnstile> DD \<union> CC \<longrightarrow> I \<Turnstile> E) \<and> (\<forall>D' \<in> DD. D' < D)"
proof -
  from assms obtain DD0 :: "'f multiset" where
    "set_mset DD0 \<subseteq> N \<and> (\<forall>I. I \<Turnstile> set_mset DD0 \<union> CC \<longrightarrow> I \<Turnstile> E)
    \<and> (\<forall>D' \<in> set_mset DD0. D' < D)"
    by (metis (no_types) finite_set_mset_mset_set)
  hence dd0: "DD0 \<in> {DD. set_mset DD \<subseteq> N \<and> (\<forall>I. I \<Turnstile> set_mset DD \<union> CC \<longrightarrow> I \<Turnstile> E)
      \<and> (\<forall>D' \<in> set_mset DD. D' < D)}"
    by blast
  have "\<exists>DD. set_mset DD \<subseteq> N \<and> (\<forall>I. I \<Turnstile> set_mset DD \<union> CC \<longrightarrow> I \<Turnstile> E) \<and> (\<forall>D' \<in># DD. D' < D) \<and>
    (\<forall>DD'. set_mset DD' \<subseteq> N \<and> (\<forall>I. I \<Turnstile> set_mset DD' \<union> CC \<longrightarrow> I \<Turnstile> E) \<and> (\<forall>D' \<in># DD'. D' < D) \<longrightarrow>
       DD \<le> DD')"
    using wf_eq_minimal[THEN iffD1, rule_format, OF wf_less_multiset, OF dd0]
    unfolding not_le[symmetric] by blast
  then obtain DD where
    dd_subs_n: "set_mset DD \<subseteq> N" and
    ddcc_imp_e: "\<forall>I. I \<Turnstile> set_mset DD \<union> CC \<longrightarrow> I \<Turnstile> E" and
    dd_lt_d: "\<forall>D' \<in># DD. D' < D" and
    d_min: "\<forall>DD'. set_mset DD' \<subseteq> N \<and> (\<forall>I. I \<Turnstile> set_mset DD' \<union> CC \<longrightarrow> I \<Turnstile> E)
        \<and> (\<forall>D' \<in># DD'. D' < D) \<longrightarrow>
      DD \<le> DD'"
    by blast

  have "\<forall>Da. Da \<in># DD \<longrightarrow> Da \<notin> Red_F N"
  proof clarify
    fix Da
    assume
      da_in_dd: "Da \<in># DD" and
      da_rf: "Da \<in> Red_F N"

    from da_rf obtain DD' :: "'f multiset" where
      dd'_subs_n: "set_mset DD' \<subseteq> N" and
      dd'_imp_da: "\<forall>I. I \<Turnstile> set_mset DD' \<longrightarrow> I \<Turnstile> {Da}" and
      dd'_lt_da: "\<forall>D' \<in># DD'. D' < Da"
      unfolding Red_F_def mem_Collect_eq by (metis finite_set_mset_mset_set)

    define DDa where
      "DDa = DD - {#Da#} + DD'"

    have "set_mset DDa \<subseteq> N"
      unfolding DDa_def using dd_subs_n dd'_subs_n
      by (meson contra_subsetD in_diffD subsetI union_iff)
    moreover have "\<forall>I. I \<Turnstile> set_mset DDa \<union> CC \<longrightarrow> I \<Turnstile> E"
      using dd'_imp_da ddcc_imp_e da_in_dd unfolding DDa_def
      by (metis entail_union insert_DiffM2 set_mset_add_mset_insert set_mset_empty set_mset_union)
    moreover have "\<forall>D'. D' \<in># DDa \<longrightarrow> D' < D"
      using dd_lt_d dd'_lt_da da_in_dd unfolding DDa_def
      by (metis insert_DiffM2 order.strict_trans union_iff)
    moreover have "DDa < DD"
      unfolding DDa_def
      by (meson da_in_dd dd'_lt_da mset_lt_single_right_iff single_subset_iff union_le_diff_plus)
    ultimately show False
      using d_min unfolding less_eq_multiset_def by (auto intro!: antisym)
  qed
  then show ?thesis
    using dd_subs_n ddcc_imp_e dd_lt_d by blast
qed

lemma Red_F_imp_ex_non_Red_F:
  assumes "C \<in> Red_F N"
  shows "\<exists>CC \<subseteq> N - Red_F N. finite CC \<and> (\<forall>I. I \<Turnstile> CC \<longrightarrow> I \<Turnstile> {C}) \<and> (\<forall>C' \<in> CC. C' < C)"
  using assms by (auto simp: Red_F_def intro: wlog_non_Red_F[of _ _ "{}", simplified])

lemma Red_F_subs_Red_F_diff_Red_F: "Red_F N \<subseteq> Red_F (N - Red_F N)"
proof
  fix C
  assume c_rf: "C \<in> Red_F N"
  then obtain CC where
    cc_fin: "finite CC" and
    cc_subs: "CC \<subseteq> N - Red_F N" and
    cc_imp_c: "\<forall>I. I \<Turnstile> CC \<longrightarrow> I \<Turnstile> {C}" and
    cc_lt_c: "\<forall>C' \<in> CC. C' < C"
    using Red_F_imp_ex_non_Red_F[of C N] by blast
  have "\<forall>D \<in> CC. D \<notin> Red_F N"
    using cc_subs by fast
  then have cc_nr:
    "\<forall>C \<in> CC. \<forall>DD \<subseteq> N. finite DD \<longrightarrow> (\<forall>I. I \<Turnstile> DD \<longrightarrow> I \<Turnstile> {C}) \<longrightarrow> (\<exists>D \<in> DD. \<not> D < C)"
    unfolding Red_F_def by simp metis
  have "CC \<subseteq> N"
    using cc_subs by auto
  then have "CC \<subseteq> N - {C. \<exists>DD \<subseteq> N. finite DD \<and> (\<forall>I. I \<Turnstile> DD \<longrightarrow> I \<Turnstile> {C}) \<and> (\<forall>D \<in> DD. D < C)}"
    using cc_nr by blast
  then show "C \<in> Red_F (N - Red_F N)"
    using cc_fin cc_imp_c cc_lt_c unfolding Red_F_def by auto
qed

lemma Red_F_eq_Red_F_diff_Red_F: "Red_F N = Red_F (N - Red_F N)"
  by (simp add: Red_F_of_subset Red_F_subs_Red_F_diff_Red_F set_eq_subset)

text \<open>
The following results correspond to Lemma 4.6.
\<close>

lemma Red_Inf_of_subset: "N \<subseteq> N' \<Longrightarrow> Red_Inf N \<subseteq> Red_Inf N'"
  unfolding Red_Inf_def redundant_infer_def by auto

lemma Red_Inf_subs_Red_Inf_diff_Red_F: "Red_Inf N \<subseteq> Red_Inf (N - Red_F N)"
proof
  fix \<iota>
  assume \<iota>_ri: "\<iota> \<in> Red_Inf N"
  define CC where
    "CC = set (side_prems_of \<iota>)"
  define D where
    "D = main_prem_of \<iota>"
  define E where
    "E = concl_of \<iota>"
  obtain DD where
    dd_sub: "DD \<subseteq> N" and
    dd_fin: "finite DD" and
    dd_ent: "\<forall>I. I \<Turnstile> DD \<union> CC \<longrightarrow> I \<Turnstile> {E}" and
    dd_lt_d: "\<forall>C \<in> DD. C < D"
    using \<iota>_ri unfolding Red_Inf_def redundant_infer_def CC_def D_def E_def by blast
  obtain DD' where
    "DD' \<subseteq> N - Red_F N" and "finite DD'" and "\<forall>I. I \<Turnstile> DD' \<union> CC \<longrightarrow> I \<Turnstile> {E}" and
    "\<forall>D' \<in> DD'. D' < D"
    using wlog_non_Red_F[OF dd_sub dd_fin dd_ent dd_lt_d] by blast
  then show "\<iota> \<in> Red_Inf (N - Red_F N)"
    using \<iota>_ri unfolding Red_Inf_def redundant_infer_def CC_def D_def E_def by blast
qed

lemma Red_Inf_eq_Red_Inf_diff_Red_F: "Red_Inf N = Red_Inf (N - Red_F N)"
  by (metis Diff_subset Red_Inf_of_subset Red_Inf_subs_Red_Inf_diff_Red_F subset_antisym)

lemma Red_Inf_to_Inf: "Red_Inf N \<subseteq> Inf"
  unfolding Red_Inf_def by blast

lemma Red_F_indep: "N' \<subseteq> Red_F N \<Longrightarrow> Red_F N \<subseteq> Red_F (N - N')"
  by (metis Diff_mono Red_F_eq_Red_F_diff_Red_F Red_F_of_subset order_refl)

lemma Red_Inf_of_Red_F_subset: "N' \<subseteq> Red_F N \<Longrightarrow> Red_Inf N \<subseteq> Red_Inf (N - N')"
  by (metis Diff_mono Red_Inf_eq_Red_Inf_diff_Red_F Red_Inf_of_subset order_refl)

lemma Red_F_model: "I \<Turnstile> N - Red_F N \<Longrightarrow> I \<Turnstile> N"
  by (metis DiffI Red_F_imp_ex_non_Red_F entail_set_all_formulas entails_trans subset_entailed)

lemma Red_F_Bot: "B \<in> Bot \<Longrightarrow> N \<Turnstile> {B} \<Longrightarrow> N - Red_F N \<Turnstile> {B}"
  using Red_F_model entails_trans subset_entailed by blast

lemma Red_Inf_of_Inf_to_N: "\<iota> \<in> Inf \<Longrightarrow> concl_of \<iota> \<in> N \<Longrightarrow> \<iota> \<in> Red_Inf N" sorry



sublocale redundancy_criterion Inf Red_F Red_Inf
  by unfold_locales (rule Red_Inf_to_Inf, (elim Red_F_of_subset Red_Inf_of_subset Red_F_indep Red_Inf_indep Red_F_sat)+)

end

locale standard_redundancy_criterion_reductive =
  standard_redundancy_criterion + reductive_inference_system
begin

text \<open>
The following corresponds to Theorems 4.7 and 4.8:
\<close>

lemma Red_Inf_effective:
  assumes
    in_\<iota>: "\<iota> \<in> Inf" and
    concl_of_in_n_un_rf_n: "concl_of \<iota> \<in> N \<union> Red_F N"
  shows "\<iota> \<in> Red_Inf N"
proof -
  obtain CC D E where
    \<iota>: "\<iota> = Infer CC D E"
    by (cases \<iota>)
  then have cc: "CC = side_prems_of \<iota>" and d: "D = main_prem_of \<iota>" and e: "E = concl_of \<iota>"
    unfolding \<iota> by simp_all
  note e_in_n_un_rf_n = concl_of_in_n_un_rf_n[folded e]

  {
    assume "E \<in> N"
    moreover have "E < D"
      using Inf_reductive e d in_\<iota> by auto
    ultimately have
      "set_mset {#E#} \<subseteq> N" and "\<forall>I. I \<Turnstile>m {#E#} + CC \<longrightarrow> I \<Turnstile> E" and "\<forall>D'. D' \<in># {#E#} \<longrightarrow> D' < D"
      by simp_all
    then have "redundant_infer N \<iota>"
      using redundant_infer_def cc d e by blast
  }
  moreover
  {
    assume "E \<in> Red_F N"
    then obtain DD where
      dd_sset: "set_mset DD \<subseteq> N" and
      dd_imp_e: "\<forall>I. I \<Turnstile>m DD \<longrightarrow> I \<Turnstile> E" and
      dd_lt_e: "\<forall>C'. C' \<in># DD \<longrightarrow> C' < E"
      unfolding Red_F_def by blast
    from dd_lt_e have "\<forall>Da. Da \<in># DD \<longrightarrow> Da < D"
      using d e in_\<iota> Inf_reductive less_trans by blast
    then have "redundant_infer N \<iota>"
      using redundant_infer_def dd_sset dd_imp_e cc d e by blast
  }
  ultimately show "\<iota> \<in> Red_Inf N"
    using in_\<iota> e_in_n_un_rf_n unfolding Red_Inf_def by blast
qed

sublocale effective_redundancy_criterion Inf Red_F Red_Inf
  unfolding effective_redundancy_criterion_def
  by (intro conjI redundancy_criterion_axioms, unfold_locales, rule Red_Inf_effective)

lemma contradiction_Red_F: "{#} \<in> N \<Longrightarrow> Red_Inf N = Inf"
  unfolding Red_Inf_def redundant_infer_def using Inf_reductive le_multiset_empty_right
  by (force intro: exI[of _ "{#{#}#}"] le_multiset_empty_left)

end

locale standard_redundancy_criterion_counterex_reducing =
  standard_redundancy_criterion + counterex_reducing_inference_system
begin

text \<open>
The following result corresponds to Theorem 4.9.
\<close>

lemma saturated_upto_complete_if:
  assumes
    satur: "saturated_upto N" and
    unsat: "\<not> satisfiable N"
  shows "{#} \<in> N"
proof (rule ccontr)
  assume ec_ni_n: "{#} \<notin> N"

  define M where
    "M = N - Red_F N"

  have ec_ni_m: "{#} \<notin> M"
    unfolding M_def using ec_ni_n by fast

  have "I_of M \<Turnstile>s M"
  proof (rule ccontr)
    assume "\<not> I_of M \<Turnstile>s M"
    then obtain D where
      d_in_m: "D \<in> M" and
      d_cex: "\<not> I_of M \<Turnstile> D" and
      d_min: "\<And>C. C \<in> M \<Longrightarrow> C < D \<Longrightarrow> I_of M \<Turnstile> C"
      using ex_min_counterex by meson
    then obtain \<iota> CC E where
      \<iota>: "\<iota> = Infer CC D E" and
      cc_subs_m: "set_mset CC \<subseteq> M" and
      cc_true: "I_of M \<Turnstile>m CC" and
      \<iota>_in: "\<iota> \<in> Inf" and
      e_cex: "\<not> I_of M \<Turnstile> E" and
      e_lt_d: "E < D"
      using Inf_counterex_reducing[OF ec_ni_m] not_less by metis
    have cc: "CC = side_prems_of \<iota>" and d: "D = main_prem_of \<iota>" and e: "E = concl_of \<iota>"
      unfolding \<iota> by simp_all
    have "\<iota> \<in> Red_Inf N"
      by (rule subsetD[OF satur[unfolded saturated_upto_def inferences_from_def infer_from_def]])
        (simp add: \<iota>_in d_in_m cc_subs_m cc[symmetric] d[symmetric] M_def[symmetric])
    then have "\<iota> \<in> Red_Inf M"
      unfolding M_def using Red_Inf_indep by fast
    then obtain DD where
      dd_subs_m: "set_mset DD \<subseteq> M" and
      dd_cc_imp_d: "\<forall>I. I \<Turnstile>m DD + CC \<longrightarrow> I \<Turnstile> E" and
      dd_lt_d: "\<forall>C. C \<in># DD \<longrightarrow> C < D"
      unfolding Red_Inf_def redundant_infer_def cc d e by blast
    from dd_subs_m dd_lt_d have "I_of M \<Turnstile>m DD"
      using d_min unfolding true_cls_mset_def by (metis contra_subsetD)
    then have "I_of M \<Turnstile> E"
      using dd_cc_imp_d cc_true by auto
    then show False
      using e_cex by auto
  qed
  then have "I_of M \<Turnstile>s N"
    using M_def Red_F_model by blast
  then show False
    using unsat by blast
qed

theorem saturated_upto_complete:
  assumes "saturated_upto N"
  shows "\<not> satisfiable N \<longleftrightarrow> {#} \<in> N"
  using assms saturated_upto_complete_if true_clss_def by auto

end

end
