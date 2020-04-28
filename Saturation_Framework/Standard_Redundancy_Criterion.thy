(*  Title:       The Standard Redundancy Criterion (Revisited)
    Author:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2014, 2017, 2020
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2014
    Author:      Anders Schlichtkrull <andschl at dtu.dk>, 2017
    Maintainer:  Jasmin Blanchette <j.c.blanchette at vu.nl>
*)

section \<open>The Standard Redundancy Criterion (Revisited)\<close>

theory Standard_Redundancy_Criterion
  imports Counterexample_Reducing_Inference_Systems
begin

text \<open>
This material is partly based on Section 4.2.2 (``The Standard Redundancy Criterion'') of Bachmair
and Ganzinger's chapter, but adapted to the saturation framework of Waldmann et al.
\<close>

locale calculus_with_std_red_crit = inference_system Inf + consequence_relation Bot entails
  for
    Inf :: "('f :: wellorder) inference set" and
    Bot :: "'f set" and
    entails :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" (infix "\<Turnstile>" 50) +
  assumes
    Inf_has_prem: "\<iota> \<in> Inf \<Longrightarrow> prems_of \<iota> \<noteq> []" and
    Inf_reductive: "\<iota> \<in> Inf \<Longrightarrow> concl_of \<iota> < main_prem_of \<iota>"
begin

definition redundant_infer :: "'f set \<Rightarrow> 'f inference \<Rightarrow> bool" where
  "redundant_infer N \<iota> \<longleftrightarrow>
   (\<exists>DD \<subseteq> N. finite DD \<and> DD \<union> set (side_prems_of \<iota>) \<Turnstile> {concl_of \<iota>} \<and> (\<forall>D \<in> DD. D < main_prem_of \<iota>))"

definition Red_Inf :: "'f set \<Rightarrow> 'f inference set" where
"Red_Inf N = {\<iota> \<in> Inf. redundant_infer N \<iota>}"

definition Red_F :: "'f set \<Rightarrow> 'f set" where
"Red_F N = {C. (\<exists>DD \<subseteq> N. finite DD \<and> DD \<Turnstile> {C} \<and> (\<forall>D \<in> DD. D < C))}"

text \<open>
The following results correspond to Lemma 4.5. The lemma \<open>wlog_non_Red_F\<close> generalizes the core of
the argument.
\<close>

lemma Red_F_of_subset: "N \<subseteq> N' \<Longrightarrow> Red_F N \<subseteq> Red_F N'"
  unfolding Red_F_def by auto

lemma wlog_non_Red_F:
  assumes "DD0 \<subseteq> N" "finite DD0" "DD0 \<union> CC \<Turnstile> E" "\<forall>D' \<in> DD0. D' < D"
  shows "\<exists>DD \<subseteq> N - Red_F N. finite DD \<and> DD \<union> CC \<Turnstile> E \<and> (\<forall>D' \<in> DD. D' < D)"
proof -
  from assms obtain DD0 :: "'f multiset" where
    "set_mset DD0 \<subseteq> N \<and> set_mset DD0 \<union> CC \<Turnstile> E \<and> (\<forall>D' \<in> set_mset DD0. D' < D)"
    by (metis (no_types) finite_set_mset_mset_set)
  hence dd0: "DD0 \<in> {DD. set_mset DD \<subseteq> N \<and> set_mset DD \<union> CC \<Turnstile> E \<and> (\<forall>D' \<in> set_mset DD. D' < D)}"
    by blast
  have "\<exists>DD. set_mset DD \<subseteq> N \<and> set_mset DD \<union> CC \<Turnstile> E \<and> (\<forall>D' \<in># DD. D' < D) \<and>
    (\<forall>DD'. set_mset DD' \<subseteq> N \<and> set_mset DD' \<union> CC \<Turnstile> E \<and> (\<forall>D' \<in># DD'. D' < D) \<longrightarrow> DD \<le> DD')"
    using wf_eq_minimal[THEN iffD1, rule_format, OF wf_less_multiset, OF dd0]
    unfolding not_le[symmetric] by blast
  then obtain DD :: "'f multiset" where
    dd_subs_n: "set_mset DD \<subseteq> N" and
    ddcc_ent_e: "set_mset DD \<union> CC \<Turnstile> E" and
    dd_lt_d: "\<forall>D' \<in># DD. D' < D" and
    d_min: "\<forall>DD'. set_mset DD' \<subseteq> N \<and> set_mset DD' \<union> CC \<Turnstile> E \<and> (\<forall>D' \<in># DD'. D' < D) \<longrightarrow> DD \<le> DD'"
    by blast

  have "\<forall>Da. Da \<in># DD \<longrightarrow> Da \<notin> Red_F N"
  proof clarify
    fix Da
    assume
      da_in_dd: "Da \<in># DD" and
      da_rf: "Da \<in> Red_F N"

    from da_rf obtain DD' :: "'f multiset" where
      dd'_subs_n: "set_mset DD' \<subseteq> N" and
      dd'_ent_da: "set_mset DD' \<Turnstile> {Da}" and
      dd'_lt_da: "\<forall>D' \<in># DD'. D' < Da"
      unfolding Red_F_def mem_Collect_eq by (metis finite_set_mset_mset_set)

    define DDa :: "'f multiset" where
      "DDa = DD - {#Da#} + DD'"

    have "set_mset DDa \<subseteq> N"
      unfolding DDa_def using dd_subs_n dd'_subs_n
      by (meson contra_subsetD in_diffD subsetI union_iff)
    moreover have "set_mset DDa \<union> CC \<Turnstile> E"
      by (rule subset_entailed_strong[of _ "{Da}"],
          metis DDa_def dd'_ent_da entail_union entails_trans order_refl set_mset_union
            subset_entailed,
          smt DDa_def da_in_dd ddcc_ent_e entails_trans insert_DiffM2 set_mset_add_mset_insert
            set_mset_empty set_mset_union subset_entailed sup_assoc sup_commute sup_ge1)
    moreover have "\<forall>D' \<in># DDa. D' < D"
      using dd_lt_d dd'_lt_da da_in_dd unfolding DDa_def
      by (metis insert_DiffM2 order.strict_trans union_iff)
    moreover have "DDa < DD"
      unfolding DDa_def
      by (meson da_in_dd dd'_lt_da mset_lt_single_right_iff single_subset_iff union_le_diff_plus)
    ultimately show False
      using d_min unfolding less_eq_multiset_def by (auto intro!: antisym)
  qed
  then show ?thesis
    using dd_subs_n ddcc_ent_e dd_lt_d by blast
qed

lemma Red_F_imp_ex_non_Red_F:
  assumes "C \<in> Red_F N"
  shows "\<exists>CC \<subseteq> N - Red_F N. finite CC \<and> CC \<Turnstile> {C} \<and> (\<forall>C' \<in> CC. C' < C)"
  using assms by (auto simp: Red_F_def intro: wlog_non_Red_F[of _ _ "{}", simplified])

lemma Red_F_subs_Red_F_diff_Red_F: "Red_F N \<subseteq> Red_F (N - Red_F N)"
proof
  fix C
  assume c_rf: "C \<in> Red_F N"
  then obtain CC :: "'f set" where
    cc_fin: "finite CC" and
    cc_subs: "CC \<subseteq> N - Red_F N" and
    cc_ent_c: "CC \<Turnstile> {C}" and
    cc_lt_c: "\<forall>C' \<in> CC. C' < C"
    using Red_F_imp_ex_non_Red_F[of C N] by blast
  have "\<forall>D \<in> CC. D \<notin> Red_F N"
    using cc_subs by fast
  then have cc_nr:
    "\<forall>C \<in> CC. \<forall>DD \<subseteq> N. finite DD \<longrightarrow> DD \<Turnstile> {C} \<longrightarrow> (\<exists>D \<in> DD. \<not> D < C)"
    unfolding Red_F_def by simp
  have "CC \<subseteq> N"
    using cc_subs by auto
  then have "CC \<subseteq> N - {C. \<exists>DD \<subseteq> N. finite DD \<and> DD \<Turnstile> {C} \<and> (\<forall>D \<in> DD. D < C)}"
    using cc_nr by blast
  then show "C \<in> Red_F (N - Red_F N)"
    using cc_fin cc_ent_c cc_lt_c unfolding Red_F_def by blast
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
  define CC :: "'f set" where
    "CC = set (side_prems_of \<iota>)"
  define D :: 'f where
    "D = main_prem_of \<iota>"
  define E :: 'f where
    "E = concl_of \<iota>"
  obtain DD :: "'f set" where
    dd_sub: "DD \<subseteq> N" and
    dd_fin: "finite DD" and
    dd_ent: "DD \<union> CC \<Turnstile> {E}" and
    dd_lt_d: "\<forall>C \<in> DD. C < D"
    using \<iota>_ri unfolding Red_Inf_def redundant_infer_def CC_def D_def E_def by blast
  obtain DD' :: "'f set" where
    "DD' \<subseteq> N - Red_F N" and "finite DD'" and "DD' \<union> CC \<Turnstile> {E}" and "\<forall>D' \<in> DD'. D' < D"
    using wlog_non_Red_F[OF dd_sub dd_fin dd_ent dd_lt_d] by blast
  then show "\<iota> \<in> Red_Inf (N - Red_F N)"
    using \<iota>_ri unfolding Red_Inf_def redundant_infer_def CC_def D_def E_def by blast
qed

lemma Red_Inf_eq_Red_Inf_diff_Red_F: "Red_Inf N = Red_Inf (N - Red_F N)"
  by (metis Diff_subset Red_Inf_of_subset Red_Inf_subs_Red_Inf_diff_Red_F subset_antisym)

lemma Red_Inf_to_Inf: "Red_Inf N \<subseteq> Inf"
  unfolding Red_Inf_def by blast

lemma Red_F_of_Red_F_subset: "N' \<subseteq> Red_F N \<Longrightarrow> Red_F N \<subseteq> Red_F (N - N')"
  by (metis Diff_mono Red_F_eq_Red_F_diff_Red_F Red_F_of_subset order_refl)

lemma Red_Inf_of_Red_F_subset: "N' \<subseteq> Red_F N \<Longrightarrow> Red_Inf N \<subseteq> Red_Inf (N - N')"
  by (metis Diff_mono Red_Inf_eq_Red_Inf_diff_Red_F Red_Inf_of_subset order_refl)

lemma Red_F_model: "M \<Turnstile> N - Red_F N \<Longrightarrow> M \<Turnstile> N"
  by (metis DiffI Red_F_imp_ex_non_Red_F entail_set_all_formulas entails_trans subset_entailed)

lemma Red_F_Bot: "B \<in> Bot \<Longrightarrow> N \<Turnstile> {B} \<Longrightarrow> N - Red_F N \<Turnstile> {B}"
  using Red_F_model entails_trans subset_entailed by blast

lemma Red_Inf_of_Inf_to_N:
  assumes
    in_\<iota>: "\<iota> \<in> Inf" and
    concl_in: "concl_of \<iota> \<in> N"
  shows "\<iota> \<in> Red_Inf N"
proof -
  have "concl_of \<iota> \<in> N \<Longrightarrow> redundant_infer N \<iota>"
    unfolding redundant_infer_def
    by (metis Inf_reductive empty_iff empty_subsetI entail_union finite.emptyI finite_insert in_\<iota>
        insert_iff insert_subset subset_entailed subset_refl)
  then show "\<iota> \<in> Red_Inf N"
    by (simp add: Red_Inf_def concl_in in_\<iota>)
qed

text \<open>
The following corresponds to Theorems 4.7 and 4.8:
\<close>

sublocale calculus_with_red_crit Bot Inf "(\<Turnstile>)" Red_Inf Red_F
  by (unfold_locales, fact Red_Inf_to_Inf, fact Red_F_Bot, fact Red_F_of_subset,
      fact Red_Inf_of_subset, fact Red_F_of_Red_F_subset, fact Red_Inf_of_Red_F_subset,
      fact Red_Inf_of_Inf_to_N)

end

locale cex_red_calculus_with_std_red_crit =
  calculus_with_std_red_crit Inf + cex_red_inference_system _ _ Inf
  for Inf :: "('f :: wellorder) inference set"
begin

text \<open>
The following result loosely corresponds to Theorem 4.9.
\<close>

lemma saturated_complete:
  assumes
    satur: "saturated N" and
    bot_ni_n: "N \<inter> Bot = {}"
  shows "I_of N \<Turnstile> N"
proof (rule ccontr)
  assume "\<not> I_of N \<Turnstile> N"
  then obtain D :: 'f where
    d_in_n: "D \<in> N" and
    d_cex: "\<not> I_of N \<Turnstile> {D}" and
    d_min: "\<And>C. C \<in> N \<Longrightarrow> C < D \<Longrightarrow> I_of N \<Turnstile> {C}"
    using ex_min_cex by blast
  then obtain \<iota> :: "'f inference" where
    \<iota>_in: "\<iota> \<in> Inf" and
    \<iota>_mprem: "D = main_prem_of \<iota>" and
    sprem_subs_n: "set (side_prems_of \<iota>) \<subseteq> N" and
    sprem_true: "I_of N \<Turnstile> set (side_prems_of \<iota>)" and
    concl_cex: "\<not> I_of N \<Turnstile> {concl_of \<iota>}" and
    concl_lt_d: "concl_of \<iota> < D"
    using Inf_cex_reducing[OF bot_ni_n] not_le by metis
  have "\<iota> \<in> Red_Inf N"
    by (rule subsetD[OF satur[unfolded saturated_def Inf_from_def]], simp add: \<iota>_in)
      (use \<iota>_mprem d_in_n sprem_subs_n in blast)
  then have "\<iota> \<in> Red_Inf N"
    using Red_Inf_without_red_F by blast
  then obtain DD :: "'f set" where
    dd_subs_n: "DD \<subseteq> N" and
    dd_cc_ent_d: "DD \<union> set (side_prems_of \<iota>) \<Turnstile> {concl_of \<iota>}" and
    dd_lt_d: "\<forall>C \<in> DD. C < D"
    unfolding Red_Inf_def redundant_infer_def \<iota>_mprem by blast
  from dd_subs_n dd_lt_d have "I_of N \<Turnstile> DD"
    using d_min by (meson ex_min_cex subset_iff)
  then have "I_of N \<Turnstile> {concl_of \<iota>}"
    using entails_trans dd_cc_ent_d entail_union sprem_true by blast
  then show False
    using concl_cex by auto
qed

end

end
