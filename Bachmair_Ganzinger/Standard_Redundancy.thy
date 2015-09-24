(*  Title:       The Standard Redundancy Criterion
    Author:      Jasmin Blanchette <jasmin.blanchette at inria.fr>, 2014
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2014
    Maintainer:  Jasmin Blanchette <jasmin.blanchette at inria.fr>
*)

section {* The Standard Redundancy Criterion *}

theory Standard_Redundancy
imports Proving_Process
begin

text {*
This material is based on Section 4.2.2 (``The Standard Redundancy Criterion'') of Bachmair and
Ganzinger's chapter.
*}

locale standard_redundancy_criterion = counterex_reducing_inference_system
begin

abbreviation redundant_infer :: "'a clause set \<Rightarrow> 'a inference \<Rightarrow> bool" where
  "redundant_infer N \<gamma> \<equiv>
   \<exists>DD. set_mset DD \<subseteq> N \<and> (\<forall>I. I \<Turnstile>m DD + side_prems_of \<gamma> \<longrightarrow> I \<Turnstile> concl_of \<gamma>) \<and>
     (\<forall>D. D \<in># DD \<longrightarrow> D #\<subset># main_prem_of \<gamma>)"

definition Rf :: "'a clause set \<Rightarrow> 'a clause set" where
  "Rf N = {C. \<exists>DD. set_mset DD \<subseteq> N \<and> (\<forall>I. I \<Turnstile>m DD \<longrightarrow> I \<Turnstile> C) \<and> (\<forall>D. D \<in># DD \<longrightarrow> D #\<subset># C)}"

definition Ri :: "'a clause set \<Rightarrow> 'a inference set" where
  "Ri N = {\<gamma> \<in> \<Gamma>. redundant_infer N \<gamma>}"

text {*
The following results correspond to Lemma 4.5. The lemma @{text assume_non_Rf} generalizes the core
of the argument.
*}

lemma Rf_mono: "N \<subseteq> N' \<Longrightarrow> Rf N \<subseteq> Rf N'"
  unfolding Rf_def by auto

lemma assume_non_Rf:
  assumes ex: "\<exists>CC. set_mset CC \<subseteq> N \<and> (\<forall>I. I \<Turnstile>m CC + EE \<longrightarrow> I \<Turnstile> E) \<and> (\<forall>C'. C' \<in># CC \<longrightarrow> C' #\<subset># C)"
  shows "\<exists>CC. set_mset CC \<subseteq> N - Rf N \<and> (\<forall>I. I \<Turnstile>m CC + EE \<longrightarrow> I \<Turnstile> E) \<and> (\<forall>C'. C' \<in># CC \<longrightarrow> C' #\<subset># C)"
proof -
  from ex obtain CC0 where
    cc0: "CC0 \<in> {CC. set_mset CC \<subseteq> N \<and> (\<forall>I. I \<Turnstile>m CC + EE \<longrightarrow> I \<Turnstile> E) \<and> (\<forall>C'. C' \<in># CC \<longrightarrow> C' #\<subset># C)}"
    by blast
  have "\<exists>CC. set_mset CC \<subseteq> N \<and> (\<forall>I. I \<Turnstile>m CC + EE \<longrightarrow> I \<Turnstile> E) \<and> (\<forall>C'. C' \<in># CC \<longrightarrow> C' #\<subset># C) \<and>
      (\<forall>CC'. set_mset CC' \<subseteq> N \<and> (\<forall>I. I \<Turnstile>m CC' + EE \<longrightarrow> I \<Turnstile> E) \<and> (\<forall>C'. C' \<in># CC' \<longrightarrow> C' #\<subset># C) \<longrightarrow>
    CC #\<subseteq>## CC')"
    using wf_eq_minimal[THEN iffD1, rule_format, OF wf_less_mset_mset cc0]
    unfolding multiset_multiset_linorder.not_less[symmetric] by blast
  then obtain CC where
    cc_subs_n: "set_mset CC \<subseteq> N" and
    cc_imp_c: "\<forall>I. I \<Turnstile>m CC + EE \<longrightarrow> I \<Turnstile> E" and
    cc_lt_c: "\<forall>C'. C' \<in># CC \<longrightarrow> C' #\<subset># C" and
    c_min: "\<forall>CC'. set_mset CC' \<subseteq> N \<and> (\<forall>I. I \<Turnstile>m CC' + EE \<longrightarrow> I \<Turnstile> E) \<and> (\<forall>C'. C' \<in># CC' \<longrightarrow> C' #\<subset># C) \<longrightarrow>
      CC #\<subseteq>## CC'"
    by blast
  have "\<forall>D. D \<in># CC \<longrightarrow> D \<notin> Rf N"
  proof clarify
    fix D
    assume d_in_cc: "D \<in># CC" and d_rf: "D \<in> Rf N"
    from d_rf obtain CC' where
      cc'_subs_n: "set_mset CC' \<subseteq> N" and
      cc'_imp_d: "\<forall>I. I \<Turnstile>m CC' \<longrightarrow> I \<Turnstile> D" and
      cc'_lt_d: "\<forall>C'. C' \<in># CC' \<longrightarrow> C' #\<subset># D"
      unfolding Rf_def by blast
    def DD \<equiv> "CC - {#D#} + CC'"
    have "set_mset DD \<subseteq> N"
      unfolding DD_def using cc_subs_n cc'_subs_n by auto
    moreover have "\<forall>I. I \<Turnstile>m DD + EE \<longrightarrow> I \<Turnstile> E"
      using cc'_imp_d cc_imp_c unfolding DD_def true_cls_mset_def by auto blast
    moreover have "\<forall>C'. C' \<in># DD \<longrightarrow> C' #\<subset># C"
      using cc_lt_c cc'_lt_d d_in_cc unfolding DD_def
      by (auto intro: multiset_order.less_trans[rule_format])
    moreover have "DD #\<subset>## CC"
      unfolding DD_def
      proof (rule union_less_mset_mset_diff_plus)
        show "{#D#} \<le># CC"
          using d_in_cc by (metis insert_DiffM mset_le_exists_conv)
      next
        show "CC' #\<subset>## {#D#}"
          using cc'_lt_d ex_gt_imp_less_mset_mset unfolding Bex_mset_def 
          by (metis multi_member_last)
      qed
    ultimately show False
      using c_min multiset_multiset_order.antisym unfolding le_mset_mset_def by blast
  qed
  thus ?thesis
    using cc_subs_n cc_imp_c cc_lt_c by auto
qed

lemma Rf_imp_ex_non_Rf:
  assumes "C \<in> Rf N"
  shows "\<exists>CC. set_mset CC \<subseteq> N - Rf N \<and> (\<forall>I. I \<Turnstile>m CC \<longrightarrow> I \<Turnstile> C) \<and> (\<forall>C'. C' \<in># CC \<longrightarrow> C' #\<subset># C)"
proof (rule assume_non_Rf[of _ "{#}", simplified])
  show "\<exists>CC. set_mset CC \<subseteq> N \<and> (\<forall>I. I \<Turnstile>m CC \<longrightarrow> I \<Turnstile> C) \<and> (\<forall>C'. C' \<in># CC \<longrightarrow> C' #\<subset># C)"
    using assms unfolding Rf_def by blast
qed

lemma Rf_subs_Rf_diff_Rf: "Rf N \<subseteq> Rf (N - Rf N)"
proof
  fix C
  assume c_rf: "C \<in> Rf N"
  then obtain CC where
    cc_subs: "set_mset CC \<subseteq> N - Rf N" and
    cc_imp_c: "\<forall>I. I \<Turnstile>m CC \<longrightarrow> I \<Turnstile> C" and
    cc_lt_c: "\<forall>C'. C' \<in># CC \<longrightarrow> C' #\<subset># C"
    using Rf_imp_ex_non_Rf by blast
  have "\<forall>D. D \<in># CC \<longrightarrow> D \<notin> Rf N"
    using cc_subs by (simp add: subset_iff)
  hence cc_nr:
    "\<And>C DD. C \<in># CC \<Longrightarrow> set_mset DD \<subseteq> N \<Longrightarrow> \<forall>I. I \<Turnstile>m DD \<longrightarrow> I \<Turnstile> C \<Longrightarrow> \<exists>D. D \<in># DD \<and> ~ D #\<subset># C"
      unfolding Rf_def by auto metis
  have "set_mset CC \<subseteq> N"
    using cc_subs by auto
  hence "set_mset CC \<subseteq> N - {C. \<exists>DD. set_mset DD \<subseteq> N \<and> (\<forall>I. I \<Turnstile>m DD \<longrightarrow> I \<Turnstile> C) \<and> (\<forall>D. D \<in># DD \<longrightarrow> D #\<subset># C)}"
    using cc_nr by auto blast
  thus "C \<in> Rf (N - Rf N)"
    using cc_imp_c cc_lt_c unfolding Rf_def by auto
qed

lemma Rf_eq_Rf_diff_Rf: "Rf N = Rf (N - Rf N)"
  by (metis Diff_subset Rf_mono Rf_subs_Rf_diff_Rf subset_antisym)

text {*
The following results correspond to Lemma 4.6.

\begin{nit}
Lemma 4.6 does not seem to be derivable from Lemma 4.5, unlike what the chapter claims. Instead, it
appears necessary to generalize the argument of Lemma 4.5 (cf.\ the @{thm [source] assume_non_Rf}
lemma).
\end{nit}
*}

lemma Ri_mono: "N \<subseteq> N' \<Longrightarrow> Ri N \<subseteq> Ri N'"
  unfolding Ri_def by auto

lemma Ri_subs_Ri_diff_Rf: "Ri N \<subseteq> Ri (N - Rf N)"
proof
  fix \<gamma>
  assume \<gamma>_ri: "\<gamma> \<in> Ri N"
  then obtain CC C D where \<gamma>: "\<gamma> = Infer CC C D"
    by (cases \<gamma>)
  have cc: "CC = side_prems_of \<gamma>" and c: "C = main_prem_of \<gamma>" and d: "D = concl_of \<gamma>"
    unfolding \<gamma> by simp_all
  obtain DD where
    "set_mset DD \<subseteq> N" and "\<forall>I. I \<Turnstile>m DD + CC \<longrightarrow> I \<Turnstile> D" and "\<forall>D. D \<in># DD \<longrightarrow> D #\<subset># C"
    using \<gamma>_ri unfolding Ri_def cc c d by blast
  then obtain DD' where
    "set_mset DD' \<subseteq> N - Rf N" and "\<forall>I. I \<Turnstile>m DD' + CC \<longrightarrow> I \<Turnstile> D" and "\<forall>D'. D' \<in># DD' \<longrightarrow> D' #\<subset># C"
    using assume_non_Rf by atomize_elim blast
  thus "\<gamma> \<in> Ri (N - Rf N)"
    using \<gamma>_ri unfolding Ri_def c cc d by blast
qed

lemma Ri_eq_Ri_diff_Rf: "Ri N = Ri (N - Rf N)"
  by (metis Diff_subset Ri_mono Ri_subs_Ri_diff_Rf subset_antisym)
  
lemma Ri_subset_\<Gamma>: "Ri N \<subseteq> \<Gamma>"
  unfolding Ri_def by blast

lemma Rf_indep: "N' \<subseteq> Rf N \<Longrightarrow> Rf N \<subseteq> Rf (N - N')"
  by (metis Diff_cancel Diff_eq_empty_iff Diff_mono Rf_eq_Rf_diff_Rf Rf_mono)
  
lemma Ri_indep: "N' \<subseteq> Rf N \<Longrightarrow> Ri N \<subseteq> Ri (N - N')"
  by (metis Diff_mono Ri_eq_Ri_diff_Rf Ri_mono order_refl)

lemma Rf_true:
  assumes "I \<Turnstile>s N - Rf N"
  shows "I \<Turnstile>s N"
proof -
  have "I \<Turnstile>s Rf (N - Rf N)"
    unfolding true_clss_def
    by (subst Rf_def) (auto, metis assms mem_set_mset_iff subset_eq true_cls_mset_def true_clss_def)
  hence "I \<Turnstile>s Rf N"
    using Rf_subs_Rf_diff_Rf true_clss_mono by blast
  thus ?thesis
    using assms by (metis Un_Diff_cancel true_clss_union)
qed

lemma Rf_sat: "satisfiable (N - Rf N) \<Longrightarrow> satisfiable N"
  by (metis Rf_true)

text {*
The following corresponds to Theorem 4.7:
*}

sublocale redundancy_criterion \<Gamma> Rf Ri
  by unfold_locales (rule Ri_subset_\<Gamma>, (elim Rf_mono Ri_mono Rf_indep Ri_indep Rf_sat)+)

text {*
The following result corresponds to Theorem 4.9. (The ``if'' direction is omitted because trivial.)

\begin{nit}
The invocation of Lemma 4.5 does not fit. What is needed is a generalized version of Lemma 4.6.
\end{nit}
*}

theorem saturated_upto_refute_complete:
  assumes
    satur: "saturated_upto N" and
    unsat: "\<not> satisfiable N"
  shows "{#} \<in> N"
proof (rule ccontr)
  assume ec_ni_n: "{#} \<notin> N"
  def M \<equiv> "N - Rf N"
  have ec_ni_m: "{#} \<notin> M"
    unfolding M_def using ec_ni_n by fast
  have "INTERP M \<Turnstile>s M"
  proof (rule ccontr)
    assume "\<not> INTERP M \<Turnstile>s M"
    then obtain C where
      c_in_m: "C \<in> M" and
      c_cex: "\<not> INTERP M \<Turnstile> C" and
      c_min: "\<And>D. D \<in> M \<Longrightarrow> D #\<subset># C \<Longrightarrow> INTERP M \<Turnstile> D"
      using ex_min_counterex by meson
    then obtain \<gamma> CC D where
      \<gamma>: "\<gamma> = Infer CC C D" and
      cc_subs_m: "set_mset CC \<subseteq> M" and
      cc_true: "INTERP M \<Turnstile>m CC" and
      \<gamma>_in: "\<gamma> \<in> \<Gamma>" and
      d_cex: "\<not> INTERP M \<Turnstile> D" and
      d_lt_c: "D #\<subset># C"
      using \<Gamma>_counterex_reducing[OF ec_ni_m] multiset_linorder.not_less by metis
    have cc: "CC = side_prems_of \<gamma>" and c: "C = main_prem_of \<gamma>" and d: "D = concl_of \<gamma>"
      unfolding \<gamma> by simp_all
    have "\<gamma> \<in> Ri N"
      by (rule set_mp[OF satur[unfolded saturated_upto_def inferences_from_def infer_from_def]])
        (simp add: \<gamma>_in c_in_m cc_subs_m cc[symmetric] c[symmetric] d[symmetric] M_def[symmetric])
    hence "\<gamma> \<in> Ri M"
      unfolding M_def using Ri_subs_Ri_diff_Rf by fast
    then obtain DD where
      dd_subs_m: "set_mset DD \<subseteq> M" and
      dd_cc_imp_d: "\<forall>I. I \<Turnstile>m DD + CC \<longrightarrow> I \<Turnstile> D" and
      dd_lt_c: "\<forall>D. D \<in># DD \<longrightarrow> D #\<subset># C"
      unfolding Ri_def cc c d by blast
    from dd_subs_m dd_lt_c have "INTERP M \<Turnstile>m DD"
      using c_min unfolding true_cls_mset_def by (metis contra_subsetD mem_set_mset_iff)
    hence "INTERP M \<Turnstile> D"
      using dd_cc_imp_d cc_true by auto
    thus False
      using d_cex by auto
  qed
  hence "INTERP M \<Turnstile>s N"
    using M_def Rf_true by blast
  thus False
    using unsat by blast
qed

lemma redudancy_criterion: "redundancy_criterion \<Gamma> Rf Ri" ..

end

locale standard_redundancy_criterion_reductive =
  standard_redundancy_criterion + reductive_inference_system
begin

text {*
The following corresponds to Theorem 4.8:
*}

sublocale effective_redundancy_criterion \<Gamma> Rf Ri
unfolding effective_redundancy_criterion_def
proof (intro conjI redudancy_criterion, unfold_locales)
  fix \<gamma> N
  assume in_\<gamma>: "\<gamma> \<in> \<Gamma>" and concl_of_in_n_un_rf_n: "concl_of \<gamma> \<in> N \<union> Rf N"
  obtain CC D E where \<gamma>: "\<gamma> = Infer CC D E"  
    by (cases \<gamma>)
  hence cc: "CC = side_prems_of \<gamma>" and d: "D = main_prem_of \<gamma>" and e: "E = concl_of \<gamma>"
    unfolding \<gamma> by simp_all
  note e_in_n_un_rf_n = concl_of_in_n_un_rf_n[folded e]

  { assume "E \<in> N"
    moreover have "E #\<subset># D"
      using \<Gamma>_reductive e d in_\<gamma> by auto
    ultimately have
      "set_mset {#E#} \<subseteq> N" and "\<forall>I. I \<Turnstile>m {#E#} + CC \<longrightarrow> I \<Turnstile> E" and "\<forall>D'. D' \<in># {#E#} \<longrightarrow> D' #\<subset># D"
      by simp_all
    hence "redundant_infer N \<gamma>"
      using cc d e by blast }
  moreover
  { assume "E \<in> Rf N"
    then obtain DD where
      dd_sset: "set_mset DD \<subseteq> N" and
      dd_imp_e: "\<forall>I. I \<Turnstile>m DD \<longrightarrow> I \<Turnstile> E" and
      dd_lt_e: "\<forall>C'. C' \<in># DD \<longrightarrow> C' #\<subset># E"
      unfolding Rf_def by blast
    from dd_lt_e have "\<forall>Da. Da \<in># DD \<longrightarrow> Da #\<subset># D"
      using d e in_\<gamma> \<Gamma>_reductive mult_less_trans by blast
    hence "redundant_infer N \<gamma>"
      using dd_sset dd_imp_e cc d e by blast }
  ultimately show "\<gamma> \<in> Ri N"
    using in_\<gamma> e_in_n_un_rf_n unfolding Ri_def by blast
qed

end

end
