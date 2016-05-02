(*  Title:       Refutational Inference Systems
    Author:      Jasmin Blanchette <jasmin.blanchette at inria.fr>, 2014
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2014
    Maintainer:  Jasmin Blanchette <jasmin.blanchette at inria.fr>
*)

section {* Refutational Inference Systems *}

theory Inference_System
imports "../lib/Herbrand_Interpretation"
begin

text {*
This theory gathers results from Section 2.4 (``Refutational Theorem Proving''), 3 (``Standard
Resolution''), and 4.2 (``Counterexample-Reducing Inference Systems'') of Bachmair and Ganzinger's
chapter.
*}


subsection {* Preliminaries *}

text {*
Inferences have one distinguished main premise, any number of side premises, and a conclusion.
*}

datatype 'a inference =
  Infer (side_prems_of: "'a clause multiset") (main_prem_of: "'a clause") (concl_of: "'a clause")

abbreviation concls_of :: "'a inference set \<Rightarrow> 'a clause set" where
  "concls_of \<Gamma> \<equiv> concl_of ` \<Gamma>"

definition infer_from :: "'a clause set \<Rightarrow> 'a inference \<Rightarrow> bool" where
  "infer_from CC \<gamma> \<longleftrightarrow> set_mset (side_prems_of \<gamma>) \<subseteq> CC \<and> main_prem_of \<gamma> \<in> CC"

locale inference_system =
  fixes \<Gamma> :: "'a inference set"
begin

definition inferences_from :: "'a clause set \<Rightarrow> 'a inference set" where
  "inferences_from CC = {\<gamma>. \<gamma> \<in> \<Gamma> \<and> infer_from CC \<gamma>}"

lemma inferences_from_mono: "CC \<subseteq> DD \<Longrightarrow> inferences_from CC \<subseteq> inferences_from DD"
  unfolding inferences_from_def infer_from_def by fast

definition saturated :: "'a clause set \<Rightarrow> bool" where
  "saturated N \<longleftrightarrow> concls_of (inferences_from N) \<subseteq> N"

lemma saturatedD:
  assumes
    satur: "saturated N" and
    inf: "Infer DD C E \<in> \<Gamma>" and
    dd_subs_n: "set_mset DD \<subseteq> N" and
    c_in_n: "C \<in> N"
  shows "E \<in> N"
proof -
  have "Infer DD C E \<in> inferences_from N"
    unfolding inferences_from_def infer_from_def using inf dd_subs_n c_in_n by simp
  hence "E \<in> concls_of (inferences_from N)"
    unfolding image_iff by (metis inference.sel(3))
  thus "E \<in> N"
    using satur unfolding saturated_def by blast
qed

end

text {*
Satisfiability preservation is a weaker requirement than soundness.
*}

locale sat_preserving_inference_system = inference_system +
  assumes \<Gamma>_sat_preserving: "satisfiable N \<Longrightarrow> satisfiable (N \<union> concls_of (inferences_from N))"

locale sound_inference_system = inference_system +
  assumes \<Gamma>_sound: "Infer CC D E \<in> \<Gamma> \<Longrightarrow> I \<Turnstile>m CC \<Longrightarrow> I \<Turnstile> D \<Longrightarrow> I \<Turnstile> E"
begin

lemma \<Gamma>_sat_preserving:
  assumes sat_n: "satisfiable N"
  shows "satisfiable (N \<union> concls_of (inferences_from N))"
proof -
  obtain I where i: "I \<Turnstile>s N"
    using sat_n by blast
  hence "\<And>CC D E. Infer CC D E \<in> \<Gamma> \<Longrightarrow> set_mset CC \<subseteq> N \<Longrightarrow> D \<in> N \<Longrightarrow> I \<Turnstile> E"
    using \<Gamma>_sound unfolding true_clss_def true_cls_mset_def by (simp add: subset_eq)
  hence "\<And>\<gamma>. \<gamma> \<in> \<Gamma> \<Longrightarrow> infer_from N \<gamma> \<Longrightarrow> I \<Turnstile> concl_of \<gamma>"
    unfolding infer_from_def by (case_tac \<gamma>) clarsimp
  hence "I \<Turnstile>s concls_of (inferences_from N)"
    unfolding inferences_from_def image_def true_clss_def infer_from_def by blast
  hence "I \<Turnstile>s N \<union> concls_of (inferences_from N)"
    using i by simp
  thus ?thesis
    by blast
qed

sublocale sat_preserving_inference_system
  by unfold_locales (erule \<Gamma>_sat_preserving)

end

locale reductive_inference_system = inference_system \<Gamma> for \<Gamma> :: "('a :: wellorder) inference set" +
  assumes \<Gamma>_reductive: "\<And>\<gamma>. \<gamma> \<in> \<Gamma> \<Longrightarrow> concl_of \<gamma> #\<subset># main_prem_of \<gamma>"


subsection {* Refutational Completeness *}

text {*
Refutational completeness can be established once and for all for counterexample-reducing inference
systems. The material formalized here draws from both the general framework of Section 4.2 and the
concrete instances of Section 3.

\begin{nit}
The chapter uses the phrase ``true in $N$'' to mean ``true in $I_N$ and element of $N$.'' This is
formalized by the condition @{prop "set_mset DD \<subseteq> N \<and> interp N \<Turnstile>m DD"} below.
\end{nit}
*}

locale counterex_reducing_inference_system =
  inference_system \<Gamma> for \<Gamma> :: "('a :: wellorder) inference set" +
  fixes INTERP :: "'a clause set \<Rightarrow> 'a interp"
  assumes \<Gamma>_counterex_reducing:
    "\<And>N. {#} \<notin> N \<Longrightarrow> C \<in> N \<Longrightarrow> \<not> INTERP N \<Turnstile> C \<Longrightarrow> (\<And>D. D \<in> N \<Longrightarrow> \<not> INTERP N \<Turnstile> D \<Longrightarrow> C #\<subseteq># D) \<Longrightarrow>
       \<exists>DD E. set_mset DD \<subseteq> N \<and> INTERP N \<Turnstile>m DD \<and> Infer DD C E \<in> \<Gamma> \<and> \<not> INTERP N \<Turnstile> E \<and> E #\<subset># C"
begin

lemma ex_min_counterex:
  fixes N :: "('a :: wellorder) clause set"
  assumes "\<not> I \<Turnstile>s N"
  shows "\<exists>C \<in> N. \<not> I \<Turnstile> C \<and> (\<forall>D \<in> N. D #\<subset># C \<longrightarrow> I \<Turnstile> D)"
proof -
  obtain C where "C \<in> N" and "\<not> I \<Turnstile> C"
    using assms unfolding true_clss_def by auto
  hence c_in: "C \<in> {C \<in> N. \<not> I \<Turnstile> C}"
    by blast
  show ?thesis
    using wf_eq_minimal[THEN iffD1, rule_format, OF wf_less_multiset c_in] by blast
qed

(* Theorem 4.4 (generalizes Theorem 3.9) *)

theorem saturated_no_empty_imp_model:
  assumes
    satur: "saturated N" and
    ec_ni_n: "{#} \<notin> N"
  shows "INTERP N \<Turnstile>s N"
proof -
  have ec_ni_n: "{#} \<notin> N"
    using ec_ni_n by auto

  { assume "\<not> INTERP N \<Turnstile>s N"
    then obtain C where
      c_in_n: "C \<in> N" and
      c_cex: "\<not> INTERP N \<Turnstile> C" and
      c_min: "\<And>D. D \<in> N \<Longrightarrow> D #\<subset># C \<Longrightarrow> INTERP N \<Turnstile> D"
      using ex_min_counterex by meson
    then obtain DD E where
      dd_subs_n: "set_mset DD \<subseteq> N" and
      inf_e: "Infer DD C E \<in> \<Gamma>" and
      e_cex: "\<not> INTERP N \<Turnstile> E" and
      e_lt_c: "E #\<subset># C"
      using \<Gamma>_counterex_reducing[OF ec_ni_n] multiset_linorder.not_less by metis
    from dd_subs_n inf_e have "E \<in> N"
      using c_in_n satur by (blast dest: saturatedD)
    hence False
      using e_cex e_lt_c c_min multiset_linorder.not_less by blast }
  thus ?thesis
    by satx
qed

text {*
Cf. Corollary 3.10:
*}

corollary saturated_refute_complete: "saturated N \<Longrightarrow> \<not> satisfiable N \<Longrightarrow> {#} \<in> N"
  by (metis saturated_no_empty_imp_model)

end


subsection {* Compactness *}

text {*
Bachmair and Ganzinger claim that compactness follows from refutational completeness but leave the
proof to the readers' imagination. Our proof relies on an inductive definition of saturation in
terms of a base set of clauses.
*}

context inference_system
begin

inductive_set saturate :: "'a clause set \<Rightarrow> 'a clause set" for CC :: "'a clause set" where
  base: "C \<in> CC \<Longrightarrow> C \<in> saturate CC"
| step: "Infer CC' D E \<in> \<Gamma> \<Longrightarrow> (\<And>C'. C' \<in># CC' \<Longrightarrow> C' \<in> saturate CC) \<Longrightarrow> D \<in> saturate CC \<Longrightarrow>
    E \<in> saturate CC"

lemma saturate_mono: "C \<in> saturate CC \<Longrightarrow> CC \<subseteq> DD \<Longrightarrow> C \<in> saturate DD"
  by (induct rule: saturate.induct) (auto intro: saturate.intros)

lemma saturated_saturate[simp, intro]: "saturated (saturate N)"
  unfolding saturated_def inferences_from_def infer_from_def image_def
  by clarify (rename_tac x, case_tac x, auto elim!: saturate.step)

lemma saturate_imp_finite_subset: "C \<in> saturate CC \<Longrightarrow> \<exists>DD. DD \<subseteq> CC \<and> finite DD \<and> C \<in> saturate DD"
proof (induct rule: saturate.induct)
  case (base C)
  hence "{C} \<subseteq> CC" and "finite {C}" and "C \<in> saturate {C}"
    by (auto intro: saturate.intros)
  thus ?case
    by blast
next
  case (step CC' D E)
  obtain DD_of where
    "\<And>C. C \<in># CC' \<Longrightarrow> DD_of C \<subseteq> CC \<and> finite (DD_of C) \<and> C \<in> saturate (DD_of C)"
    using step(3) by metis
  hence "(\<Union>C \<in> set_mset CC'. DD_of C) \<subseteq> CC \<and>
    finite (\<Union>C \<in> set_mset CC'. DD_of C) \<and> set_mset CC' \<subseteq> saturate (\<Union>C \<in> set_mset CC'. DD_of C)"
    by (auto intro: saturate_mono)
  hence "\<exists>DD \<subseteq> CC. finite DD \<and> set_mset CC' \<subseteq> saturate DD" ..
  then obtain DD where
    d_sub: "DD \<subseteq> CC" and d_fin: "finite DD" and in_sat_d: "set_mset CC' \<subseteq> saturate DD"
    by blast
  obtain EE where
    e_sub: "EE \<subseteq> CC" and e_fin: "finite EE" and in_sat_ee: "D \<in> saturate EE"
    using step(5) by blast
  have "DD \<union> EE \<subseteq> CC"
    using d_sub e_sub step(1) by fast
  moreover have "finite (DD \<union> EE)"
    using d_fin e_fin by fast
  moreover have "E \<in> saturate (DD \<union> EE)"
  proof -
    obtain C_of where
      c_of: "\<And>CC DD :: 'a clause set. \<not> CC \<subseteq> DD \<longrightarrow> C_of CC DD \<in> CC \<and> C_of CC DD \<notin> DD"
      by (metis subsetI)
    hence c_of': "\<And>CC DD EE. C_of CC (DD \<union> EE) \<in> DD \<longrightarrow> CC \<subseteq> DD \<union> EE"
      by (meson Un_iff)
    hence "D \<in> saturate (DD \<union> EE)"
      using c_of by (metis in_sat_ee saturate_mono sup_commute)
    thus ?thesis
      using c_of' c_of in_sat_d step.hyps(1)
      by (meson saturated_saturate saturate_mono saturatedD subsetCE)
  qed
  ultimately show ?case
    by blast
qed

end

context sound_inference_system
begin

theorem saturate_sound: "C \<in> saturate CC \<Longrightarrow> I \<Turnstile>s CC \<Longrightarrow> I \<Turnstile> C"
  by (induct rule: saturate.induct) (auto simp: true_cls_mset_def true_clss_def \<Gamma>_sound)

end

context sat_preserving_inference_system
begin

text {*
This result surely holds, but we have yet to prove it.
*}

theorem saturate_sat_preserving: "satisfiable CC \<Longrightarrow> satisfiable (saturate CC)"
  oops

end

locale sound_counterex_reducing_inference_system =
  counterex_reducing_inference_system + sound_inference_system
begin

text {*
Compactness of clausal logic is stated as Theorem 3.12 for the case of unordered ground resolution.
The proof below is a generalization to any sound counterexample-reducing inference system. The
actual theorem will become available once the locale has been instantiated with a concrete inference
system.
*}

theorem clausal_logic_compact:
  fixes N :: "('a :: wellorder) clause set"
  shows "\<not> satisfiable N \<longleftrightarrow> (\<exists>DD. DD \<subseteq> N \<and> finite DD \<and> \<not> satisfiable DD)"
proof
  assume unsat: "\<not> satisfiable N"
  show "\<exists>DD. DD \<subseteq> N \<and> finite DD \<and> \<not> satisfiable DD"
  proof -
    have "{#} \<in> saturate N"
      using unsat saturated_refute_complete saturated_saturate saturate.base
      unfolding true_clss_mono true_clss_def by meson
    then obtain DD where
      subs: "DD \<subseteq> N" and fin: "finite DD" and ec_in_satur: "{#} \<in> saturate DD"
      using saturate_imp_finite_subset by meson
    from ec_in_satur have "\<not> satisfiable DD"
      by (auto dest: saturate_sound)
    thus ?thesis
      using subs fin by blast
  qed
next
  assume "\<exists>DD. DD \<subseteq> N \<and> finite DD \<and> \<not> satisfiable DD"
  thus "\<not> satisfiable N"
    by (blast intro: true_clss_mono)
qed

end

end
