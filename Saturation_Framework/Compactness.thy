(*  Title:       Compactness
    Author:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2014, 2017, 2020
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2014
    Author:      Anders Schlichtkrull <andschl at dtu.dk>, 2017
    Maintainer:  Anders Schlichtkrull <andschl at dtu.dk>
*)

section \<open>Compactness\<close>

theory Compactness
  imports Sound_Inference_Systems
begin

text \<open>
Bachmair and Ganzinger claim that compactness follows from refutational
completeness but leave the proof to the readers' imagination. Our proof relies
on an inductive definition of saturation in terms of a base set of clauses.
\<close>

context inference_system
begin

inductive_set saturate :: "'f set \<Rightarrow> 'f set" for N :: "'f set" where
  base: "C \<in> N \<Longrightarrow> C \<in> saturate N"
| step: "Infer Cs D \<in> Inf \<Longrightarrow> Cs \<in> lists (saturate N) \<Longrightarrow> E \<in> saturate N"

lemma saturate_mono: "C \<in> saturate CC \<Longrightarrow> CC \<subseteq> DD \<Longrightarrow> C \<in> saturate DD"
  by (induct rule: saturate.induct) (auto intro: saturate.intros)

lemma saturated_saturate[simp, intro]: "saturated (saturate N)"
  unfolding saturated_def inferences_from_def infer_from_def image_def
  by clarify (rename_tac x, case_tac x, auto elim!: saturate.step)

lemma saturate_finite: "C \<in> saturate CC \<Longrightarrow> \<exists>DD. DD \<subseteq> CC \<and> finite DD \<and> C \<in> saturate DD"
proof (induct rule: saturate.induct)
  case (base C)
  then have "{C} \<subseteq> CC" and "finite {C}" and "C \<in> saturate {C}"
    by (auto intro: saturate.intros)
  then show ?case
    by blast
next
  case (step CC' D E)
  obtain DD_of where
    "\<And>C. C \<in># CC' \<Longrightarrow> DD_of C \<subseteq> CC \<and> finite (DD_of C) \<and> C \<in> saturate (DD_of C)"
    using step(3) by metis
  then have
    "(\<Union>C \<in> set_mset CC'. DD_of C) \<subseteq> CC"
    "finite (\<Union>C \<in> set_mset CC'. DD_of C) \<and> set_mset CC' \<subseteq> saturate (\<Union>C \<in> set_mset CC'. DD_of C)"
    by (auto intro: saturate_mono)
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
    using in_sat_d in_sat_ee step.hyps(1)
    by (blast intro: inference_system.saturate.step saturate_mono)
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

text \<open>
This result surely holds, but we have yet to prove it. The challenge is: Every time a new clause is
introduced, we also get a new interpretation (by the definition of
\<open>sat_preserving_inference_system\<close>). But the interpretation we want here is then the one that
exists "at the limit". Maybe we can use compactness to prove it.
\<close>

theorem saturate_sat_preserving: "satisfiable CC \<Longrightarrow> satisfiable (saturate CC)"
  oops

end

locale sound_counterex_reducing_inference_system =
  counterex_reducing_inference_system + sound_inference_system
begin

text \<open>
Compactness of clausal logic is stated as Theorem 3.12 for the case of unordered ground resolution.
The proof below is a generalization to any sound counterexample-reducing inference system. The
actual theorem will become available once the locale has been instantiated with a concrete inference
system.
\<close>

theorem clausal_logic_compact:
  fixes N :: "('a :: wellorder) clause set"
  shows "\<not> satisfiable N \<longleftrightarrow> (\<exists>DD \<subseteq> N. finite DD \<and> \<not> satisfiable DD)"
proof
  assume "\<not> satisfiable N"
  then have "{#} \<in> saturate N"
    using saturated_complete saturated_saturate saturate.base unfolding true_clss_def by meson
  then have "\<exists>DD \<subseteq> N. finite DD \<and> {#} \<in> saturate DD"
    using saturate_finite by fastforce
  then show "\<exists>DD \<subseteq> N. finite DD \<and> \<not> satisfiable DD"
    using saturate_sound by auto
next
  assume "\<exists>DD \<subseteq> N. finite DD \<and> \<not> satisfiable DD"
  then show "\<not> satisfiable N"
    by (blast intro: true_clss_mono)
qed

end
