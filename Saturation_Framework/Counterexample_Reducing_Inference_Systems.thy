(*  Title:       Counterexample-Reducing Inference Systems
    Author:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2014, 2017, 2020
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2014
    Author:      Anders Schlichtkrull <andschl at dtu.dk>, 2017
    Maintainer:  Jasmin Blanchette <j.c.blanchette at vu.nl>
*)

section \<open>Counterexample-Reducing Inference Systems\<close>

theory Counterexample_Reducing_Inference_Systems
  imports
    Saturation_Framework.Calculi
    "HOL-Library.Multiset_Order"
begin

text \<open>
Refutational completeness can be established once and for all for counterexample-reducing inference
systems. The material formalized here draws from both the general framework of Section 4.2 and the
concrete instances of Section 3.
\<close>

abbreviation main_prem_of :: "'f inference \<Rightarrow> 'f" where
  "main_prem_of \<iota> \<equiv> last (prems_of \<iota>)"

abbreviation side_prems_of :: "'f inference \<Rightarrow> 'f list" where
  "side_prems_of \<iota> \<equiv> butlast (prems_of \<iota>)"

lemma set_prems_of[simp]:
  "set (prems_of \<iota>) = (if prems_of \<iota> = [] then {} else {main_prem_of \<iota>} \<union> set (side_prems_of \<iota>))"
  by clarsimp (metis Un_insert_right append_Nil2 append_butlast_last_id list.set(2) set_append)

locale cex_red_inference_system = inference_system Inf + consequence_relation
  for Inf :: "('f :: wellorder) inference set" +
  fixes I_of :: "'f set \<Rightarrow> 'f set"
  assumes Inf_cex_reducing:
    "N \<inter> Bot = {} \<Longrightarrow> D \<in> N \<Longrightarrow> \<not> I_of N \<Turnstile> {D} \<Longrightarrow> (\<And>C. C \<in> N \<Longrightarrow> \<not> I_of N \<Turnstile> {C} \<Longrightarrow> D \<le> C) \<Longrightarrow>
     \<exists>\<iota> \<in> Inf. main_prem_of \<iota> = D \<and> set (side_prems_of \<iota>) \<subseteq> N \<and> I_of N \<Turnstile> set (side_prems_of \<iota>) \<and>
       \<not> I_of N \<Turnstile> {concl_of \<iota>} \<and> concl_of \<iota> < D"
begin

lemma ex_min_cex:
  fixes N :: "('f :: wellorder) set"
  assumes "\<not> I \<Turnstile> N"
  shows "\<exists>C \<in> N. \<not> I \<Turnstile> {C} \<and> (\<forall>D \<in> N. D < C \<longrightarrow> I \<Turnstile> {D})"
proof -
  obtain C :: 'f where
    "C \<in> N" and "\<not> I \<Turnstile> {C}"
    using assms all_formulas_entailed by blast
  then have c_in: "C \<in> {C \<in> N. \<not> I \<Turnstile> {C}}"
    by blast
  show ?thesis
    using wf_eq_minimal[THEN iffD1, rule_format, OF wellorder_class.wf c_in] by blast
qed

end

text \<open>
Theorem 4.4 (generalizes Theorems 3.9 and 3.16):
\<close>

locale cex_red_inference_system_with_triv_red_crit =
  cex_red_inference_system _ _ Inf + calculus_with_red_crit _ Inf _ "\<lambda>_. {}" "\<lambda>_. {}"
  for Inf :: "('f :: wellorder) inference set"
begin

theorem saturated_model:
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
    by (meson ex_min_cex)
  then obtain \<iota> :: "'f inference" where
    \<iota>_inf: "\<iota> \<in> Inf" and
    concl_cex: "\<not> I_of N \<Turnstile> {concl_of \<iota>}" and
    concl_lt_d: "concl_of \<iota> < D"
    using Inf_cex_reducing[OF bot_ni_n] by fastforce
  have "concl_of \<iota> \<in> N"
    using \<iota>_inf Red_Inf_of_Inf_to_N by blast
  then show False
    using concl_cex concl_lt_d d_min by blast
qed

text \<open>
An abstract version of Corollary 3.10 does not hold without some conditions, according to Nitpick:
\<close>

corollary saturated_complete:
  assumes
    satur: "saturated N" and
    unsat: "N \<Turnstile> Bot"
  shows "N \<inter> Bot \<noteq> {}"
  oops

end

end
