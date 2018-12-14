(*  Title:       Preliminaries for Abstract Splitting Architecture
    Author:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2018
*)

section \<open>Preliminaries for Abstract Splitting Architecture\<close>

theory Splitting_Preliminaries
  imports
    Ordered_Resolution_Prover.Clausal_Logic
    "../Saturation_Framework/Saturation_Framework_Preliminaries"
begin

locale clausal_consequence_relation = consequence_relation Bot for Bot :: "'a clause set" +
  assumes
    entails_excluded_middle: "{} \<Turnstile> {{#Pos a, Neg a#}}" and
    entails_absurd: "{{#Pos a#}, {#Neg a#}} \<Turnstile> {C}" and
    entails_subclause: "C \<subseteq># D \<Longrightarrow> {C} \<Turnstile> {D}"
begin

definition entails_comp_sqcup :: "'a clause set \<Rightarrow> 'a clause set \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>\<squnion>" 50) where
  "M \<Turnstile>\<^sub>\<squnion> CC \<longleftrightarrow> (\<forall>N D. N \<Turnstile> M \<longrightarrow> (\<forall>C \<in> CC. N \<union> {C} \<Turnstile> {D}) \<longrightarrow> N \<Turnstile> {D})"

lemma entails_comp_sqcup_trans:
  assumes
    mn: "M \<Turnstile> N" and
    ncc: "N \<Turnstile>\<^sub>\<squnion> CC"
  shows "M \<Turnstile>\<^sub>\<squnion> CC"
  unfolding entails_comp_sqcup_def
  apply clarify
  apply (rename_tac P D)
  apply (rule ncc[unfolded entails_comp_sqcup_def, rule_format])
  using entails_trans mn apply blast
  by blast

definition is_propos :: "'a \<Rightarrow> bool" where
  "is_propos a \<longleftrightarrow> (\<forall>L \<in> {Pos a, Neg a}. \<forall>C. {{#L#} + C} \<Turnstile>\<^sub>\<squnion> {{#L#}, C})"

lemma is_propos_entails_comp_sqcup_excluded_middle:
  assumes prp: "is_propos a"
  shows "{} \<Turnstile>\<^sub>\<squnion> {{#Pos a#}, {#Neg a#}}"
  apply (rule entails_comp_sqcup_trans)
   apply (rule entails_excluded_middle)
  using prp[unfolded is_propos_def, rule_format, of "Pos a" "{#Neg a#}", simplified]
  by (smt add_mset_commute clausal_consequence_relation.entails_comp_sqcup_trans
      clausal_consequence_relation_axioms entails_excluded_middle insert_subset order_refl subset_entailed)

end

end
