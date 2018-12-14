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
    entails_excluded_middle: "{} \<Turnstile> {{#Pos A, Neg A#}}" and
    entails_absurd: "{{#Pos A#}, {#Neg A#}} \<Turnstile> {C}" and
    entails_subclause: "C \<subseteq># D \<Longrightarrow> {C} \<Turnstile> {D}"
begin

abbreviation entails_comp_or :: "'a clause set \<Rightarrow> 'a clause set \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>\<squnion>" 50) where
  "M \<Turnstile>\<^sub>\<squnion> CC \<equiv> (\<forall>N D. N \<supseteq> M \<longrightarrow> (\<forall>C \<in> CC. N \<union> {C} \<Turnstile> {D}) \<longrightarrow> N \<Turnstile> {D})"

definition is_propositional :: "'a \<Rightarrow> bool" where
  "is_propositional A \<longleftrightarrow> (\<forall>L C. atm_of L = A \<longrightarrow> {{#L#} + C} \<Turnstile>\<^sub>\<squnion> {{#L#}, C})"

end

end
