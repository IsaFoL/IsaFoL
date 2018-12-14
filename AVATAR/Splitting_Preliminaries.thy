(*  Title:       Preliminaries for Abstract Splitting Architecture
    Author:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2018
*)

section \<open>Preliminaries for Abstract Splitting Architecture\<close>

theory Splitting_Preliminaries
  imports
    Ordered_Resolution_Prover.Clausal_Logic
    "../Saturation_Framework/Saturation_Framework_Preliminaries"
begin

context calculus
begin

abbreviation entails_comp_or :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>\<squnion>" 50) where
  "M \<Turnstile>\<^sub>\<squnion> CC \<equiv> (\<forall>N D. N \<supseteq> M \<longrightarrow> (\<forall>C \<in> CC. N \<union> {C} \<Turnstile> D) \<longrightarrow> N \<Turnstile> D)"

end

locale compact_calculus = calculus Bot for Bot :: "'f set" +
  assumes
    Red_F_compact: "C \<in> Red_F N \<Longrightarrow> \<exists>N' \<subseteq> N. finite N' \<and> C \<in> Red_F N'"

end
