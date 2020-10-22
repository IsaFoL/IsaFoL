(* Title:        Preliminaries of the Splitting Framework
* Author:       Sophie Tourret <stourret at mpi-inf.mpg.de>, 2020 *)

theory Preliminaries
  imports Saturation_Framework.Calculus
begin


locale consequence_relation =
  fixes
    bot :: "'f" and
    entails :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" (infix "\<Turnstile>" 50)
  assumes
    bot_entails_empty: "{bot} \<Turnstile> {}" and
    entails_reflexive: "{C} \<Turnstile> {C}" and
    entails_subsets: "M \<subseteq> N \<Longrightarrow> P \<subseteq> Q \<Longrightarrow> M \<Turnstile> P \<Longrightarrow> N \<Turnstile> Q" and
    entails_each: "M \<Turnstile> N \<Longrightarrow> (\<forall>D\<in>N. M \<union> {D} \<Turnstile> P) \<Longrightarrow> M \<Turnstile> P"
begin

definition entails_conjunctive :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" (infix "\<Turnstile>\<inter>" 50) where
  "M \<Turnstile>\<inter> N \<equiv> \<forall>C\<in>N. M \<Turnstile> {C}"

  sublocale Calculus.consequence_relation "{bot}" "(\<Turnstile>\<inter>)"
proof
  show "{bot} \<noteq> {}" by simp
next
  fix B N
  assume b_in: "B \<in> {bot}"
  then have b_is: "B = bot" by simp
  show "{B} \<Turnstile>\<inter> N"
  proof (cases "N = {}")
    assume n_empty: "N = {}"
    then show "{B} \<Turnstile>\<inter> N"
      unfolding entails_conjunctive_def by blast
  next
    assume n_full: "N \<noteq> {}"
    then obtain C where c_in: "C \<in> N" by blast
    have "{B} \<Turnstile> {C}" sorry
    then show "{B} \<Turnstile>\<inter> N"
      unfolding entails_conjunctive_def using c_in b_is bot_entails_empty entails_subsets by blast
  qed
oops

end


end
    