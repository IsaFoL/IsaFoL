(*  Title:       Preliminaries for Abstract Splitting Architecture
    Author:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2018
*)

section \<open>Preliminaries for Abstract Splitting Architecture\<close>

theory Splitting_Preliminaries
  imports
    Ordered_Resolution_Prover.Clausal_Logic
begin

locale nonclausal_consequence_relation =
  fixes
    bot :: 'f and
    entails :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" (infix "\<Turnstile>" 50)
  assumes
    bot_implies_all: "{bot} \<Turnstile> N1" and
    subset_entailed: "N2 \<subseteq> N1 \<Longrightarrow> N1 \<Turnstile> N2" and
    all_formulas_entailed [intro]: "(\<forall>C \<in> N2. N1 \<Turnstile> {C}) \<Longrightarrow> N1 \<Turnstile> N2" and
    entails_trans [trans]: "N1 \<Turnstile> N2 \<Longrightarrow> N2 \<Turnstile> N3 \<Longrightarrow> N1 \<Turnstile> N3" and
    nothing_nimplies_bot:  "\<not> {} \<Turnstile> {bot}"
begin

lemma entail_iff_each: "N1 \<Turnstile> N2 \<longleftrightarrow> (\<forall>C \<in> N2. N1 \<Turnstile> {C})"
  by (meson all_formulas_entailed bot.extremum entails_trans insert_subsetI subset_entailed)

lemma entails_bigunion_iff: "N \<Turnstile> (\<Union>i \<in> I. M i) \<longleftrightarrow> (\<forall>i \<in> I. N \<Turnstile> M i)"
  by (smt UN_iff entail_iff_each)

end

locale clausal_consequence_relation = nonclausal_consequence_relation "{#}" +
  assumes
    entails_excluded_middle: "{} \<Turnstile> {{#Pos a, Neg a#}}" and
    entails_absurd: "{{#Pos a#}, {#Neg a#}} \<Turnstile> {C}" and
    entails_subclause: "C \<subseteq># D \<Longrightarrow> {C} \<Turnstile> {D}"
begin

lemma entails_weaken_subclause:
  assumes stronger: "N \<union> {C1 + C2} \<Turnstile> C3"
  shows "N \<union> {C1} \<Turnstile> C3"
proof -
  have "N \<union> {C1} \<Turnstile> {C1}"
    by (simp add: subset_entailed)
  moreover have "{C1} \<Turnstile> {C1 + C2}"
    by (simp add: entails_subclause) 
  ultimately have "N \<union> {C1} \<Turnstile> {C1 + C2}"
    using entails_trans by blast

  hence "N \<union> {C1} \<Turnstile> N \<union> {C1 + C2}"
    by (metis Un_iff bot.extremum entail_iff_each insert_subset subset_entailed)
  thus "N \<union> {C1} \<Turnstile> C3"
    using entails_trans stronger by blast
qed

definition entails_comp_sqcup :: "'a clause set \<Rightarrow> 'a clause set \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>\<squnion>" 50) where
  "M \<Turnstile>\<^sub>\<squnion> CC \<longleftrightarrow> (\<forall>N D. N \<Turnstile> M \<longrightarrow> (\<forall>C \<in> CC. N \<union> {C} \<Turnstile> {D}) \<longrightarrow> N \<Turnstile> {D})"

lemma entails_comp_sqcup_trans:
  assumes
    mn: "M \<Turnstile> N" and
    ncc: "N \<Turnstile>\<^sub>\<squnion> CC"
  shows "M \<Turnstile>\<^sub>\<squnion> CC"
  unfolding entails_comp_sqcup_def
  by (clarify, rule ncc[unfolded entails_comp_sqcup_def, rule_format])
    (blast intro: entails_trans mn)+

definition is_propos :: "'a \<Rightarrow> bool" where
  "is_propos a \<longleftrightarrow> (\<forall>L \<in> {Pos a, Neg a}. \<forall>C. {{#L#} + C} \<Turnstile>\<^sub>\<squnion> {{#L#}, C})"

lemma is_propos_entails_comp_sqcup_excluded_middle:
  assumes prp: "is_propos a"
  shows "{} \<Turnstile>\<^sub>\<squnion> {{#Pos a#}, {#Neg a#}}"
  using prp[unfolded is_propos_def, rule_format, of "Pos a" "{#Neg a#}", simplified]
  by (metis (no_types) add_mset_commute entails_comp_sqcup_trans entails_excluded_middle)

end

locale abstraction_function = clausal_consequence_relation +
  fixes
    \<alpha> :: "'a clause \<Rightarrow> 'a literal set" and
    \<alpha>s  :: "'a clause set \<Rightarrow> 'a literal set"
  assumes
    \<alpha>_propos: "\<forall>L \<in> \<alpha> C. is_propos (atm_of L)" and
    \<alpha>s_def: "\<alpha>s N = {L. \<exists>C \<in> N. L \<in> \<alpha> C}" and
    \<alpha>_literal: "M \<union> {mset_set (\<alpha>s N)} \<Turnstile> {{#L#}} \<Longrightarrow> M \<union> N \<Turnstile> {C}" and
    \<alpha>_clause: "M \<union> {mset_set (\<alpha>s N)} \<Turnstile> {C} \<Longrightarrow> M \<union> N \<Turnstile> {C}"
begin

lemma \<alpha>s_empty: "\<alpha>s {} = {}"
  by (simp add: \<alpha>s_def)

lemma \<alpha>s_inter_imp_entails:
  assumes in_inter: "L \<in> \<alpha> C \<inter> \<alpha> D"
  shows "{C} \<Turnstile> {D}"
proof -
  have False (* "{mset_set (\<alpha> C)} \<Turnstile> {{#L#}}" *)
    by (metis (no_types) \<alpha>s_empty Un_insert_right \<alpha>_clause entails_subclause mset_set.empty nothing_nimplies_bot subset_mset.le_zero_eq sup_bot.right_neutral)


  thm \<alpha>_literal[of "{}" "{C}" L D, unfolded \<alpha>s_def, simplified]
qed

end

end
