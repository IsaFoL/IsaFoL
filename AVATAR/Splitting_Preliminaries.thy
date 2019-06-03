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
