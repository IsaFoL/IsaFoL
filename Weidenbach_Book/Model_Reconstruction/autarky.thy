theory autarky
  imports Entailment_Definition.Partial_Herbrand_Interpretation
    Entailment_Definition.Partial_Annotated_Herbrand_Interpretation
    modelReconstruction
    inprocessingRulesNeu2
    simulation2
begin

(*Ist die Defintion hier richtig?*)
definition autarky :: "'a literal set \<Rightarrow>'a clauses \<Rightarrow> 'a clauses \<Rightarrow> bool " where
"autarky I F Fa = (consistent_interp I \<longrightarrow> ((I \<Turnstile>m Fa) \<and> (\<forall>C \<in># F.  \<not>I \<Turnstile> C \<and> \<not>I \<Turnstile> mset_set(uminus ` set_mset C))))"

lemma autarky_cons:
  assumes "autarky I F Fa" and "consistent_interp I"
  shows "(I \<Turnstile>m Fa) \<and> (\<forall>C \<in># F.  \<not>I \<Turnstile> C \<and> \<not>I \<Turnstile> mset_set(uminus ` set_mset C))"
  using assms unfolding autarky_def by auto

(*Welche Beweismethode ist am besten und stimmt es so wie ich das Lemma aufgeschrieben habe?*)
lemma autarky_simulation: 
  assumes "autarky I N Na" and "consistent_interp I"
  obtains R' S' V' where "rules\<^sup>*\<^sup>*(N + Na, R, S, V \<union> atms_of_mm (N + Na) \<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set S)) (N, R', S@S', V')" and "wit_clause `# mset S' = Na" and "\<forall>I'\<in># (wit_interp `# mset S'). I' \<subseteq> I"
  using assms
proof-
  show ?thesis sorry
qed


end