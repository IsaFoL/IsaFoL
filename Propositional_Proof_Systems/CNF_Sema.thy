theory CNF_Sema
imports CNF Sema
begin

lemma nnf_semantics: "\<A> \<Turnstile> nnf F \<longleftrightarrow> \<A> \<Turnstile> F"
  by(induction F rule: nnf.induct; simp)

primrec lit_semantics :: "valuation \<Rightarrow> literal \<Rightarrow> bool" where
"lit_semantics \<A> (k\<^sup>+) = \<A> k" |
"lit_semantics \<A> (k\<inverse>) = (\<not>\<A> k)"
case_of_simps lit_semantics_cases: lit_semantics.simps
definition clause_semantics where
  "clause_semantics \<A> s \<equiv> \<exists>l \<in> s. lit_semantics \<A> l"
definition cnf_semantics where
  "cnf_semantics \<A> S \<equiv> \<forall>s \<in> S. clause_semantics \<A> s"

lemma cnf_semantics: "is_nnf F \<Longrightarrow> cnf_semantics \<A> (cnf F) \<longleftrightarrow> \<A> \<Turnstile> F"
  by(induction F rule: cnf.induct; simp add: cnf_semantics_def clause_semantics_def ball_Un; metis Un_iff)
  (* surprisingly, the solvers are smarter if this one is done on mutlisets.*)

lemma cnf_form_semantics: 
  assumes nnf: "is_nnf F"
  shows "\<A> \<Turnstile> (cnf_form_of F) \<longleftrightarrow> \<A> \<Turnstile> F"
proof -
  def cnf_semantics_list \<equiv> "\<lambda>\<A> S. \<forall>s \<in> set S. \<exists>l \<in> set s. lit_semantics \<A> l"
  have tcn: "cnf F = set (map set (cnf_lists F))" using nnf
    by(induction F rule: cnf.induct) (auto simp add: image_UN image_comp comp_def )
  have "\<A> \<Turnstile> F \<longleftrightarrow> cnf_semantics \<A> (cnf F)" using cnf_semantics nnf by simp
  also have "\<dots> = cnf_semantics \<A> (set (map set (cnf_lists F)))" unfolding tcn ..
  also have "\<dots> = cnf_semantics_list \<A> (cnf_lists F)"
    unfolding cnf_semantics_def clause_semantics_def cnf_semantics_list_def by fastforce
  also have "\<dots> = \<A> \<Turnstile> (cnf_form_of F)" using nnf
    by(induction F rule: cnf_lists.induct;
       simp add: cnf_semantics_list_def cnf_form_of_defs  ball_Un bex_Un)
  finally show ?thesis by simp
qed
  
corollary "\<exists>G. \<A> \<Turnstile> F \<longleftrightarrow> \<A> \<Turnstile> G \<and> is_cnf G"
  using cnf_form_of_is cnf_form_semantics is_nnf_nnf nnf_semantics by blast

end
