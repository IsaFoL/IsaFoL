theory Propo_Superposition
imports Partial_Clausal_Logic "../Bachmair_Ganzinger/Herbrand_Interpretation"
begin
no_notation Herbrand_Interpretation.true_cls (infix "\<Turnstile>" 50)
notation Herbrand_Interpretation.true_cls (infix "\<Turnstile>h" 50)

no_notation Herbrand_Interpretation.true_cls (infix "\<Turnstile>s" 50)
notation Herbrand_Interpretation.true_clss (infix "\<Turnstile>hs" 50)

definition clss_lt :: "'a::wellorder clauses \<Rightarrow> 'a clause \<Rightarrow> 'a clauses" ("_\<^sup>\<prec>\<^sup>_") where
"clss_lt N C = {D \<in> N. D #<# C}"

definition abstract_red :: "'a::wellorder clause \<Rightarrow> 'a clauses \<Rightarrow> bool" where
"abstract_red C N = (clss_lt N C \<Turnstile>p C)"

lemma tautology_is_redundant:
  assumes "tautology C"
  shows "abstract_red C N"
  using assms unfolding abstract_red_def true_clss_cls_def tautology_def by auto
  
lemma subsumed_is_redundant:
  assumes AB: "A \<subset># B"
  and AN: "A \<in> N" and "B \<in> N"
  shows "abstract_red B N"
proof -
  have "A \<in> clss_lt N B" using AN AB unfolding clss_lt_def 
    by (auto dest: less_eq_imp_le_multiset simp add: multiset_order.dual_order.order_iff_strict)
  thus ?thesis
    using AB unfolding abstract_red_def true_clss_cls_def Partial_Clausal_Logic.true_clss_def by blast
qed
  
locale selection =
  fixes S :: "'a clause \<Rightarrow> 'a clause"
  assumes
    S_selects_subseteq: "\<And>C. S C \<le># C" and
    S_selects_neg_lits: "\<And>C L. L \<in># S C \<Longrightarrow> is_neg L"

locale ground_resolution_with_selection =
  selection S for S :: "('a :: wellorder) clause \<Rightarrow> 'a clause"
begin

context
  fixes N :: "'a clause set"
begin

text \<open>We do not create an equivalent of @{term \<delta>}, but we directly defined @{term N\<^sub>C} by inlining the definition.\<close>
function
  production :: "'a clause \<Rightarrow> 'a interp"
where
  "production C =
   {A. C \<in> N \<and> C \<noteq> {#} \<and> Max (set_mset C) = Pos A \<and> \<not> (\<Union>D \<in> {D. D #\<subset># C}. production D) \<Turnstile>h C \<and>
      S C = {#}}"
  by auto
  termination by (relation "{(D, C). D #\<subset># C}") (auto simp: wf_less_multiset)


declare production.simps[simp del]

definition interp :: "'a clause \<Rightarrow> 'a interp" where
  "interp C = (\<Union>D \<in> {D. D #\<subset># C}. production D)"

lemma production_unfold:
  "production C = {A. C \<in> N \<and> C \<noteq> {#} \<and> Max (set_mset C) = Pos A \<and> \<not> interp C \<Turnstile>h C \<and> S C = {#}}"
  unfolding interp_def by (rule production.simps)

abbreviation "productive A \<equiv> (production A \<noteq> {})"

abbreviation produces :: "'a clause \<Rightarrow> 'a \<Rightarrow> bool" where
  "produces C A \<equiv> production C = {A}"

lemma producesD:
  "produces C A \<Longrightarrow> C \<in> N \<and> C \<noteq> {#} \<and> Pos A = Max (set_mset C) \<and> \<not> interp C \<Turnstile>h C \<and> S C = {#}"
  unfolding production_unfold by auto

lemma "produces C A \<Longrightarrow> Pos A \<in># C"
  by (simp add: Max_in_lits producesD)

lemma interp'_def_in_set:
  "interp C = (\<Union>D \<in> {D \<in> N. D #\<subset># C}. production D)"
  unfolding interp_def apply auto
  unfolding production_unfold apply auto
  done
end

definition partial_model :: "'a clauses \<Rightarrow> 'a interp" ("_\<^sub>\<I>") where
"partial_model N = (\<Union>D \<in> {D. D \<in>N}. production N D)"

lemma "partial_model {} =  {}"
  unfolding partial_model_def by auto

lemma
  assumes D: "C+{#-P#} #\<subset># D" 
  shows "ground_resolution_with_selection.production S N D \<noteq> {atm_of P}"
oops

lemma
  assumes "produces N C P"
  shows "partial_model N \<Turnstile>h C"
oops

end

interpretation selection "(\<lambda>_. {#})"
  by standard auto


interpretation ground_resolution_with_selection "(\<lambda>_. {#})"
  by standard auto

end