theory Maximal_Literal
  imports 
    Clausal_Calculus_Extra
    Min_Max_Least_Greatest_Multiset 
    Restricted_Order
begin

locale maximal_literal = order: strict_order where less = less 
for less :: "'a literal \<Rightarrow> 'a literal \<Rightarrow> bool"
begin

abbreviation is_maximal :: "'a literal \<Rightarrow> 'a clause \<Rightarrow> bool" where
  "is_maximal l C \<equiv> order.is_maximal_in_mset C l"

abbreviation is_strictly_maximal :: "'a literal \<Rightarrow> 'a clause \<Rightarrow> bool" where
  "is_strictly_maximal l C \<equiv> order.is_strictly_maximal_in_mset C l"

lemmas is_maximal_def = order.is_maximal_in_mset_iff

lemmas is_strictly_maximal_def = order.is_strictly_maximal_in_mset_iff

lemmas is_maximal_if_is_strictly_maximal = order.is_maximal_in_mset_if_is_strictly_maximal_in_mset

lemma maximal_in_clause:
  assumes "is_maximal l C"
  shows "l \<in># C"
  using assms 
  unfolding is_maximal_def
  by(rule conjunct1)

lemma strictly_maximal_in_clause:
  assumes "is_strictly_maximal l C"
  shows "l \<in># C"
  using assms  
  unfolding is_strictly_maximal_def
  by(rule conjunct1)

(* TODO: Names *)
lemma is_maximal_empty [intro]: "is_maximal l C \<Longrightarrow> C \<noteq> {#}"  
  using maximal_in_clause
  by fastforce

lemma is_strictly_maximal_empty [intro]: "is_strictly_maximal l C \<Longrightarrow> C \<noteq> {#}"
  using strictly_maximal_in_clause
  by fastforce

end

end
