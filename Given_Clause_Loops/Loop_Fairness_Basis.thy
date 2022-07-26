theory Loop_Fairness_Basis
  imports Coinductive.Coinductive_List
begin

type_synonym 'f strategy = "'f set \<Rightarrow> 'f set"

definition is_strategy_legal :: "'f strategy \<Rightarrow> bool" where
  "is_strategy_legal stgy \<longleftrightarrow> (\<forall>P. stgy P \<subseteq> P) \<and> (\<forall>P. P \<noteq> {} \<longrightarrow> stgy P \<noteq> {})"

definition is_strategy_fair :: "'f strategy \<Rightarrow> bool" where
  "is_strategy_fair stgy \<longleftrightarrow>
   (\<forall>C Ps i. ((\<forall>j \<ge> i. C \<in> lnth Ps j) \<longrightarrow> (\<exists>j \<ge> i. C \<in> stgy (lnth Ps j))))"

end
