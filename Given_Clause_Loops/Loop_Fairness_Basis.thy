theory Loop_Fairness_Basis
  imports Main
begin

type_synonym 'f strategy = "'f set \<Rightarrow> 'f set"

definition is_strategy_legal :: "'f strategy \<Rightarrow> bool" where
  "is_strategy_legal stgy \<longleftrightarrow> (\<forall>P. stgy P \<subseteq> P) \<and> (\<forall>P. P \<noteq> {} \<longrightarrow> stgy P \<noteq> {})"

inductive strategy_step :: "'f strategy \<Rightarrow> 'f set \<Rightarrow> 'f set \<Rightarrow> 'f set \<Rightarrow> bool"
    for stgy :: "'f strategy" where
  "C \<in> stgy P \<Longrightarrow> strategy_step stgy P (P - {C}) ((P - {C}) \<union> N)"

definition is_strategy_fair :: "'f strategy \<Rightarrow> bool" where
  "is_strategy_fair stgy \<longleftrightarrow> "

end
