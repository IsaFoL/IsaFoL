theory Fold_Extra
  imports Main
begin

lemma comp_fun_idem_conj: "comp_fun_idem_on X (\<and>)"
  by unfold_locales fastforce+

lemma comp_fun_idem_disj: "comp_fun_idem_on X (\<or>)"
  by unfold_locales fastforce+

lemma fold_conj_insert [simp]: 
  "Finite_Set.fold (\<and>) True (insert b B) \<longleftrightarrow> b \<and> Finite_Set.fold (\<and>) True B"
  using comp_fun_idem_on.fold_insert_idem[OF comp_fun_idem_conj]
  by (metis finite top_greatest)

lemma fold_disj_insert [simp]: 
  "Finite_Set.fold (\<or>) False (insert b B) \<longleftrightarrow> b \<or> Finite_Set.fold (\<or>) False B"
  using comp_fun_idem_on.fold_insert_idem[OF comp_fun_idem_disj]
  by (metis finite top_greatest)

end
