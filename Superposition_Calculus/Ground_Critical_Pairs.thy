theory Ground_Critical_Pairs
  imports TRS.Trs
begin

definition ground_critical_pairs :: "('f, 'v) trs \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) rule set" where
  "ground_critical_pairs P R = { (ctxt\<langle>r\<^sub>R\<rangle>, r\<^sub>P) | ctxt l r\<^sub>P r\<^sub>R. (ctxt\<langle>l\<rangle>, r\<^sub>P) \<in> P \<and> (l, r\<^sub>R) \<in> R}"

locale ground_critical_pair_lemma =
  fixes dummy_fun :: 'f and dummy_var :: 'v
  assumes
    WCR_iff_ground_critical_pairs_subset_join_rstep: "\<And>(R :: ('f, 'v) trs).
      vars_trs R = {} \<Longrightarrow> WCR (rstep R) \<longleftrightarrow> ground_critical_pairs R R \<subseteq> (rstep R)\<^sup>\<down>"

end