theory Ground_Critical_Pairs
  imports TRS.Trs
begin

definition ground_critical_pairs :: "('f, 'v) trs \<Rightarrow> ('f, 'v) rule set" where
  "ground_critical_pairs R = {(ctxt\<langle>r\<^sub>2\<rangle>, r\<^sub>1) | ctxt l r\<^sub>1 r\<^sub>2. (ctxt\<langle>l\<rangle>, r\<^sub>1) \<in> R \<and> (l, r\<^sub>2) \<in> R}"

locale ground_critical_pair_lemma =
  fixes dummy_fun :: 'f and dummy_var :: 'v
  assumes
    WCR_iff_ground_critical_pairs_subset_join_rstep: "\<And>(R :: ('f, 'v) trs).
      vars_trs R = {} \<Longrightarrow> WCR (rstep R) \<longleftrightarrow> ground_critical_pairs R \<subseteq> (rstep R)\<^sup>\<down>"

end