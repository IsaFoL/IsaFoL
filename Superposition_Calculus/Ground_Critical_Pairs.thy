theory Ground_Critical_Pairs
  imports
    "Abstract-Rewriting.Relative_Rewriting"
    First_Order_Terms.Term
    Knuth_Bendix_Order.Subterm_and_Context
begin

definition vars_rewrite_rule where
  "vars_rewrite_rule r = vars_term (fst r) \<union> vars_term (snd r)"

definition rewrite_steps where
  "rewrite_steps R = {(ctxt\<langle>t\<^sub>1\<rangle>, ctxt\<langle>t\<^sub>2\<rangle>) | ctxt t\<^sub>1 t\<^sub>2. (t\<^sub>1, t\<^sub>2) \<in> R}"

definition ground_critical_pairs :: "('f, 'v) term rel \<Rightarrow> ('f, 'v) term rel" where
  "ground_critical_pairs R = {(ctxt\<langle>r\<^sub>2\<rangle>, r\<^sub>1) | ctxt l r\<^sub>1 r\<^sub>2. (ctxt\<langle>l\<rangle>, r\<^sub>1) \<in> R \<and> (l, r\<^sub>2) \<in> R}"

locale ground_critical_pair_lemma =
  fixes dummy_fun :: 'f and dummy_var :: 'v
  assumes
    WCR_iff_ground_critical_pairs_subset_join_rewrite_steps: "\<And>(R :: ('f, 'v) term rel).
      (\<Union>r \<in> R. vars_rewrite_rule r) = {} \<Longrightarrow>
      WCR (rewrite_steps R) \<longleftrightarrow> ground_critical_pairs R \<subseteq> (rewrite_steps R)\<^sup>\<down>"

end