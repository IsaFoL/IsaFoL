theory Ground_Critical_Pairs
  imports Term_Rewrite_System
begin

definition ground_critical_pairs :: "'f gterm rel \<Rightarrow> 'f gterm rel" where
  "ground_critical_pairs R = {(ctxt\<langle>r\<^sub>2\<rangle>\<^sub>G, r\<^sub>1) | ctxt l r\<^sub>1 r\<^sub>2. (ctxt\<langle>l\<rangle>\<^sub>G, r\<^sub>1) \<in> R \<and> (l, r\<^sub>2) \<in> R}"

abbreviation ground_critical_pair_theorem :: "'f gterm rel \<Rightarrow> bool" where
  "ground_critical_pair_theorem (R :: 'f gterm rel) \<equiv>
    WCR (rewrite_inside_gctxt R) \<longleftrightarrow> ground_critical_pairs R \<subseteq> (rewrite_inside_gctxt R)\<^sup>\<down>"

end