theory IsaSAT_Clauses
imports IsaSAT_Trail
begin

subsubsection \<open>Representation of Clauses\<close>

text \<open>The representation of clauses relies on two important properties:
  \<^item> the empty clause indicates that the clause is not present.
  \<^item> the elements are accessed through type \<^typ>\<open>nat\<close>.
\<close>

definition list_fmap_rel :: \<open>_ \<Rightarrow> _ \<Rightarrow> ('a list \<times> nat clauses_l) set\<close> where
  list_fmap_rel_internal_def:
  \<open>list_fmap_rel unused R = {(NU', NU). (\<forall>i\<in>#dom_m NU. i < length NU' \<and> (NU'!i, NU \<propto> i) \<in> R) \<and>
         (\<forall>i. i \<notin># dom_m NU \<longrightarrow> i \<ge> length NU' \<or> NU'!i = unused)}\<close>

lemma list_fmap_rel_def:
  \<open>\<langle>R\<rangle>list_fmap_rel unused = {(NU', NU). (\<forall>i\<in>#dom_m NU. i < length NU' \<and> (NU'!i, NU \<propto> i) \<in> R) \<and>
         (\<forall>i. i \<notin># dom_m NU \<longrightarrow> i \<ge> length NU' \<or> NU'!i = unused)}\<close>
  by (simp add: relAPP_def list_fmap_rel_internal_def)

lemma nth_clauses_l:
  \<open>(uncurry (RETURN oo op !), uncurry (RETURN oo (\<lambda>N i. N \<propto> i))) 
    \<in> [\<lambda>(N, i). i \<in># dom_m N]\<^sub>f \<langle>R\<rangle>list_fmap_rel unused \<times>\<^sub>r nat_rel \<rightarrow> \<langle>R\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: list_fmap_rel_def)

abbreviation clauses_l_fmat where
  \<open>clauses_l_fmat \<equiv> list_fmap_rel []\<close>

abbreviation clauses_ll_assn :: \<open>nat clauses_l \<Rightarrow> uint32 array array_list \<Rightarrow> assn\<close> where
  \<open>clauses_ll_assn \<equiv> hr_comp (arlO_assn clause_ll_assn) (\<langle>Id\<rangle>clauses_l_fmat)\<close>


definition nth_rll :: "(nat, 'a literal list \<times> bool) fmap \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a literal" where
  \<open>nth_rll l i j = l \<propto> i ! j\<close>

term nth_rl
end