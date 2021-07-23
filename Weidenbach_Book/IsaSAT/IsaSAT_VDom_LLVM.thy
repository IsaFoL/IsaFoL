theory IsaSAT_VDom_LLVM
  imports IsaSAT_VDom IsaSAT_Stats_LLVM IsaSAT_Clauses_LLVM IsaSAT_Arena_Sorting_LLVM
begin

abbreviation aivdom_int_rel :: \<open>(aivdom \<times> aivdom) set\<close> where
  \<open>aivdom_int_rel \<equiv> \<langle>Id\<rangle>list_rel \<times>\<^sub>r \<langle>Id\<rangle>list_rel \<times>\<^sub>r \<langle>Id\<rangle>list_rel\<close>

abbreviation aivdom_rel :: \<open>(aivdom \<times> isasat_aivdom) set\<close> where
  \<open>aivdom_rel \<equiv> \<langle>aivdom_int_rel\<rangle>code_hider_rel\<close>

abbreviation aivdom_int_assn :: \<open>aivdom \<Rightarrow> _ \<Rightarrow> assn\<close> where
  \<open>aivdom_int_assn \<equiv> vdom_fast_assn \<times>\<^sub>a vdom_fast_assn \<times>\<^sub>a vdom_fast_assn\<close>

definition aivdom_assn :: \<open>isasat_aivdom \<Rightarrow> _ \<Rightarrow> assn\<close> where
  \<open>aivdom_assn = code_hider_assn aivdom_int_assn Id\<close>

lemma
  add_learned_clause_aivdom_int:
  \<open>(add_learned_clause_aivdom_int, add_learned_clause_aivdom) \<in> nat_rel \<rightarrow> aivdom_rel \<rightarrow> aivdom_rel\<close> and
  \<open>(remove_inactive_aivdom_int, remove_inactive_aivdom) \<in> nat_rel \<rightarrow> aivdom_rel \<rightarrow> aivdom_rel\<close>
  by (auto intro!: frefI simp: code_hider_rel_def add_learned_clause_aivdom_def remove_inactive_aivdom_def)

sepref_def add_learned_clause_aivdom_impl
  is \<open>uncurry (RETURN oo add_learned_clause_aivdom_int)\<close>
  :: \<open>[\<lambda>(C,(a,b,c)). Suc (length (a)) < max_snat 64 \<and> Suc (length b) < max_snat 64]\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a aivdom_int_assn\<^sup>d \<rightarrow> aivdom_int_assn\<close>
  unfolding add_learned_clause_aivdom_int_def
  by sepref

sepref_def remove_inactive_aivdom_impl
  is \<open>uncurry (RETURN oo remove_inactive_aivdom_int)\<close>
  :: \<open>[\<lambda>(C,(a,b,c)). C < (length b)]\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a aivdom_int_assn\<^sup>d \<rightarrow> aivdom_int_assn\<close>
  unfolding remove_inactive_aivdom_int_def
  by sepref

context
  notes [fcomp_norm_unfold] = stats_assn_alt_def[symmetric] aivdom_assn_def[symmetric]
begin
lemmas [sepref_fr_rules] =
  add_learned_clause_aivdom_impl.refine[FCOMP add_learned_clause_aivdom_int]
  
end
end