theory IsaSAT_Clauses_LLVM
  imports IsaSAT_Clauses  IsaSAT_Arena_LLVM
begin

sepref_register is_short_clause header_size fm_add_new_fast fm_mv_clause_to_new_arena

abbreviation clause_ll_assn :: \<open>nat clause_l \<Rightarrow> _ \<Rightarrow> assn\<close> where
  \<open>clause_ll_assn \<equiv> larray64_assn unat_lit_assn\<close>

sepref_definition is_short_clause_code
  is \<open>RETURN o is_short_clause\<close>
  :: \<open> clause_ll_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding is_short_clause_def 
  by sepref
declare is_short_clause_code.refine[sepref_fr_rules]

sepref_definition header_size_code
  is \<open>RETURN o header_size\<close>
  :: \<open>clause_ll_assn\<^sup>k \<rightarrow>\<^sub>a sint64_nat_assn\<close>
  unfolding header_size_def
  apply (annot_snat_const "TYPE(64)")
  supply [simp] = max_snat_def
  by sepref
declare header_size_code.refine[sepref_fr_rules]


lemma header_size_bound: "header_size x \<le> 5" by (auto simp: header_size_def)
  
lemma fm_add_new_bounds1: "\<lbrakk> 
  length a2' < header_size baa + length b + length baa; 
  length b + length baa + 5 \<le> sint64_max   \<rbrakk> 
  \<Longrightarrow> Suc (length a2') < max_snat 64"
  
  "length b + length baa + 5 \<le> sint64_max \<Longrightarrow> length b + header_size baa < max_snat 64"
  using header_size_bound[of baa]
  by (auto simp: max_snat_def sint64_max_def)
  

sepref_definition (in -)append_and_length_fast_code
  is \<open>uncurry2 fm_add_new_fast\<close>
  :: \<open>[append_and_length_fast_code_pre]\<^sub>a
     bool1_assn\<^sup>k *\<^sub>a clause_ll_assn\<^sup>k *\<^sub>a (arena_fast_assn)\<^sup>d \<rightarrow>
       arena_fast_assn *a sint64_nat_assn\<close>
  unfolding fm_add_new_fast_def fm_add_new_def append_and_length_fast_code_pre_def
  
  apply (rewrite at "AActivity \<hole>" unat_const_fold[where 'a=32])+
  apply (rewrite at "APos \<hole>" unat_const_fold[where 'a=32])+
  apply (rewrite at "length _ - 2" annot_snat_unat_downcast[where 'l=32])
  
  supply [simp] = max_snat_def sint64_max_def max_unat_def uint32_max_def
  supply [simp] = fm_add_new_bounds1[simplified]
  supply [dest!] = rdomp_al_imp_len_bound
  
  apply (annot_snat_const "TYPE(64)")
  by sepref

declare append_and_length_fast_code.refine[sepref_fr_rules]


sepref_definition fm_mv_clause_to_new_arena_fast_code
  is \<open>uncurry2 fm_mv_clause_to_new_arena\<close>
  :: \<open>[\<lambda>((n, arena\<^sub>o), arena). length arena\<^sub>o \<le> sint64_max \<and> length arena + arena_length arena\<^sub>o n +
         (if arena_length arena\<^sub>o  n \<le> 4 then 4 else 5) \<le> sint64_max]\<^sub>a
       sint64_nat_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>d \<rightarrow> arena_fast_assn\<close>
  supply [[goals_limit=1]] if_splits[split]
  supply [simp] = max_snat_def sint64_max_def
  unfolding fm_mv_clause_to_new_arena_def 
  apply (annot_snat_const "TYPE(64)")
  by sepref

declare fm_mv_clause_to_new_arena_fast_code.refine[sepref_fr_rules]

end

