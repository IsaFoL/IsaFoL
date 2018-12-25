theory Impl_List_Set_Ndj
imports
  "Collections.Refine_Dflt_ICF"
  "Refine_Imperative_HOL.IICF"
  "Refine_Imperative_HOL.Sepref_ICF_Bindings"
begin

  definition [simp]: "ndls_rel \<equiv> br set (\<lambda>_. True)" 
  definition "nd_list_set_assn A \<equiv> pure (ndls_rel O \<langle>the_pure A\<rangle>set_rel)"
  
  context
    notes [fcomp_norm_unfold] = nd_list_set_assn_def[symmetric]
    notes [fcomp_norm_unfold] = list_set_assn_def[symmetric]
  begin    
  
    lemma ndls_empty_hnr_aux: "([],op_set_empty) \<in> ndls_rel" by (auto simp: in_br_conv)
    sepref_decl_impl (no_register) ndls_empty: ndls_empty_hnr_aux[sepref_param] .

    lemma ndls_is_empty_hnr_aux: "((=) [], op_set_is_empty) \<in> ndls_rel \<rightarrow> bool_rel" 
      by (auto simp: in_br_conv)   
    sepref_decl_impl ndls_is_empty: ndls_is_empty_hnr_aux[sepref_param] .   

    lemma ndls_insert_hnr_aux: "((#), op_set_insert) \<in> Id \<rightarrow> ndls_rel \<rightarrow> ndls_rel"
      by (auto simp: in_br_conv)   
      
    sepref_decl_impl ndls_insert: ndls_insert_hnr_aux[sepref_param] .    

        
    sepref_decl_op ndls_ls_copy: "\<lambda>x::'a set. x" :: "\<langle>A\<rangle>set_rel \<rightarrow> \<langle>A\<rangle>set_rel" .
    lemma op_ndls_ls_copy_hnr_aux: 
      "(remdups, op_ndls_ls_copy)\<in>ndls_rel \<rightarrow> \<langle>Id\<rangle>list_set_rel"  
      by (auto simp: in_br_conv list_set_rel_def)
      
    sepref_decl_impl op_ndls_ls_copy_hnr_aux[sepref_param] .   
  end      

  definition [simp]: "op_ndls_empty = op_set_empty"
  interpretation ndls: set_custom_empty "return []" op_ndls_empty
    by unfold_locales simp
  sepref_register op_ndls_empty
  lemmas [sepref_fr_rules] = ndls_empty_hnr[folded op_ndls_empty_def]

  lemma fold_ndls_ls_copy: "x = op_ndls_ls_copy x" by simp  
    

end
