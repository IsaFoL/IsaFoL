theory IsaSAT_Proofs_LLVM
  imports IsaSAT_Proofs IsaSAT_Setup_LLVM
begin

sepref_def log_literal_impl
  is \<open>RETURN o log_literal\<close>
  :: \<open>unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding log_literal_def
  by sepref


sepref_def log_start_new_clause_impl
  is \<open>RETURN o log_start_new_clause\<close>
  :: \<open>unat64_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding log_start_new_clause_def
  by sepref

sepref_def log_start_del_clause_impl
  is \<open>RETURN o log_start_del_clause\<close>
  :: \<open>unat64_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding log_start_del_clause_def
  by sepref

sepref_def log_end_clause_impl
  is \<open>RETURN o log_end_clause\<close>
  :: \<open>unat64_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding log_end_clause_def
  by sepref

sepref_def log_clause_heur_impl
  is \<open>uncurry log_clause_heur\<close>
  :: \<open>[\<lambda>(S, C). length (get_clauses_wl_heur S) \<le> sint64_max]\<^sub>a isasat_bounded_assn\<^sup>k *\<^sub>a snat64_assn\<^sup>k \<rightarrow> unit_assn\<close>
  unfolding log_clause_heur_def
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref


sepref_def log_new_clause_heur_impl
  is \<open>uncurry log_new_clause_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a snat64_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  supply [dest] = isasat_bounded_assn_length_arenaD
  unfolding log_new_clause_heur_def
  apply (annot_unat_const \<open>TYPE(64)\<close>)
  by sepref

sepref_def log_del_clause_heur_impl
  is \<open>uncurry log_del_clause_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a snat64_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  supply [dest] = isasat_bounded_assn_length_arenaD
  unfolding log_del_clause_heur_def
  apply (annot_unat_const \<open>TYPE(64)\<close>)
  by sepref

sepref_register log_del_clause_heur log_new_clause_heur_impl log_unit_clause

sepref_def log_unit_clause_impl
  is \<open>RETURN o log_unit_clause\<close>
  :: \<open>unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding log_unit_clause_def
  apply (annot_unat_const \<open>TYPE(64)\<close>)
  by sepref

sepref_def mark_literal_for_unit_deletion_impl
  is \<open>RETURN o mark_literal_for_unit_deletion\<close>
  :: \<open>unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding mark_literal_for_unit_deletion_def
  by sepref


sepref_def mark_clause_for_unit_as_unchanged_impl
  is \<open>RETURN o mark_clause_for_unit_as_unchanged\<close>
  :: \<open>unat64_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding mark_clause_for_unit_as_unchanged_def
  by sepref

sepref_def mark_clause_for_unit_as_changed_impl
  is \<open>RETURN o mark_clause_for_unit_as_changed\<close>
  :: \<open>unat64_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding mark_clause_for_unit_as_changed_def
  by sepref

end