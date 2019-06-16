theory IsaSAT_Initialisation_SML
  imports IsaSAT_Setup_SML IsaSAT_VMTF_SML Watched_Literals.Watched_Literals_Watch_List_Initialisation
        Watched_Literals.Watched_Literals_Watch_List_Initialisation
begin


sepref_definition (in -) atoms_hash_empty_code
  is \<open>atoms_hash_int_empty\<close>
  :: \<open>nat_assn\<^sup>k \<rightarrow>\<^sub>a phase_saver_conc\<close>
  unfolding atoms_hash_int_empty_def array_fold_custom_replicate
  by sepref

sepref_definition distinct_atms_empty_code
  is \<open>distinct_atms_int_empty\<close>
  :: \<open>nat_assn\<^sup>k \<rightarrow>\<^sub>a arl_assn uint32_nat_assn *a atoms_hash_assn\<close>
  unfolding distinct_atms_int_empty_def array_fold_custom_replicate
    arl.fold_custom_empty
  by sepref

declare distinct_atms_empty_code.refine[sepref_fr_rules]

end