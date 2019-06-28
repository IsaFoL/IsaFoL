theory IsaSAT_Decide_LLVM
  imports IsaSAT_Decide IsaSAT_VMTF_LLVM IsaSAT_Setup_LLVM
begin

sepref_definition lit_of_found_atm_D_code
  is \<open>uncurry lit_of_found_atm_D\<close>
  :: \<open>[lit_of_found_atm_D_pre]\<^sub>a
      (array_assn bool_assn)\<^sup>k *\<^sub>a (option_assn uint32_nat_assn)\<^sup>d \<rightarrow>
          option_assn unat_lit_assn\<close>
  supply [[goals_limit=1]]
  supply not_is_None_not_None[simp] Pos_unat_lit_assn'[sepref_fr_rules]
    Neg_unat_lit_assn'[sepref_fr_rules]
  unfolding lit_of_found_atm_D_def PR_CONST_def lit_of_found_atm_D_pre_def
  by sepref

declare lit_of_found_atm_D_code.refine[sepref_fr_rules]

lemma lit_of_found_atm_hnr[sepref_fr_rules]:
  \<open>(uncurry lit_of_found_atm_D_code, uncurry lit_of_found_atm)
   \<in> [lit_of_found_atm_D_pre]\<^sub>a
     phase_saver_conc\<^sup>k *\<^sub>a (option_assn uint32_nat_assn)\<^sup>d \<rightarrow>
     option_assn unat_lit_assn\<close>
  using lit_of_found_atm_D_code.refine[FCOMP lit_of_found_atm_D_lit_of_found_atm[unfolded convert_fref]] by simp

sepref_register find_undefined_atm
sepref_definition find_unassigned_lit_wl_D_code
  is \<open>find_unassigned_lit_wl_D_heur\<close>
  :: \<open>isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a (isasat_unbounded_assn *a option_assn unat_lit_assn)\<close>
  supply [[goals_limit=1]]
  unfolding find_unassigned_lit_wl_D_heur_def isasat_unbounded_assn_def PR_CONST_def
  by sepref

sepref_definition find_unassigned_lit_wl_D_fast_code
  is \<open>find_unassigned_lit_wl_D_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a (isasat_bounded_assn *a option_assn unat_lit_assn)\<close>
  supply [[goals_limit=1]]
  unfolding find_unassigned_lit_wl_D_heur_def isasat_bounded_assn_def PR_CONST_def
  by sepref

declare find_unassigned_lit_wl_D_code.refine[sepref_fr_rules]
  find_unassigned_lit_wl_D_fast_code.refine[sepref_fr_rules]


sepref_definition decide_lit_wl_code
  is \<open>uncurry decide_lit_wl_heur\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding decide_lit_wl_heur_def isasat_unbounded_assn_def PR_CONST_def
    cons_trail_Decided_def[symmetric]
  by sepref


sepref_definition decide_lit_wl_fast_code
  is \<open>uncurry decide_lit_wl_heur\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding decide_lit_wl_heur_def isasat_bounded_assn_def PR_CONST_def
    cons_trail_Decided_def[symmetric]
  by sepref

declare decide_lit_wl_code.refine[sepref_fr_rules]
  decide_lit_wl_fast_code.refine[sepref_fr_rules]


sepref_register decide_wl_or_skip_D find_unassigned_lit_wl_D_heur decide_lit_wl_heur
sepref_definition decide_wl_or_skip_D_code
  is \<open>decide_wl_or_skip_D_heur\<close>
  :: \<open>isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a bool_assn *a isasat_unbounded_assn\<close>
  unfolding decide_wl_or_skip_D_heur_def PR_CONST_def
  supply [[goals_limit = 1]]
    find_unassigned_lit_wl_D_def[simp] image_image[simp]
  by sepref

sepref_definition decide_wl_or_skip_D_fast_code
  is \<open>decide_wl_or_skip_D_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a bool_assn *a isasat_bounded_assn\<close>
  unfolding decide_wl_or_skip_D_heur_def PR_CONST_def
  supply [[goals_limit = 1]]
    find_unassigned_lit_wl_D_def[simp] image_image[simp]
  by sepref

declare decide_wl_or_skip_D_code.refine[sepref_fr_rules]
  decide_wl_or_skip_D_fast_code.refine[sepref_fr_rules]

end