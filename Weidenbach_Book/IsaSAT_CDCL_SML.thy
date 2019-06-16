theory IsaSAT_CDCL_SML
  imports IsaSAT_CDCL IsaSAT_Propagate_Conflict_SML IsaSAT_Conflict_Analysis_SML
    IsaSAT_Backtrack_SML
    IsaSAT_Decide_SML IsaSAT_Show_SML
begin


sepref_register get_conflict_wl_is_None decide_wl_or_skip_D_heur skip_and_resolve_loop_wl_D_heur
  backtrack_wl_D_nlit_heur isasat_current_status count_decided_st_heur get_conflict_wl_is_None_heur

sepref_register cdcl_twl_o_prog_wl_D

sepref_definition cdcl_twl_o_prog_wl_D_code
  is \<open>cdcl_twl_o_prog_wl_D_heur\<close>
  :: \<open>isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a bool_assn *a isasat_unbounded_assn\<close>
  unfolding cdcl_twl_o_prog_wl_D_heur_def PR_CONST_def
  unfolding get_conflict_wl_is_None get_conflict_wl_is_None_heur_alt_def[symmetric]
  supply [[goals_limit = 1]]
  by sepref

sepref_definition cdcl_twl_o_prog_wl_D_fast_code
  is \<open>cdcl_twl_o_prog_wl_D_heur\<close>
  :: \<open>[isasat_fast]\<^sub>a
      isasat_bounded_assn\<^sup>d \<rightarrow> bool_assn *a isasat_bounded_assn\<close>
  unfolding cdcl_twl_o_prog_wl_D_heur_def PR_CONST_def
  unfolding get_conflict_wl_is_None get_conflict_wl_is_None_heur_alt_def[symmetric]
  supply [[goals_limit = 1]] isasat_fast_def[simp]
  by sepref

declare cdcl_twl_o_prog_wl_D_code.refine[sepref_fr_rules]
  cdcl_twl_o_prog_wl_D_fast_code.refine[sepref_fr_rules]

sepref_register cdcl_twl_stgy_prog_wl_D unit_propagation_outer_loop_wl_D_heur
  cdcl_twl_o_prog_wl_D_heur

sepref_definition cdcl_twl_stgy_prog_wl_D_code
  is \<open>cdcl_twl_stgy_prog_wl_D_heur\<close>
  :: \<open>isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
  unfolding cdcl_twl_stgy_prog_wl_D_heur_def PR_CONST_def
  supply [[goals_limit = 1]]
  by sepref


export_code cdcl_twl_stgy_prog_wl_D_code in SML_imp module_name SAT_Solver
  file "code/CDCL_Cached_Array_Trail.sml"

end