theory IsaSAT_Simplify_Forward_Subsumption_LLVM
  imports
    IsaSAT_Simplify_Forward_Subsumption
    IsaSAT_Simplify_Clause_Units_LLVM
begin

no_notation WB_More_Refinement.fref (\<open>[_]\<^sub>f _ \<rightarrow> _\<close> [0,60,60] 60)
no_notation WB_More_Refinement.freft (\<open>_ \<rightarrow>\<^sub>f _\<close> [60,60] 60)

(*TODO: kill mop_arena_lit2_st*)
sepref_def isa_all_lit_clause_unset
  is \<open>uncurry isa_all_lit_clause_unset\<close>
  :: \<open>sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  supply [[goals_limit=1]]
  unfolding isa_all_lit_clause_unset_def
    mop_access_lit_in_clauses_heur_def[symmetric] mop_polarity_st_heur_def[symmetric]
    tri_bool_eq_def[symmetric] UNSET_def[symmetric]
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

lemma rdomp_aivdom_assn_length_avdomD: \<open>rdomp aivdom_assn x \<Longrightarrow> length (get_avdom_aivdom x) < max_snat 64\<close>
  unfolding isasat_bounded_assn_def
  apply (cases x)
  apply (auto simp: isasat_bounded_assn_def sint64_max_def max_snat_def length_avdom_def
    aivdom_assn_def code_hider_assn_def hr_comp_def code_hider_rel_def
    split: isasat_int_splits
    dest: al_assn_boundD[of sint64_nat_assn] mod_starD)
  done

lemma rdomp_isasat_bounded_assn_length_avdomD:
  \<open>rdomp isasat_bounded_assn x \<Longrightarrow> length_avdom x < max_snat 64\<close>
  using rdomp_aivdom_assn_length_avdomD[of \<open>get_aivdom x\<close>] apply -
  unfolding isasat_bounded_assn_def rdomp_def
  apply normalize_goal+
  by (cases x)
   (force simp: isasat_bounded_assn_def length_avdom_def 
    split: isasat_int_splits
    dest!: rdomp_aivdom_assn_length_avdomD mod_starD)


sepref_register isa_all_lit_clause_unset isa_push_to_occs_list_st
  find_best_subsumption_candidate 

(*TODO: missing get_occs setup*)
sepref_def find_best_subsumption_candidate_code
  is \<open>uncurry find_best_subsumption_candidate\<close>
  :: \<open>sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a unat_lit_assn\<close>
  supply [[goals_limit=1]]
  unfolding find_best_subsumption_candidate_def
    mop_access_lit_in_clauses_heur_def[symmetric]
    tri_bool_eq_def[symmetric] UNSET_def[symmetric]
  apply (annot_snat_const \<open>TYPE(64)\<close>)
oops

sepref_def isa_populate_occs_code
  is isa_populate_occs
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a al_assn' TYPE(64) uint64_nat_assn \<times>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  supply [dest] = rdomp_isasat_bounded_assn_length_avdomD
  unfolding isa_populate_occs_def access_avdom_at_def[symmetric] length_avdom_def[symmetric]
    al_fold_custom_empty[where 'l=64] Let_def[of \<open>get_avdom _\<close>] Let_def[of \<open>get_occs _\<close>]
  apply (annot_snat_const \<open>TYPE(64)\<close>)
(*  apply sepref_dbg_keep
  apply sepref_dbg_trans_keep
  apply sepref_dbg_trans_step_keep
  apply sepref_dbg_side_unfold
  subgoal
    apply (auto dest!: rdomp_isasat_bounded_assn_length_avdomD)
try0
  *)
  oops

thm isa_populate_occs_def
thm access_avdom_at_def
find_theorems get_avdom length
thm isa_forward_subsumption_all_wl2_def
sepref_register isa_forward_subsumption_all_wl2 isa_populate_occs

sepref_register isa_forward_subsumption_all

sepref_def isa_forward_subsumption_all
  is \<open>isa_forward_subsumption_all\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  unfolding isa_forward_subsumption_all_def
  by sepref

end