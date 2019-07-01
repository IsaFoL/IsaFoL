theory IsaSAT_Inner_Propagation_LLVM
  imports IsaSAT_Setup_LLVM
     IsaSAT_Inner_Propagation
begin

sepref_register isa_save_pos

sepref_definition isa_save_pos_fast_code
  is \<open>uncurry2 isa_save_pos\<close>
  :: \<open>sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply
    [[goals_limit=1]]
    if_splits[split]
  unfolding isa_save_pos_def PR_CONST_def isasat_bounded_assn_def
  by sepref

declare isa_save_pos_fast_code.refine[sepref_fr_rules]

lemma [def_pat_rules]: \<open>nth_rll \<equiv> op_list_list_idx\<close>
 by (auto simp: nth_rll_def intro!: ext eq_reflection)

sepref_definition watched_by_app_heur_fast_code
  is \<open>uncurry2 (RETURN ooo watched_by_app_heur)\<close>
  :: \<open>[watched_by_app_heur_pre]\<^sub>a
        isasat_bounded_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> watcher_fast_assn\<close>
  supply [[goals_limit=1]]
  unfolding watched_by_app_heur_alt_def isasat_bounded_assn_def nth_rll_def[symmetric]
   watched_by_app_heur_pre_def
  by sepref

declare watched_by_app_heur_fast_code.refine[sepref_fr_rules]


(* TODO most of the unfolding should move to the definition *)
sepref_register isa_find_unwatched_wl_st_heur isa_find_unwatched_between isa_find_unset_lit
  polarity_pol

(*TODO dup*)
sepref_register 0 1

(*lemma "found = None \<longleftrightarrow> is_None (ASSN_ANNOT (snat_option_assn' TYPE(64)) found)"*)

sepref_definition isa_find_unwatched_between_fast_code
  is \<open>uncurry4 isa_find_unset_lit\<close>
  :: \<open>[\<lambda>((((M, N), _), _), _). length N \<le> sint64_max]\<^sub>a
     trail_pol_fast_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow>
       snat_option_assn' TYPE(64)\<close>
  supply [[goals_limit = 3]]
  supply [simp] = max_unat_def max_snat_def sint64_max_def
  unfolding isa_find_unset_lit_def isa_find_unwatched_between_def SET_FALSE_def[symmetric]
    PR_CONST_def
  apply (rewrite in \<open>if \<hole> then _ else _\<close>  tri_bool_eq_def[symmetric])
  apply (annot_snat_const "TYPE (64)")
  (*apply (rewrite in \<open>WHILEIT _ (\<lambda>(_,_). (\<hole>=_) \<and> _)\<close> annotate_assn[where A = \<open>snat_option_assn' TYPE(64)\<close>])
  apply (rewrite in \<open>WHILEIT _ _ _ (\<hole>,_)\<close> annotate_assn[where A = \<open>snat_option_assn' TYPE(64)\<close>])
  *)
  by sepref

declare isa_find_unwatched_between_fast_code.refine[sepref_fr_rules]

sepref_definition find_unwatched_wl_st_heur_fast_code
  is \<open>uncurry isa_find_unwatched_wl_st_heur\<close>
  :: \<open>[(\<lambda>(S, C). find_unwatched_wl_st_heur_pre (S, C) \<and>
            length (get_clauses_wl_heur S) \<le> sint64_max)]\<^sub>a
         isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> snat_option_assn' TYPE(64)\<close>
  supply [[goals_limit = 1]] isasat_fast_def[simp]
  supply [simp] = max_snat_def
  unfolding isa_find_unwatched_wl_st_heur_def PR_CONST_def
    find_unwatched_def fmap_rll_def[symmetric] isasat_bounded_assn_def
    length_uint32_nat_def[symmetric] isa_find_unwatched_def
    case_tri_bool_If find_unwatched_wl_st_heur_pre_def
    fmap_rll_u64_def[symmetric]
  apply (subst isa_find_unset_lit_def[symmetric])
  apply (subst isa_find_unset_lit_def[symmetric])
  apply (subst isa_find_unset_lit_def[symmetric])
  apply (annot_snat_const "TYPE (64)")
  by sepref

declare find_unwatched_wl_st_heur_fast_code.refine[sepref_fr_rules]


sepref_register update_clause_wl_heur
setup \<open>map_theory_claset (fn ctxt => ctxt delSWrapper "split_all_tac")\<close>

lemma arena_lit_pre_le2: \<open>
       arena_lit_pre a i \<Longrightarrow> length a \<le> sint64_max \<Longrightarrow> i < max_snat 64\<close>
   using arena_lifting(7)[of a _ _] unfolding arena_lit_pre_def arena_is_valid_clause_idx_and_access_def sint64_max_def max_snat_def
  by fastforce

lemma sint64_max_le_max_snat64: \<open>a < sint64_max \<Longrightarrow> Suc a < max_snat 64\<close>
  by (auto simp: max_snat_def sint64_max_def)

sepref_definition update_clause_wl_fast_code
  is \<open>uncurry7 update_clause_wl_heur\<close>
  :: \<open>[\<lambda>(((((((L, C), b), j), w), i), f), S). update_clause_wl_code_pre (((((((L, C), b), j), w), i), f), S) \<and>
        length (get_clauses_wl_heur S) \<le> sint64_max]\<^sub>a
     unat_lit_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a
       sint64_nat_assn\<^sup>k
        *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> sint64_nat_assn *a sint64_nat_assn *a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]  arena_lit_pre_le2[intro] swap_lits_pre_def[simp]
    sint64_max_le_max_snat64[intro]
  unfolding update_clause_wl_heur_def isasat_bounded_assn_def
    fmap_rll_def[symmetric] delete_index_and_swap_update_def[symmetric]
    delete_index_and_swap_ll_def[symmetric] fmap_swap_ll_def[symmetric]
    append_ll_def[symmetric] update_clause_wl_code_pre_def
    fmap_rll_u64_def[symmetric]
    fmap_swap_ll_u64_def[symmetric]
    fmap_swap_ll_def[symmetric]
    PR_CONST_def
  apply (annot_snat_const "TYPE (64)")
  by sepref

declare update_clause_wl_fast_code.refine[sepref_fr_rules]

lemma standard_constanst[simp, intro!]:
  \<open>0 < max_snat n\<close>
  \<open>1 < max_snat 32\<close>
  \<open>2 < max_snat 32\<close>
  \<open>3 < max_snat 32\<close>
  \<open>4 < max_snat 32\<close>
  \<open>1 < max_snat 64\<close>
  \<open>2 < max_snat 64\<close>
  \<open>3 < max_snat 64\<close>
  \<open>4 < max_snat 64\<close>
  \<open>1 < max_unat 32\<close>
  \<open>2 < max_unat 32\<close>
  \<open>3 < max_unat 32\<close>
  \<open>4 < max_unat 32\<close>
  \<open>1 < max_unat 64\<close>
  \<open>2 < max_unat 64\<close>
  \<open>3 < max_unat 64\<close>
  \<open>4 < max_unat 64\<close>
  by (auto simp: max_snat_def max_unat_def)

sepref_definition propagate_lit_wl_fast_code
  is \<open>uncurry3 propagate_lit_wl_heur\<close>
  :: \<open>[\<lambda>(((L, C), i), S). propagate_lit_wl_heur_pre (((L, C), i), S) \<and>
      length (get_clauses_wl_heur S) \<le> sint64_max]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  unfolding PR_CONST_def propagate_lit_wl_heur_def
    cons_trail_Propagated_def[symmetric]
  supply [[goals_limit=1]] swap_lits_pre_def[simp]
  unfolding update_clause_wl_heur_def isasat_bounded_assn_def
    propagate_lit_wl_heur_pre_def fmap_swap_ll_def[symmetric]
    fmap_swap_ll_u64_def[symmetric]
    save_phase_def
  apply (rewrite at \<open>count_decided_pol _ = \<hole>\<close> unat_const_fold[where 'a=32])
  apply (annot_snat_const "TYPE (64)")
  by sepref

declare propagate_lit_wl_fast_code.refine[sepref_fr_rules]


sepref_definition propagate_lit_wl_bin_fast_code
  is \<open>uncurry3 propagate_lit_wl_bin_heur\<close>
  :: \<open>[\<lambda>(((L, C), i), S). propagate_lit_wl_heur_pre(((L, C), i), S) \<and>
      length (get_clauses_wl_heur S) \<le> sint64_max]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>
      isasat_bounded_assn\<close>
  unfolding PR_CONST_def propagate_lit_wl_heur_def
    cons_trail_Propagated_def[symmetric]
  supply [[goals_limit=1]]  length_ll_def[simp]
  unfolding update_clause_wl_heur_def isasat_bounded_assn_def
    propagate_lit_wl_heur_pre_def fmap_swap_ll_def[symmetric]
    fmap_swap_ll_u64_def[symmetric]
    save_phase_def propagate_lit_wl_bin_heur_def
  apply (rewrite at \<open>count_decided_pol _ = \<hole>\<close> unat_const_fold[where 'a=32])
  by sepref

declare propagate_lit_wl_bin_fast_code.refine[sepref_fr_rules]


sepref_register neq : "(op_neq :: clause_status \<Rightarrow> _ \<Rightarrow> _)" 
lemma status_neq_refine1: "((\<noteq>),op_neq) \<in> status_rel \<rightarrow> status_rel \<rightarrow> bool_rel"
  by (auto simp: status_rel_def)

sepref_definition status_neq_impl is "uncurry (RETURN oo (\<noteq>))" 
  :: "(unat_assn' TYPE(32))\<^sup>k *\<^sub>a (unat_assn' TYPE(32))\<^sup>k \<rightarrow>\<^sub>a bool1_assn"  
  by sepref

lemmas [sepref_fr_rules] = status_neq_impl.refine[FCOMP status_neq_refine1]

sepref_definition clause_not_marked_to_delete_heur_fast_code
  is \<open>uncurry (RETURN oo clause_not_marked_to_delete_heur)\<close>
  :: \<open>[clause_not_marked_to_delete_heur_pre]\<^sub>a isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> bool1_assn\<close>
  supply [[goals_limit=1]]
  unfolding clause_not_marked_to_delete_heur_alt_def isasat_bounded_assn_def
     clause_not_marked_to_delete_heur_pre_def
  by sepref

declare clause_not_marked_to_delete_heur_fast_code.refine[sepref_fr_rules]


find_theorems sint64_max max_snat
sepref_definition update_blit_wl_heur_fast_code
  is \<open>uncurry6 update_blit_wl_heur\<close>
  :: \<open>[\<lambda>((((((_, _), _), _), C), i), S). length (get_clauses_wl_heur S) \<le> sint64_max]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a
         isasat_bounded_assn\<^sup>d \<rightarrow>
     sint64_nat_assn *a sint64_nat_assn *a isasat_bounded_assn\<close>
  supply [[goals_limit=1]] sint64_max_le_max_snat64[intro]
  unfolding update_blit_wl_heur_def isasat_bounded_assn_def append_ll_def[symmetric]
  apply (annot_snat_const "TYPE (64)")
apply sepref_dbg_keep
apply sepref_dbg_trans_keep
apply sepref_dbg_trans_step_keep
apply sepref_dbg_side_unfold
apply sepref_dbg_side_keep
subgoal
oops
  by sepref

term op_list_list_pop_back
declare update_blit_wl_heur_fast_code.refine[sepref_fr_rules]

sepref_register keep_watch_heur

sepref_definition keep_watch_heur_fast_code
  is \<open>uncurry3 keep_watch_heur\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply
    [[goals_limit=1]]
    if_splits[split]
  supply undefined_lit_polarity_st_iff[iff]
    unit_prop_body_wl_D_find_unwatched_heur_inv_def[simp]
  unfolding keep_watch_heur_def PR_CONST_def
  unfolding fmap_rll_def[symmetric] isasat_bounded_assn_def
  unfolding 
    nth_rll_def[symmetric]
    SET_FALSE_def[symmetric] SET_TRUE_def[symmetric]
  by sepref

declare keep_watch_heur_fast_code.refine[sepref_fr_rules]

sepref_register isa_set_lookup_conflict_aa set_conflict_wl_heur

sepref_register arena_incr_act
term "_ oooo _"
sepref_definition set_conflict_wl_heur_fast_code
  is \<open>uncurry set_conflict_wl_heur\<close>
  :: \<open>[\<lambda>(C, S). set_conflict_wl_heur_pre (C, S) \<and>
     length (get_clauses_wl_heur S) \<le> sint64_max]\<^sub>a
    sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding set_conflict_wl_heur_def isasat_bounded_assn_def
    set_conflict_wl_heur_pre_def PR_CONST_def
  apply (annot_unat_const "TYPE (32)")
  by sepref

declare set_conflict_wl_heur_fast_code.refine[sepref_fr_rules]


sepref_register update_blit_wl_heur clause_not_marked_to_delete_heur

sepref_definition unit_propagation_inner_loop_body_wl_fast_heur_code
  is \<open>uncurry3 unit_propagation_inner_loop_body_wl_heur\<close>
  :: \<open>[\<lambda>((L, w), S). length (get_clauses_wl_heur S) \<le> uint64_max]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k  *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>
       sint64_nat_assn *a sint64_nat_assn *a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
    if_splits[split]
    length_rll_def[simp]
  supply undefined_lit_polarity_st_iff[iff]
    unit_prop_body_wl_D_find_unwatched_heur_inv_def[simp]
  unfolding unit_propagation_inner_loop_body_wl_heur_def length_rll_def[symmetric] PR_CONST_def
  unfolding fmap_rll_def[symmetric]
  unfolding fast_minus_def[symmetric]
    SET_FALSE_def[symmetric] SET_TRUE_def[symmetric] tri_bool_eq_def[symmetric]
  apply (annot_snat_const "TYPE (64)")
  by sepref

sepref_register unit_propagation_inner_loop_body_wl_heur

declare
  unit_propagation_inner_loop_body_wl_fast_heur_code.refine[sepref_fr_rules]

end
