theory IsaSAT_Propagate_Conflict_LLVM
  imports IsaSAT_Propagate_Conflict IsaSAT_Inner_Propagation_LLVM
begin

(*TODO Move*)

lemma length_ll[def_pat_rules]: \<open>length_ll$xs$i \<equiv> op_list_list_llen$xs$i\<close>
  by (auto simp: op_list_list_llen_def length_ll_def)

sepref_definition length_ll_fs_heur_fast_code
  is \<open>uncurry (RETURN oo length_ll_fs_heur)\<close>
  :: \<open>[\<lambda>(S, L). nat_of_lit L < length (get_watched_wl_heur S)]\<^sub>a
      isasat_bounded_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> sint64_nat_assn\<close>
  unfolding length_ll_fs_heur_alt_def get_watched_wl_heur_def isasat_bounded_assn_def
    length_ll_def[symmetric]
  supply [[goals_limit=1]]
  by sepref

declare length_ll_fs_heur_fast_code.refine[sepref_fr_rules]

sepref_register unit_propagation_inner_loop_body_wl_heur


lemma unit_propagation_inner_loop_wl_loop_D_heur_fast:
  \<open>length (get_clauses_wl_heur b) \<le> sint64_max \<Longrightarrow>
    unit_propagation_inner_loop_wl_loop_D_heur_inv b a (a1', a1'a, a2'a) \<Longrightarrow>
     length (get_clauses_wl_heur a2'a) \<le> sint64_max\<close>
  unfolding unit_propagation_inner_loop_wl_loop_D_heur_inv_def
  by auto

sepref_definition unit_propagation_inner_loop_wl_loop_D_fast
  is \<open>uncurry unit_propagation_inner_loop_wl_loop_D_heur\<close>
  :: \<open>[\<lambda>(L, S). length (get_clauses_wl_heur S) \<le> sint64_max]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> sint64_nat_assn *a sint64_nat_assn *a isasat_bounded_assn\<close>
  unfolding unit_propagation_inner_loop_wl_loop_D_heur_def PR_CONST_def
  unfolding watched_by_nth_watched_app watched_app_def[symmetric]
    length_ll_fs_heur_def[symmetric]
  unfolding delete_index_and_swap_update_def[symmetric] append_update_def[symmetric]
    is_None_def[symmetric] get_conflict_wl_is_None_heur_alt_def[symmetric]
    length_ll_fs_def[symmetric]
  supply [[goals_limit=1]] unit_propagation_inner_loop_wl_loop_D_heur_fast[intro] length_ll_fs_heur_def[simp]
apply (annot_snat_const "TYPE (64)")
  by sepref

lemma le_uint64_max_minus_4_uint64_max: \<open>a \<le> sint64_max - 4 \<Longrightarrow> Suc a < max_snat 64\<close>
  by (auto simp: sint64_max_def max_snat_def)

sepref_definition cut_watch_list_heur2_fast_code
  is \<open>uncurry3 cut_watch_list_heur2\<close>
  :: \<open>[\<lambda>(((j, w), L), S). length (watched_by_int S L) \<le> sint64_max-4]\<^sub>a
     sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a
     isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]] (* length_ll_def[simp] sint64_max_le_max_snat64[intro]
    le_uint64_max_minus_4_uint64_max[dest]*)  unfolding cut_watch_list_heur2_def isasat_bounded_assn_def length_ll_def[symmetric]
    nth_rll_def[symmetric]
    op_list_list_take_alt_def[symmetric]
    op_list_list_upd_alt_def[symmetric]
  apply (annot_snat_const "TYPE (64)")
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
supply sint64_max_le_max_snat64[intro del:]
    le_uint64_max_minus_4_uint64_max[dest del:]
apply sepref_dbg_trans_step
apply sepref_dbg_side
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step
apply sepref_dbg_trans_step

oops
  apply sepref_dbg_trans
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_constraints

  apply sepref_dbg_keep
apply sepref_dbg_trans_keep
apply sepref_dbg_trans_step_keep
apply sepref_dbg_side_unfold
subgoal
apply (auto intro: sint64_max_le_max_snat64 simp: dest: le_uint64_max_minus_4_uint64_max )[]
oops
  by sepref

declare cut_watch_list_heur2_fast_code.refine[sepref_fr_rules]


sepref_definition unit_propagation_inner_loop_wl_D_fast_code
  is \<open>uncurry unit_propagation_inner_loop_wl_D_heur\<close>
  :: \<open>[\<lambda>(L, S). length (get_clauses_wl_heur S) \<le> uint64_max]\<^sub>a
        unat_lit_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]] nat_of_uint64_conv_hnr[sepref_fr_rules]
  unfolding PR_CONST_def unit_propagation_inner_loop_wl_D_heur_def
  by sepref

declare unit_propagation_inner_loop_wl_D_fast_code.refine[sepref_fr_rules]


sepref_definition select_and_remove_from_literals_to_update_wl_code
  is \<open>select_and_remove_from_literals_to_update_wl_heur\<close>
  :: \<open>isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn *a unat_lit_assn\<close>
  supply [[goals_limit=1]] uint32_nat_assn_plus[sepref_fr_rules]
  unfolding select_and_remove_from_literals_to_update_wl_heur_alt_def isasat_unbounded_assn_def
    one_uint32_nat_def[symmetric]
  supply [[goals_limit = 1]]
  by sepref

declare select_and_remove_from_literals_to_update_wl_code.refine[sepref_fr_rules]

sepref_definition select_and_remove_from_literals_to_update_wlfast_code
  is \<open>select_and_remove_from_literals_to_update_wl_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn *a unat_lit_assn\<close>
  supply [[goals_limit=1]] uint32_nat_assn_plus[sepref_fr_rules]
  unfolding select_and_remove_from_literals_to_update_wl_heur_alt_def isasat_bounded_assn_def
    one_uint32_nat_def[symmetric]
  supply [[goals_limit = 1]]
  by sepref

declare select_and_remove_from_literals_to_update_wlfast_code.refine[sepref_fr_rules]


sepref_definition literals_to_update_wl_literals_to_update_wl_empty_code
  is \<open>RETURN o literals_to_update_wl_literals_to_update_wl_empty\<close>
  :: \<open>[\<lambda>S. isa_length_trail_pre (get_trail_wl_heur S)]\<^sub>a isasat_unbounded_assn\<^sup>k \<rightarrow> bool_assn\<close>
  unfolding literals_to_update_wl_literals_to_update_wl_empty_alt_def
    isasat_unbounded_assn_def
  by sepref

declare literals_to_update_wl_literals_to_update_wl_empty_code.refine[sepref_fr_rules]

sepref_definition literals_to_update_wl_literals_to_update_wl_empty_fast_code
  is \<open>RETURN o literals_to_update_wl_literals_to_update_wl_empty\<close>
  :: \<open>[\<lambda>S. isa_length_trail_pre (get_trail_wl_heur S)]\<^sub>a isasat_bounded_assn\<^sup>k \<rightarrow> bool_assn\<close>
  unfolding literals_to_update_wl_literals_to_update_wl_empty_alt_def
    isasat_bounded_assn_def
  by sepref

declare literals_to_update_wl_literals_to_update_wl_empty_fast_code.refine[sepref_fr_rules]

sepref_register literals_to_update_wl_literals_to_update_wl_empty
  select_and_remove_from_literals_to_update_wl_heur


sepref_definition unit_propagation_outer_loop_wl_D_code
  is \<open>unit_propagation_outer_loop_wl_D_heur\<close>
  :: \<open>isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
  supply [[goals_limit=1]]
    unit_propagation_outer_loop_wl_D_invI[intro]
  unfolding unit_propagation_outer_loop_wl_D_heur_def
    literals_to_update_wl_literals_to_update_wl_empty_def[symmetric]
  by sepref

declare unit_propagation_outer_loop_wl_D_code.refine[sepref_fr_rules]

sepref_definition unit_propagation_outer_loop_wl_D_fast_code
  is \<open>unit_propagation_outer_loop_wl_D_heur\<close>
  :: \<open>[\<lambda>S. length (get_clauses_wl_heur S) \<le> uint64_max]\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]] unit_propagation_outer_loop_wl_D_heur_fast[intro]
    unit_propagation_outer_loop_wl_D_invI[intro]
  unfolding unit_propagation_outer_loop_wl_D_heur_def
    literals_to_update_wl_literals_to_update_wl_empty_def[symmetric]
  by sepref

declare unit_propagation_outer_loop_wl_D_fast_code.refine[sepref_fr_rules]

end