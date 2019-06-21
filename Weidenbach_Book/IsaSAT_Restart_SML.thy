theory IsaSAT_Restart_SML
  imports IsaSAT_Restart IsaSAT_Restart_Heuristics_SML IsaSAT_CDCL_SML
begin
sepref_register length_avdom
sepref_register clause_is_learned_heur

sepref_definition length_avdom_code
  is \<open>RETURN o length_avdom\<close>
  :: \<open>isasat_unbounded_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  unfolding length_avdom_alt_def access_vdom_at_pre_def isasat_unbounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

sepref_definition length_avdom_fast_code
  is \<open>RETURN o length_avdom\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  unfolding length_avdom_alt_def access_vdom_at_pre_def isasat_bounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

declare  length_avdom_code.refine[sepref_fr_rules]
    length_avdom_fast_code.refine[sepref_fr_rules]

sepref_register get_the_propagation_reason_heur
sepref_definition get_the_propagation_reason_heur_code
  is \<open>uncurry get_the_propagation_reason_heur\<close>
  :: \<open>isasat_unbounded_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a option_assn nat_assn\<close>
  unfolding get_the_propagation_reason_heur_alt_def access_vdom_at_pre_def isasat_unbounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

sepref_definition get_the_propagation_reason_heur_fast_code
  is \<open>uncurry get_the_propagation_reason_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a option_assn uint64_nat_assn\<close>
  unfolding get_the_propagation_reason_heur_alt_def access_vdom_at_pre_def
     isasat_bounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

declare get_the_propagation_reason_heur_fast_code.refine[sepref_fr_rules]
    get_the_propagation_reason_heur_code.refine[sepref_fr_rules]


sepref_definition clause_is_learned_heur_code
  is \<open>uncurry (RETURN oo ( clause_is_learned_heur))\<close>
  :: \<open>[\<lambda>(S, C). arena_is_valid_clause_vdom (get_clauses_wl_heur S) C]\<^sub>a
      isasat_unbounded_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> bool_assn\<close>
  unfolding clause_is_learned_heur_alt_def isasat_unbounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

sepref_definition clause_is_learned_heur_code2
  is \<open>uncurry (RETURN oo ( clause_is_learned_heur))\<close>
  :: \<open>[\<lambda>(S, C). arena_is_valid_clause_vdom (get_clauses_wl_heur S) C]\<^sub>a
      isasat_bounded_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> bool_assn\<close>
  unfolding clause_is_learned_heur_alt_def isasat_bounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

declare clause_is_learned_heur_code.refine[sepref_fr_rules]
    clause_is_learned_heur_code2.refine[sepref_fr_rules]


sepref_register clause_lbd_heur
sepref_definition clause_lbd_heur_code
  is \<open>uncurry (RETURN oo ( clause_lbd_heur))\<close>
  :: \<open>[\<lambda>(S, C). get_clause_LBD_pre (get_clauses_wl_heur S) C]\<^sub>a
       isasat_unbounded_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  unfolding clause_lbd_heur_alt_def isasat_unbounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

sepref_definition clause_lbd_heur_code2
  is \<open>uncurry (RETURN oo clause_lbd_heur)\<close>
  :: \<open>[\<lambda>(S, C). get_clause_LBD_pre (get_clauses_wl_heur S) C]\<^sub>a
       isasat_bounded_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  unfolding clause_lbd_heur_alt_def isasat_bounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

declare  clause_lbd_heur_code2.refine[sepref_fr_rules]
    clause_lbd_heur_code.refine[sepref_fr_rules]

sepref_register mark_garbage_heur


sepref_definition mark_garbage_heur_code
  is \<open>uncurry2 (RETURN ooo mark_garbage_heur)\<close>
  :: \<open>[\<lambda>((C, i), S). mark_garbage_pre (get_clauses_wl_heur S, C) \<and> i < length_avdom S]\<^sub>a
       nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a isasat_unbounded_assn\<^sup>d \<rightarrow> isasat_unbounded_assn\<close>
  unfolding mark_garbage_heur_def isasat_unbounded_assn_def delete_index_and_swap_alt_def
    length_avdom_def
  supply [[goals_limit = 1]]
  by sepref


definition butlast_arl64 :: \<open>'a array_list64 \<Rightarrow> _\<close> where
  \<open>butlast_arl64 = (\<lambda>(xs, i). (xs, fast_minus i 1))\<close>

lemma butlast_arl_hnr[sepref_fr_rules]:
  \<open>(return o butlast_arl64, RETURN o op_list_butlast) \<in> [\<lambda>xs. xs \<noteq> []]\<^sub>a (arl64_assn A)\<^sup>d \<rightarrow> arl64_assn A\<close>
proof -
  have [simp]: \<open>b \<le> length l' \<Longrightarrow> (take b l', x) \<in> \<langle>the_pure A\<rangle>list_rel \<Longrightarrow>
     (take (b - Suc 0) l', take (length x - Suc 0) x) \<in> \<langle>the_pure A\<rangle>list_rel\<close>
    for b l' x
    using list_rel_take[of \<open>take b l'\<close> x \<open>the_pure A\<close> \<open>b -1\<close>]
    by (auto simp: list_rel_imp_same_length[symmetric]
      butlast_conv_take min_def
      simp del: take_butlast_conv)
  have [simp]: \<open>x \<noteq> [] \<Longrightarrow>
       nat_of_uint64 b \<le> length l' \<Longrightarrow>
       l' \<noteq> [] \<Longrightarrow>
       length l' \<le> uint64_max \<Longrightarrow>
       (take (nat_of_uint64 b) l', x) \<in> \<langle>the_pure A\<rangle>list_rel \<Longrightarrow>
        nat_of_uint64 (b - 1) = nat_of_uint64 b - 1\<close> for x b l'
     by (metis One_nat_def Suc_leI le_0_eq list_rel_pres_neq_nil 
         nat_of_uint64_012(3) nat_of_uint64_ge_minus nat_of_uint64_le_iff not_less take_eq_Nil)
  show ?thesis
    by sepref_to_hoare
     (sep_auto simp: butlast_arl64_def arl64_assn_def hr_comp_def is_array_list64_def
         butlast_conv_take
        simp del: take_butlast_conv)
qed

declare butlast_arl_hnr[unfolded op_list_butlast_def butlast_nonresizing_def[symmetric], sepref_fr_rules]

sepref_definition mark_garbage_heur_code2
  is \<open>uncurry2 (RETURN ooo mark_garbage_heur)\<close>
  :: \<open>[\<lambda>((C, i), S). mark_garbage_pre (get_clauses_wl_heur S, C) \<and> i < length_avdom S \<and>
         get_learned_count S \<ge> 1]\<^sub>a
       uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  unfolding mark_garbage_heur_def isasat_bounded_assn_def delete_index_and_swap_alt_def
    length_avdom_def one_uint64_nat_def[symmetric]
  supply [[goals_limit = 1]]
  by sepref

declare  mark_garbage_heur_code.refine[sepref_fr_rules]
    mark_garbage_heur_code2.refine[sepref_fr_rules]

sepref_register delete_index_vdom_heur
sepref_definition delete_index_vdom_heur_code
  is \<open>uncurry (RETURN oo delete_index_vdom_heur)\<close>
  :: \<open>[\<lambda>(i, S). i < length_avdom S]\<^sub>a
        nat_assn\<^sup>k *\<^sub>a isasat_unbounded_assn\<^sup>d \<rightarrow> isasat_unbounded_assn\<close>
  unfolding delete_index_vdom_heur_def isasat_unbounded_assn_def delete_index_and_swap_alt_def
    length_avdom_def butlast_nonresizing_def[symmetric] fast_minus_def[symmetric]
  supply [[goals_limit = 1]]
  by sepref

sepref_definition delete_index_vdom_heur_fast_code2
  is \<open>uncurry (RETURN oo delete_index_vdom_heur)\<close>
  :: \<open>[\<lambda>(i, S). i < length_avdom S]\<^sub>a
        uint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  unfolding delete_index_vdom_heur_def isasat_bounded_assn_def delete_index_and_swap_alt_def
    length_avdom_def butlast_nonresizing_def[symmetric]
  supply [[goals_limit = 1]]
  by sepref

declare delete_index_vdom_heur_code.refine[sepref_fr_rules]
  delete_index_vdom_heur_fast_code2.refine[sepref_fr_rules]

sepref_register access_length_heur
sepref_definition access_length_heur_code
  is \<open>uncurry (RETURN oo access_length_heur)\<close>
  :: \<open>[\<lambda>(S, C). arena_is_valid_clause_idx (get_clauses_wl_heur S) C]\<^sub>a
       isasat_unbounded_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  unfolding access_length_heur_alt_def isasat_unbounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

sepref_definition access_length_heur_fast_code2
  is \<open>uncurry (RETURN oo access_length_heur)\<close>
  :: \<open>[\<lambda>(S, C). arena_is_valid_clause_idx (get_clauses_wl_heur S) C]\<^sub>a
       isasat_bounded_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  unfolding access_length_heur_alt_def isasat_bounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

declare access_length_heur_code.refine[sepref_fr_rules]
  access_length_heur_fast_code2.refine[sepref_fr_rules]

(*TODO Move*)

sepref_definition isa_marked_as_used_fast_code
  is \<open>uncurry isa_marked_as_used\<close>
  :: \<open>(arl64_assn uint32_assn)\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  supply op_eq_uint32[sepref_fr_rules] STATUS_SHIFT_hnr[sepref_fr_rules]
  unfolding isa_marked_as_used_def
  by sepref

lemma isa_marked_as_used_code[sepref_fr_rules]:
  \<open>(uncurry isa_marked_as_used_fast_code, uncurry (RETURN \<circ>\<circ> marked_as_used))
     \<in> [uncurry marked_as_used_pre]\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> bool_assn\<close>
  using isa_marked_as_used_fast_code.refine[FCOMP
    isa_marked_as_used_marked_as_used[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl64_assn_comp update_lbd_pre_def)

sepref_definition isa_marked_as_used_fast_code2
  is \<open>uncurry isa_marked_as_used\<close>
  :: \<open>(arl64_assn uint32_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  supply op_eq_uint32[sepref_fr_rules] 
  unfolding isa_marked_as_used_def STATUS_SHIFT_def
  by sepref

lemma isa_marked_as_used_code2[sepref_fr_rules]:
  \<open>(uncurry isa_marked_as_used_fast_code2, uncurry (RETURN \<circ>\<circ> marked_as_used))
     \<in> [uncurry marked_as_used_pre]\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> bool_assn\<close>
  using isa_marked_as_used_fast_code2.refine[FCOMP
    isa_marked_as_used_marked_as_used[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl64_assn_comp update_lbd_pre_def)

(*END Move*)
sepref_register marked_as_used_st
sepref_definition marked_as_used_st_code
  is \<open>uncurry (RETURN oo marked_as_used_st)\<close>
  :: \<open>[\<lambda>(S, C). marked_as_used_pre (get_clauses_wl_heur S) C]\<^sub>a
       isasat_unbounded_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> bool_assn\<close>
  unfolding marked_as_used_st_alt_def isasat_unbounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

sepref_definition marked_as_used_st_fast_code
  is \<open>uncurry (RETURN oo marked_as_used_st)\<close>
  :: \<open>[\<lambda>(S, C). marked_as_used_pre (get_clauses_wl_heur S) C]\<^sub>a
       isasat_bounded_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> bool_assn\<close>
  unfolding marked_as_used_st_alt_def isasat_bounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

declare marked_as_used_st_code.refine[sepref_fr_rules]
  marked_as_used_st_fast_code.refine[sepref_fr_rules]

lemma arena_act_pre_mark_used:
  \<open>arena_act_pre arena C \<Longrightarrow>
  arena_act_pre (mark_unused arena C) C\<close>
  unfolding arena_act_pre_def arena_is_valid_clause_idx_def
  apply clarify
  apply (rule_tac x=N in exI)
  apply (rule_tac x=vdom in exI)
  by (auto simp: arena_act_pre_def
    simp: valid_arena_mark_unused)

sepref_definition mark_unused_st_code
  is \<open>uncurry (RETURN oo mark_unused_st_heur)\<close>
  :: \<open>[\<lambda>(C, S). arena_act_pre (get_clauses_wl_heur S) C]\<^sub>a
        nat_assn\<^sup>k *\<^sub>a isasat_unbounded_assn\<^sup>d \<rightarrow> isasat_unbounded_assn\<close>
  unfolding mark_unused_st_heur_def isasat_unbounded_assn_def
    arena_act_pre_mark_used[intro!]
  supply [[goals_limit = 1]]
  by sepref

(*TODO Move*)
sepref_definition isa_mark_unused_fast_code
  is \<open>uncurry isa_mark_unused\<close>
  :: \<open>(arl64_assn uint32_assn)\<^sup>d *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a (arl64_assn uint32_assn)\<close>
  unfolding isa_mark_unused_def supply STATUS_SHIFT_hnr[sepref_fr_rules]
  by sepref

lemma isa_mark_unused_code[sepref_fr_rules]:
  \<open>(uncurry isa_mark_unused_fast_code, uncurry (RETURN \<circ>\<circ> mark_unused))
     \<in> [uncurry arena_act_pre]\<^sub>a arena_fast_assn\<^sup>d *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> arena_fast_assn\<close>
  using isa_mark_unused_fast_code.refine[FCOMP isa_mark_unused_mark_unused[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl64_assn_comp)

sepref_definition isa_mark_unused_fast_code2
  is \<open>uncurry isa_mark_unused\<close>
  :: \<open>(arl64_assn uint32_assn)\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a (arl64_assn uint32_assn)\<close>
  unfolding isa_mark_unused_def STATUS_SHIFT_def
  by sepref

lemma isa_mark_unused_code2[sepref_fr_rules]:
  \<open>(uncurry isa_mark_unused_fast_code2, uncurry (RETURN \<circ>\<circ> mark_unused))
     \<in> [uncurry arena_act_pre]\<^sub>a arena_fast_assn\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow> arena_fast_assn\<close>
  using isa_mark_unused_fast_code2.refine[FCOMP isa_mark_unused_mark_unused[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl64_assn_comp)

sepref_definition isa_arena_decr_act_fast_code2
  is \<open>uncurry isa_arena_decr_act\<close>
  :: \<open>(arl64_assn uint32_assn)\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a (arl64_assn uint32_assn)\<close>
  unfolding isa_arena_decr_act_def
  three_uint32_def[symmetric] ACTIVITY_SHIFT_def
  by sepref

lemma isa_arena_decr_act_fast_code2[sepref_fr_rules]:
  \<open>(uncurry isa_arena_decr_act_fast_code2, uncurry (RETURN \<circ>\<circ> arena_decr_act))
     \<in> [uncurry arena_act_pre]\<^sub>a arena_fast_assn\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow> arena_fast_assn\<close>
  using isa_arena_decr_act_fast_code2.refine[FCOMP isa_arena_decr_act_arena_decr_act[unfolded convert_fref]]
  unfolding hr_comp_assoc[symmetric] list_rel_compp status_assn_alt_def uncurry_def
  by (auto simp add: arl64_assn_comp)


(*END Move*)

sepref_register mark_unused_st_heur
sepref_definition mark_unused_st_fast_code
  is \<open>uncurry (RETURN oo mark_unused_st_heur)\<close>
  :: \<open>[\<lambda>(C, S). arena_act_pre (get_clauses_wl_heur S) C]\<^sub>a
        uint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  unfolding mark_unused_st_heur_def isasat_bounded_assn_def
    arena_act_pre_mark_used[intro!]
  supply [[goals_limit = 1]]
  by sepref

declare mark_unused_st_code.refine[sepref_fr_rules]
  mark_unused_st_fast_code.refine[sepref_fr_rules]


sepref_register mark_clauses_as_unused_wl_D_heur
sepref_definition mark_clauses_as_unused_wl_D_heur_code
  is \<open>uncurry mark_clauses_as_unused_wl_D_heur\<close>
  :: \<open>nat_assn\<^sup>k *\<^sub>a isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding mark_clauses_as_unused_wl_D_heur_def
    mark_unused_st_heur_def[symmetric]
    access_vdom_at_def[symmetric] length_avdom_def[symmetric]
    arena_act_pre_mark_used[intro!]
  by sepref



declare clause_not_marked_to_delete_heur_fast_code.refine[sepref_fr_rules]

sepref_definition mark_clauses_as_unused_wl_D_heur_fast_code
  is \<open>uncurry mark_clauses_as_unused_wl_D_heur\<close>
  :: \<open>[\<lambda>(_, S). length (get_avdom S) \<le> uint64_max]\<^sub>a
    uint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]] length_avdom_def[simp]
  unfolding mark_clauses_as_unused_wl_D_heur_def
    mark_unused_st_heur_def[symmetric] one_uint64_nat_def[symmetric]
    access_vdom_at_def[symmetric] length_avdom_def[symmetric]
  by sepref

declare mark_clauses_as_unused_wl_D_heur_fast_code.refine[sepref_fr_rules]
  mark_clauses_as_unused_wl_D_heur_code.refine[sepref_fr_rules]


sepref_register mark_to_delete_clauses_wl_D_heur
sepref_definition mark_to_delete_clauses_wl_D_heur_impl
  is \<open>mark_to_delete_clauses_wl_D_heur\<close>
  :: \<open>isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
  supply if_splits[split]
  unfolding mark_to_delete_clauses_wl_D_heur_def
    access_vdom_at_def[symmetric] length_avdom_def[symmetric]
    get_the_propagation_reason_heur_def[symmetric]
    clause_is_learned_heur_def[symmetric]
    clause_lbd_heur_def[symmetric]
    access_length_heur_def[symmetric]
    short_circuit_conv
    marked_as_used_st_def[symmetric]
  supply [[goals_limit = 1]]
  by sepref

(* TODO Move *)
declare sort_vdom_heur_fast_code.refine[sepref_fr_rules]
  sort_vdom_heur_fast_code.refine[sepref_fr_rules]

declare access_lit_in_clauses_heur_fast_code.refine[sepref_fr_rules]

(* END Move *)
text \<open>Find a less hack-like solution\<close>
setup \<open>map_theory_claset (fn ctxt => ctxt delSWrapper "split_all_tac")\<close>

sepref_definition mark_to_delete_clauses_wl_D_heur_fast_impl
  is \<open>mark_to_delete_clauses_wl_D_heur\<close>
  :: \<open>[\<lambda>S. length (get_clauses_wl_heur S) \<le> uint64_max]\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  unfolding mark_to_delete_clauses_wl_D_heur_def
    access_vdom_at_def[symmetric] length_avdom_def[symmetric]
    get_the_propagation_reason_heur_def[symmetric]
    clause_is_learned_heur_def[symmetric]
    clause_lbd_heur_def[symmetric] nat_of_uint64_conv_def
    access_length_heur_def[symmetric] zero_uint64_nat_def[symmetric]
    short_circuit_conv mark_to_delete_clauses_wl_D_heur_is_Some_iff
    marked_as_used_st_def[symmetric] one_uint64_nat_def[symmetric]
  supply [[goals_limit = 1]] option.splits[split] if_splits[split]
    length_avdom_def[symmetric, simp] access_vdom_at_def[simp]
  by sepref

declare mark_to_delete_clauses_wl_D_heur_fast_impl.refine[sepref_fr_rules]
  mark_to_delete_clauses_wl_D_heur_impl.refine[sepref_fr_rules]

sepref_register cdcl_twl_full_restart_wl_prog_heur
sepref_definition cdcl_twl_full_restart_wl_prog_heur_code
  is \<open>cdcl_twl_full_restart_wl_prog_heur\<close>
  :: \<open>isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
  unfolding cdcl_twl_full_restart_wl_prog_heur_def
  supply [[goals_limit = 1]]
  by sepref

sepref_definition cdcl_twl_full_restart_wl_prog_heur_fast_code
  is \<open>cdcl_twl_full_restart_wl_prog_heur\<close>
  :: \<open>[\<lambda>S. length (get_clauses_wl_heur S) \<le> uint64_max]\<^sub>a  isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  unfolding cdcl_twl_full_restart_wl_prog_heur_def
  supply [[goals_limit = 1]]
  by sepref

declare cdcl_twl_full_restart_wl_prog_heur_fast_code.refine[sepref_fr_rules]
   cdcl_twl_full_restart_wl_prog_heur_code.refine[sepref_fr_rules]

sepref_definition cdcl_twl_restart_wl_heur_code
  is \<open>cdcl_twl_restart_wl_heur\<close>
  :: \<open>isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
  unfolding cdcl_twl_restart_wl_heur_def
  supply [[goals_limit = 1]]
  by sepref

sepref_definition cdcl_twl_restart_wl_heur_fast_code
  is \<open>cdcl_twl_restart_wl_heur\<close>
  :: \<open>[\<lambda>S. length (get_clauses_wl_heur S) \<le> uint64_max]\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  unfolding cdcl_twl_restart_wl_heur_def
  supply [[goals_limit = 1]]
  by sepref

declare cdcl_twl_restart_wl_heur_fast_code.refine[sepref_fr_rules]
   cdcl_twl_restart_wl_heur_code.refine[sepref_fr_rules]

sepref_definition cdcl_twl_full_restart_wl_D_GC_heur_prog_code
  is \<open>cdcl_twl_full_restart_wl_D_GC_heur_prog\<close>
  :: \<open>isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
  unfolding cdcl_twl_full_restart_wl_D_GC_heur_prog_def zero_uint32_nat_def[symmetric]
  supply [[goals_limit = 1]]
  by sepref

sepref_definition cdcl_twl_full_restart_wl_D_GC_heur_prog_fast_code
  is \<open>cdcl_twl_full_restart_wl_D_GC_heur_prog\<close>
  :: \<open>[\<lambda>S. length (get_clauses_wl_heur S) \<le> uint64_max]\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  unfolding cdcl_twl_full_restart_wl_D_GC_heur_prog_def zero_uint32_nat_def[symmetric]
  supply [[goals_limit = 1]]
  by sepref

declare cdcl_twl_full_restart_wl_D_GC_heur_prog_code.refine[sepref_fr_rules]
  cdcl_twl_restart_wl_heur_fast_code.refine[sepref_fr_rules]
    cdcl_twl_full_restart_wl_D_GC_heur_prog_code.refine[sepref_fr_rules]
  cdcl_twl_full_restart_wl_D_GC_heur_prog_fast_code.refine[sepref_fr_rules]

declare cdcl_twl_restart_wl_heur_fast_code.refine[sepref_fr_rules]
   cdcl_twl_restart_wl_heur_code.refine[sepref_fr_rules]

sepref_register restart_required_heur cdcl_twl_restart_wl_heur
sepref_definition restart_wl_D_heur_slow_code
  is \<open>uncurry2 restart_prog_wl_D_heur\<close>
  :: \<open>isasat_unbounded_assn\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a bool_assn\<^sup>k \<rightarrow>\<^sub>a isasat_unbounded_assn *a nat_assn\<close>
  unfolding restart_prog_wl_D_heur_def
  supply [[goals_limit = 1]]
  by sepref

sepref_definition restart_prog_wl_D_heur_fast_code
  is \<open>uncurry2 (restart_prog_wl_D_heur)\<close>
  :: \<open>[\<lambda>((S, _), _). length (get_clauses_wl_heur S) \<le> uint64_max]\<^sub>a
      isasat_bounded_assn\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a bool_assn\<^sup>k \<rightarrow> isasat_bounded_assn *a nat_assn\<close>
  unfolding restart_prog_wl_D_heur_def
  supply [[goals_limit = 1]]
  by sepref

declare restart_wl_D_heur_slow_code.refine[sepref_fr_rules]
   restart_prog_wl_D_heur_fast_code.refine[sepref_fr_rules]

sepref_definition cdcl_twl_stgy_restart_prog_wl_heur_code
  is \<open>cdcl_twl_stgy_restart_prog_wl_heur\<close>
  :: \<open>isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
  unfolding cdcl_twl_stgy_restart_prog_wl_heur_def
  supply [[goals_limit = 1]]
  by sepref

declare cdcl_twl_stgy_restart_prog_wl_heur_code.refine[sepref_fr_rules]

definition isasat_fast_bound where
  \<open>isasat_fast_bound = uint64_max - (uint32_max div 2 + 6)\<close>

lemma isasat_fast_bound[sepref_fr_rules]:
   \<open>(uncurry0 (return 18446744071562067962), uncurry0 (RETURN isasat_fast_bound)) \<in>
   unit_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint64_nat_rel_def br_def isasat_fast_bound_def
     uint64_max_def uint32_max_def)

sepref_register isasat_fast
sepref_definition isasat_fast_code
  is \<open>RETURN o isasat_fast\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding isasat_fast_alt_def isasat_bounded_assn_def isasat_fast_bound_def[symmetric]
  supply [[goals_limit = 1]] uint32_max_nat_hnr[sepref_fr_rules]
  by sepref

declare isasat_fast_code.refine[sepref_fr_rules]


sepref_definition cdcl_twl_stgy_restart_prog_wl_heur_fast_code
  is \<open>cdcl_twl_stgy_restart_prog_early_wl_heur\<close>
  :: \<open>[\<lambda>S. isasat_fast S]\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_unbounded_assn\<close>
  unfolding cdcl_twl_stgy_restart_prog_early_wl_heur_def
  supply [[goals_limit = 1]] isasat_fast_def[simp]
  by sepref

declare cdcl_twl_stgy_restart_prog_wl_heur_fast_code.refine[sepref_fr_rules]

end