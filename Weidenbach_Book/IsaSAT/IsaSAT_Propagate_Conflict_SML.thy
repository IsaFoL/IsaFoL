theory IsaSAT_Propagate_Conflict_SML
  imports IsaSAT_Propagate_Conflict IsaSAT_Inner_Propagation_SML
begin
sepref_definition length_ll_fs_heur_code
  is \<open>uncurry (RETURN oo length_ll_fs_heur)\<close>
  :: \<open>[\<lambda>(S, L). nat_of_lit L < length (get_watched_wl_heur S)]\<^sub>a
      isasat_unbounded_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> nat_assn\<close>
  unfolding length_ll_fs_heur_alt_def get_watched_wl_heur_def isasat_unbounded_assn_def
    length_ll_def[symmetric]
  supply [[goals_limit=1]]
  by sepref

declare length_ll_fs_heur_code.refine[sepref_fr_rules]

definition length_aa64_u32 :: \<open>('a::heap array_list64) array \<Rightarrow> uint32 \<Rightarrow> uint64 Heap\<close> where
  \<open>length_aa64_u32 xs i = do {
     x \<leftarrow> nth_u_code xs i;
    arl64_length x}\<close>

lemma length_aa64_rule[sep_heap_rules]:
    \<open>b < length xs \<Longrightarrow> (b', b) \<in> uint32_nat_rel \<Longrightarrow> <arrayO_assn (arl64_assn R) xs a> length_aa64_u32 a b'
    <\<lambda>r. arrayO_assn (arl64_assn R) xs a * \<up> (nat_of_uint64 r = length_ll xs b)>\<^sub>t\<close>
  unfolding length_aa64_u32_def nth_u_code_def Array.nth'_def
  apply (sep_auto simp flip: nat_of_uint32_code simp: br_def uint32_nat_rel_def length_ll_def)
  apply (subst arrayO_except_assn_array0_index[symmetric, of b])
  apply (simp add: nat_of_uint32_code br_def uint32_nat_rel_def)
  apply (sep_auto simp: arrayO_except_assn_def)
  done

lemma length_aa64_u32_hnr[sepref_fr_rules]: \<open>(uncurry length_aa64_u32, uncurry (RETURN \<circ>\<circ> length_ll)) \<in>
     [\<lambda>(xs, i). i < length xs]\<^sub>a (arrayO_assn (arl64_assn R))\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def br_def uint64_nat_rel_def)

sepref_definition length_ll_fs_heur_fast_code
  is \<open>uncurry (RETURN oo length_ll_fs_heur)\<close>
  :: \<open>[\<lambda>(S, L). nat_of_lit L < length (get_watched_wl_heur S)]\<^sub>a
      isasat_bounded_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  unfolding length_ll_fs_heur_alt_def get_watched_wl_heur_def isasat_bounded_assn_def
    length_ll_def[symmetric]
  supply [[goals_limit=1]] length_ll_def[simp]
  by sepref

declare length_ll_fs_heur_fast_code.refine[sepref_fr_rules]

sepref_register unit_propagation_inner_loop_body_wl_heur

sepref_definition unit_propagation_inner_loop_wl_loop_D
  is \<open>uncurry unit_propagation_inner_loop_wl_loop_D_heur\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a nat_assn \<times>\<^sub>a nat_assn \<times>\<^sub>a isasat_unbounded_assn\<close>
  unfolding unit_propagation_inner_loop_wl_loop_D_heur_def PR_CONST_def
  unfolding watched_by_nth_watched_app watched_app_def[symmetric]
    length_ll_fs_heur_def[symmetric]
  unfolding nth_ll_def[symmetric]
  unfolding swap_ll_def[symmetric]
  unfolding delete_index_and_swap_update_def[symmetric] append_update_def[symmetric]
    is_None_def[symmetric] get_conflict_wl_is_None_heur_alt_def[symmetric]
    length_ll_fs_def[symmetric]
  supply [[goals_limit=1]]
  by sepref

declare unit_propagation_inner_loop_wl_loop_D.refine[sepref_fr_rules]


sepref_definition unit_propagation_inner_loop_wl_loop_D_fast
  is \<open>uncurry unit_propagation_inner_loop_wl_loop_D_heur\<close>
  :: \<open>[\<lambda>(L, S). length (get_clauses_wl_heur S) \<le> uint64_max]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> uint64_nat_assn \<times>\<^sub>a uint64_nat_assn \<times>\<^sub>a isasat_bounded_assn\<close>
  unfolding unit_propagation_inner_loop_wl_loop_D_heur_def PR_CONST_def
  unfolding watched_by_nth_watched_app watched_app_def[symmetric]
    length_ll_fs_heur_def[symmetric]
  unfolding nth_ll_def[symmetric]
  unfolding swap_ll_def[symmetric]
  unfolding delete_index_and_swap_update_def[symmetric] append_update_def[symmetric]
    is_None_def[symmetric] get_conflict_wl_is_None_heur_alt_def[symmetric]
    length_ll_fs_def[symmetric] zero_uint64_nat_def[symmetric]
  supply [[goals_limit=1]] unit_propagation_inner_loop_wl_loop_D_heur_fast[intro]
  by sepref

declare unit_propagation_inner_loop_wl_loop_D_fast.refine[sepref_fr_rules]

sepref_register length_ll_fs_heur

sepref_register unit_propagation_inner_loop_wl_loop_D_heur cut_watch_list_heur2
sepref_definition cut_watch_list_heur2_code
  is \<open>uncurry3 cut_watch_list_heur2\<close>
  :: \<open>nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a
     isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
  supply [[goals_limit=1]] length_ll_def[simp]
  unfolding cut_watch_list_heur2_def isasat_unbounded_assn_def length_ll_def[symmetric]
  update_ll_def[symmetric] nth_rll_def[symmetric] shorten_take_ll_def[symmetric]
  by sepref

declare cut_watch_list_heur2_code.refine[sepref_fr_rules]

definition (in -) shorten_take_aa64_u32 where
  \<open>shorten_take_aa64_u32 L j W =  do {
      (a, n) \<leftarrow> nth_u_code W L;
      Array_upd_u L (a, j) W
    }\<close>

lemma shorten_take_aa_hnr[sepref_fr_rules]:
  \<open>(uncurry2 shorten_take_aa64_u32, uncurry2 (RETURN ooo shorten_take_ll)) \<in>
     [\<lambda>((L, j), W). j \<le> length (W ! L) \<and> L < length W]\<^sub>a
    uint32_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a (arrayO_assn (arl64_assn R))\<^sup>d \<rightarrow> arrayO_assn (arl64_assn R)\<close>
  unfolding shorten_take_aa64_u32_def shorten_take_ll_def nth_u_code_def Array.nth'_def
    comp_def nat_of_uint32_code[symmetric] Array_upd_u_def
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def br_def uint64_nat_rel_def)

find_theorems shorten_take_ll arl64_assn
thm shorten_take_aa_hnr
sepref_definition cut_watch_list_heur2_fast_code
  is \<open>uncurry3 cut_watch_list_heur2\<close>
  :: \<open>[\<lambda>(((j, w), L), S). length (watched_by_int S L) \<le> uint64_max-4]\<^sub>a
     uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a
     isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]] length_ll_def[simp] uint64_max_def[simp] length_rll_def[simp]
  unfolding cut_watch_list_heur2_def isasat_bounded_assn_def length_ll_def[symmetric]
  update_ll_def[symmetric] nth_rll_def[symmetric] shorten_take_ll_def[symmetric]
  one_uint64_nat_def[symmetric] length_rll_def[symmetric]
  by sepref

declare cut_watch_list_heur2_fast_code.refine[sepref_fr_rules]

sepref_definition unit_propagation_inner_loop_wl_D_code
  is \<open>uncurry unit_propagation_inner_loop_wl_D_heur\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding PR_CONST_def unit_propagation_inner_loop_wl_D_heur_def
  by sepref

declare unit_propagation_inner_loop_wl_D_code.refine[sepref_fr_rules]

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
  :: \<open>isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn \<times>\<^sub>a unat_lit_assn\<close>
  supply [[goals_limit=1]] uint32_nat_assn_plus[sepref_fr_rules]
  unfolding select_and_remove_from_literals_to_update_wl_heur_alt_def isasat_unbounded_assn_def
    one_uint32_nat_def[symmetric]
  supply [[goals_limit = 1]]
  by sepref

declare select_and_remove_from_literals_to_update_wl_code.refine[sepref_fr_rules]

sepref_definition select_and_remove_from_literals_to_update_wlfast_code
  is \<open>select_and_remove_from_literals_to_update_wl_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn \<times>\<^sub>a unat_lit_assn\<close>
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