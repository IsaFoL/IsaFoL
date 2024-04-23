theory IsaSAT_Propagate_Conflict_LLVM
  imports IsaSAT_Propagate_Conflict_Defs IsaSAT_Inner_Propagation_LLVM
begin

(*TODO Move*)


lemma unit_propagation_inner_loop_wl_loop_D_heur_fast:
  \<open>length (get_clauses_wl_heur b) \<le> snat64_max \<Longrightarrow>
    unit_propagation_inner_loop_wl_loop_D_heur_inv b a (ticks, a1', a1'a, a2'a) \<Longrightarrow>
     length (get_clauses_wl_heur a2'a) \<le> snat64_max\<close>
  unfolding unit_propagation_inner_loop_wl_loop_D_heur_inv_def
  by auto

sepref_def unit_propagation_inner_loop_wl_loop_D_fast
  is \<open>uncurry unit_propagation_inner_loop_wl_loop_D_heur\<close>
  :: \<open>[\<lambda>(L, S). length (get_clauses_wl_heur S) \<le> snat64_max]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> word64_assn \<times>\<^sub>a sint64_nat_assn \<times>\<^sub>a sint64_nat_assn \<times>\<^sub>a isasat_bounded_assn\<close>
  unfolding unit_propagation_inner_loop_wl_loop_D_heur_def PR_CONST_def
  unfolding watched_by_nth_watched_app watched_app_def[symmetric]
    length_ll_fs_heur_def[symmetric]
  unfolding delete_index_and_swap_update_def[symmetric] append_update_def[symmetric]
    is_None_def[symmetric] get_conflict_wl_is_None_heur_alt_def[symmetric]
  unfolding fold_tuple_optimizations
  supply [[goals_limit=1]] unit_propagation_inner_loop_wl_loop_D_heur_fast[intro] length_ll_fs_heur_def[simp]
  apply (annot_snat_const \<open>TYPE (64)\<close>)
  by sepref

lemma le_unat64_max_minus_4_unat64_max: \<open>a \<le> snat64_max - MIN_HEADER_SIZE \<Longrightarrow> Suc a < max_snat 64\<close>
  by (auto simp: snat64_max_def max_snat_def)

definition cut_watch_list_heur2_inv where
  \<open>cut_watch_list_heur2_inv L n = (\<lambda>(j, w, W). j \<le> w \<and> w \<le> n \<and> nat_of_lit L < length W)\<close>

lemma cut_watch_list_heur2_alt_def:
\<open>cut_watch_list_heur2 = (\<lambda>j w L S\<^sub>0. do {
  let (W, S) = extract_watchlist_wl_heur S\<^sub>0;
  ASSERT (W = get_watched_wl_heur S\<^sub>0);
  ASSERT(j \<le> length (W ! nat_of_lit L) \<and> j \<le> w \<and> nat_of_lit L < length W \<and>
     w \<le> length (W ! (nat_of_lit L)));
  let n = length (W!(nat_of_lit L));
  (j, w, W) \<leftarrow> WHILE\<^sub>T\<^bsup>cut_watch_list_heur2_inv L n\<^esup>
    (\<lambda>(j, w, W). w < n)
    (\<lambda>(j, w, W). do {
      ASSERT(w < length (W!(nat_of_lit L)));
      RETURN (j+1, w+1, W[nat_of_lit L := (W!(nat_of_lit L))[j := W!(nat_of_lit L)!w]])
    })
    (j, w, W);
  ASSERT(j \<le> length (W ! nat_of_lit L) \<and> nat_of_lit L < length W);
  let W = W[nat_of_lit L := take j (W ! nat_of_lit L)];
  RETURN (update_watchlist_wl_heur W S)
})\<close>
  unfolding cut_watch_list_heur2_inv_def  cut_watch_list_heur2_def
  by (auto simp: state_extractors Let_def intro!: ext split: isasat_int_splits)

lemma cut_watch_list_heur2I:
  \<open>length (a1'd ! nat_of_lit baa) \<le> snat64_max - MIN_HEADER_SIZE \<Longrightarrow>
       cut_watch_list_heur2_inv baa (length (a1'd ! nat_of_lit baa))
        (a1'e, a1'f, a2'f) \<Longrightarrow>
       a1'f < length_ll a2'f (nat_of_lit baa) \<Longrightarrow>
       ez \<le> bba \<Longrightarrow>
       Suc a1'e < max_snat 64\<close>
  \<open>length (a1'd ! nat_of_lit baa) \<le> snat64_max - MIN_HEADER_SIZE \<Longrightarrow>
       cut_watch_list_heur2_inv baa (length (a1'd ! nat_of_lit baa))
        (a1'e, a1'f, a2'f) \<Longrightarrow>
       a1'f < length_ll a2'f (nat_of_lit baa) \<Longrightarrow>
       ez \<le> bba \<Longrightarrow>
       Suc a1'f < max_snat 64\<close>
  \<open>cut_watch_list_heur2_inv baa (length (a1'd ! nat_of_lit baa))
        (a1'e, a1'f, a2'f) \<Longrightarrow> nat_of_lit baa < length a2'f\<close>
  \<open>cut_watch_list_heur2_inv baa (length (a1'd ! nat_of_lit baa))
        (a1'e, a1'f, a2'f) \<Longrightarrow> a1'f < length_ll a2'f (nat_of_lit baa) \<Longrightarrow>
       a1'e < length (a2'f ! nat_of_lit baa)\<close>
  by (auto simp: max_snat_def snat64_max_def cut_watch_list_heur2_inv_def length_ll_def)

sepref_def cut_watch_list_heur2_fast_code
  is \<open>uncurry3 cut_watch_list_heur2\<close>
  :: \<open>[\<lambda>(((j, w), L), S). length (watched_by_int S L) \<le> snat64_max-MIN_HEADER_SIZE]\<^sub>a
     sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a
     isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]] cut_watch_list_heur2I[intro] length_ll_def[simp]
  unfolding cut_watch_list_heur2_alt_def length_ll_def[symmetric]
    nth_rll_def[symmetric] watched_by_alt_def
    op_list_list_take_alt_def[symmetric]
    op_list_list_upd_alt_def[symmetric]
  apply (annot_snat_const \<open>TYPE (64)\<close>)
  by sepref


sepref_def unit_propagation_inner_loop_wl_D_fast_code
  is \<open>uncurry unit_propagation_inner_loop_wl_D_heur\<close>
  :: \<open>[\<lambda>(L, S). length (get_clauses_wl_heur S) \<le> snat64_max]\<^sub>a
        unat_lit_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> word64_assn \<times>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding PR_CONST_def unit_propagation_inner_loop_wl_D_heur_def
  by sepref

lemma [sepref_fr_rules]: \<open>(Mreturn o Tuple17_get_d, RETURN o literals_to_update_wl_heur) \<in> isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a sint64_nat_assn\<close>
  supply [split] =  isasat_int_splits
  unfolding isasat_bounded_assn_def
  by sepref_to_hoare vcg'

lemma select_and_remove_from_literals_to_update_wl_heur_alt_def:
\<open>select_and_remove_from_literals_to_update_wl_heur S = do {
    ASSERT(literals_to_update_wl_heur S < length (fst (get_trail_wl_heur S)));
    ASSERT(literals_to_update_wl_heur S + 1 \<le> unat32_max);
    let (j, T) = extract_literals_to_update_wl_heur S;
    ASSERT (j = literals_to_update_wl_heur S);
    L \<leftarrow> isa_trail_nth (get_trail_wl_heur T) j;
    RETURN (update_literals_to_update_wl_heur (j + 1) T, -L)
  }\<close>
  by (cases S) (auto simp: select_and_remove_from_literals_to_update_wl_heur_def state_extractors
    intro!: ext split: isasat_int_splits)

sepref_def select_and_remove_from_literals_to_update_wlfast_code
  is \<open>select_and_remove_from_literals_to_update_wl_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn \<times>\<^sub>a unat_lit_assn\<close>
  supply [[goals_limit=1]]
  unfolding select_and_remove_from_literals_to_update_wl_heur_alt_def isasat_trail_nth_st_def[symmetric]
  unfolding fold_tuple_optimizations
  supply [[goals_limit = 1]]
  apply (annot_snat_const \<open>TYPE (64)\<close>)
  by sepref


lemma unit_propagation_outer_loop_wl_D_heur_fast:
  \<open>length (get_clauses_wl_heur x) \<le> snat64_max \<Longrightarrow>
       unit_propagation_outer_loop_wl_D_heur_inv x s' \<Longrightarrow>
       length (get_clauses_wl_heur a1') =
       length (get_clauses_wl_heur s') \<Longrightarrow>
       length (get_clauses_wl_heur s') \<le> snat64_max\<close>
  by (auto simp: unit_propagation_outer_loop_wl_D_heur_inv_def)

lemma unit_propagation_outer_loop_wl_D_invI:
  \<open>unit_propagation_outer_loop_wl_D_heur_inv S\<^sub>0 S \<Longrightarrow>
    isa_length_trail_pre (get_trail_wl_heur S)\<close>
  unfolding unit_propagation_outer_loop_wl_D_heur_inv_def
  by blast

sepref_def unit_propagation_outer_loop_wl_D_fast_code
  is \<open>unit_propagation_outer_loop_wl_D_heur\<close>
  :: \<open>[\<lambda>S. length (get_clauses_wl_heur S) \<le> snat64_max]\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]] unit_propagation_outer_loop_wl_D_heur_fast[intro] of_nat_snat[sepref_import_param]
    unit_propagation_outer_loop_wl_D_invI[intro]
  unfolding unit_propagation_outer_loop_wl_D_heur_def isasat_length_trail_st_def[symmetric]
  by sepref

sepref_register unit_propagation_outer_loop_wl_D_heur

experiment begin

export_llvm
  length_ll_fs_heur_fast_code
  unit_propagation_inner_loop_wl_loop_D_fast
  cut_watch_list_heur2_fast_code
  unit_propagation_inner_loop_wl_D_fast_code
  isa_trail_nth_fast_code
  select_and_remove_from_literals_to_update_wlfast_code
  unit_propagation_outer_loop_wl_D_fast_code

end

end

