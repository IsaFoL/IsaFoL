theory IsaSAT_Propagate_Conflict
  imports IsaSAT_Setup IsaSAT_Inner_Propagation
begin


subsubsection \<open>Refining Propagate And Conflict\<close>

paragraph \<open>Unit Propagation, Inner Loop\<close>

definition (in -) length_ll_fs :: \<open>nat twl_st_wl \<Rightarrow> nat literal \<Rightarrow> nat\<close> where
  \<open>length_ll_fs = (\<lambda>(_, _, _, _, _, _, W) L. length (W L))\<close>

definition (in -) length_ll_fs_heur :: \<open>twl_st_wl_heur \<Rightarrow> nat literal \<Rightarrow> nat\<close> where
  \<open>length_ll_fs_heur S L = length (watched_by_int S L)\<close>

lemma length_ll_fs_heur_alt_def:
  \<open>length_ll_fs_heur = (\<lambda>(M, N, D, Q, W, _) L. length (W ! nat_of_lit L))\<close>
  unfolding length_ll_fs_heur_def
  apply (intro ext)
  apply (case_tac S)
  by auto

lemma (in -) get_watched_wl_heur_def: \<open>get_watched_wl_heur = (\<lambda>(M, N, D, Q, W, _). W)\<close>
  by (intro ext, rename_tac x, case_tac x) auto

sepref_definition length_ll_fs_heur_code
  is \<open>uncurry (RETURN oo length_ll_fs_heur)\<close>
  :: \<open>[\<lambda>(S, L). nat_of_lit L < length (get_watched_wl_heur S)]\<^sub>a
      isasat_unbounded_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> nat_assn\<close>
  unfolding length_ll_fs_heur_alt_def get_watched_wl_heur_def isasat_unbounded_assn_def
    length_ll_def[symmetric]
  supply [[goals_limit=1]]
  by sepref

declare length_ll_fs_heur_code.refine[sepref_fr_rules]

sepref_definition length_ll_fs_heur_fast_code
  is \<open>uncurry (RETURN oo length_ll_fs_heur)\<close>
  :: \<open>[\<lambda>(S, L). nat_of_lit L < length (get_watched_wl_heur S)]\<^sub>a
      isasat_bounded_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow>nat_assn\<close>
  unfolding length_ll_fs_heur_alt_def get_watched_wl_heur_def isasat_bounded_assn_def
    length_ll_def[symmetric]
  supply [[goals_limit=1]] length_ll_def[simp]
  by sepref

declare length_ll_fs_heur_fast_code.refine[sepref_fr_rules]

sepref_register unit_propagation_inner_loop_body_wl_heur

sepref_definition unit_propagation_inner_loop_wl_loop_D
  is \<open>uncurry unit_propagation_inner_loop_wl_loop_D_heur\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a nat_assn *a nat_assn *a isasat_unbounded_assn\<close>
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

lemma unit_propagation_inner_loop_wl_loop_D_heur_fast:
  \<open>length (get_clauses_wl_heur b) \<le> uint64_max \<Longrightarrow>
    unit_propagation_inner_loop_wl_loop_D_heur_inv b a (a1', a1'a, a2'a) \<Longrightarrow>
     length (get_clauses_wl_heur a2'a) \<le> uint64_max\<close>
  unfolding unit_propagation_inner_loop_wl_loop_D_heur_inv_def
  by auto

sepref_definition unit_propagation_inner_loop_wl_loop_D_fast
  is \<open>uncurry unit_propagation_inner_loop_wl_loop_D_heur\<close>
  :: \<open>[\<lambda>(L, S). length (get_clauses_wl_heur S) \<le> uint64_max]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> uint64_nat_assn *a uint64_nat_assn *a isasat_bounded_assn\<close>
  unfolding unit_propagation_inner_loop_wl_loop_D_heur_def PR_CONST_def
  unfolding watched_by_nth_watched_app watched_app_def[symmetric]
    length_ll_fs_heur_def[symmetric]
  unfolding nth_ll_def[symmetric]
  unfolding swap_ll_def[symmetric]
  unfolding delete_index_and_swap_update_def[symmetric] append_update_def[symmetric]
    is_None_def[symmetric] get_conflict_wl_is_None_heur_alt_def[symmetric]
    length_ll_fs_def[symmetric] zero_uint64_nat_def[symmetric]
  apply (rewrite at \<open>let _ = \<hole> in _\<close> uint64_of_nat_conv_def[symmetric])
  supply [[goals_limit=1]] unit_propagation_inner_loop_wl_loop_D_heur_fast[intro]
  by sepref

declare unit_propagation_inner_loop_wl_loop_D_fast.refine[sepref_fr_rules]

lemma unit_propagation_inner_loop_wl_loop_D_heur_alt_def:
  \<open>unit_propagation_inner_loop_wl_loop_D_heur L S\<^sub>0 = do {
    ASSERT (nat_of_lit L < length (get_watched_wl_heur S\<^sub>0));
     ASSERT (length (watched_by_int S\<^sub>0 L) \<le> length (get_clauses_wl_heur S\<^sub>0));
    let n = length (watched_by_int S\<^sub>0 L);
    let b = (zero_uint64_nat, zero_uint64_nat, S\<^sub>0);
    WHILE\<^sub>T\<^bsup>unit_propagation_inner_loop_wl_loop_D_heur_inv S\<^sub>0 L\<^esup>
      (\<lambda>(j, w, S). w < n \<and> get_conflict_wl_is_None_heur S)
      (\<lambda>(j, w, S). do {
        unit_propagation_inner_loop_body_wl_heur L j w S
      })
      b
  }\<close>
  unfolding unit_propagation_inner_loop_wl_loop_D_heur_def Let_def zero_uint64_nat_def ..


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


find_theorems shorten_take_ll
thm shorten_take_aa_u32_hnr
sepref_definition cut_watch_list_heur2_fast_code
  is \<open>uncurry3 cut_watch_list_heur2\<close>
  :: \<open>[\<lambda>(((j, w), L), S). length (watched_by_int S L) \<le> uint64_max-4]\<^sub>a
     uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a
     isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]] length_ll_def[simp] uint64_max_def[simp] length_rll_def[simp]
  unfolding cut_watch_list_heur2_def isasat_bounded_assn_def length_ll_def[symmetric]
  update_ll_def[symmetric] nth_rll_def[symmetric] shorten_take_ll_def[symmetric]
  one_uint64_nat_def[symmetric] length_rll_def[symmetric]
  apply (rewrite in \<open>shorten_take_ll _ \<hole> _\<close> nat_of_uint64_conv_def[symmetric])
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


paragraph \<open>Unit propagation, Outer Loop\<close>

lemma select_and_remove_from_literals_to_update_wl_heur_alt_def:
  \<open>select_and_remove_from_literals_to_update_wl_heur =
   (\<lambda>(M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema, ccount,
       vdom, lcount). do {
      ASSERT(j < length (fst M'));
      ASSERT(j + 1 \<le> uint32_max);
      L \<leftarrow> isa_trail_nth M' j;
      RETURN ((M', N', D', j+1, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema, ccount,
       vdom, lcount), -L)
     })
    \<close>
  unfolding select_and_remove_from_literals_to_update_wl_heur_def
  apply (intro ext)
  apply (rename_tac S; case_tac S)
  by (auto intro!: ext simp: rev_trail_nth_def Let_def)

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

definition  literals_to_update_wl_literals_to_update_wl_empty :: \<open>twl_st_wl_heur \<Rightarrow> bool\<close> where
  \<open>literals_to_update_wl_literals_to_update_wl_empty S \<longleftrightarrow>
    literals_to_update_wl_heur S < isa_length_trail (get_trail_wl_heur S)\<close>


lemma literals_to_update_wl_literals_to_update_wl_empty_alt_def:
  \<open>literals_to_update_wl_literals_to_update_wl_empty =
    (\<lambda>(M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema, ccount,
       vdom, lcount). j < isa_length_trail M')\<close>
  unfolding literals_to_update_wl_literals_to_update_wl_empty_def isa_length_trail_def
  by (auto intro!: ext split: prod.splits)

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

lemma unit_propagation_outer_loop_wl_D_invI:
  \<open>unit_propagation_outer_loop_wl_D_heur_inv S\<^sub>0 S \<Longrightarrow>
    isa_length_trail_pre (get_trail_wl_heur S)\<close>
  unfolding unit_propagation_outer_loop_wl_D_heur_inv_def
  by blast

sepref_definition unit_propagation_outer_loop_wl_D_code
  is \<open>unit_propagation_outer_loop_wl_D_heur\<close>
  :: \<open>isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
  supply [[goals_limit=1]]
    unit_propagation_outer_loop_wl_D_invI[intro]
  unfolding unit_propagation_outer_loop_wl_D_heur_def
    literals_to_update_wl_literals_to_update_wl_empty_def[symmetric]
  by sepref

declare unit_propagation_outer_loop_wl_D_code.refine[sepref_fr_rules]

lemma unit_propagation_outer_loop_wl_D_heur_fast:
  \<open>length (get_clauses_wl_heur x) \<le> uint64_max \<Longrightarrow>
       unit_propagation_outer_loop_wl_D_heur_inv x s' \<Longrightarrow>
       length (get_clauses_wl_heur a1') =
       length (get_clauses_wl_heur s') \<Longrightarrow>
       (a, a2') \<in> unat_lit_rel \<Longrightarrow>
       length (get_clauses_wl_heur s') \<le> uint64_max\<close>
  by (auto simp: unit_propagation_outer_loop_wl_D_heur_inv_def)

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