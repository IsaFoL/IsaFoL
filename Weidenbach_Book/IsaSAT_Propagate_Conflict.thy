theory IsaSAT_Propagate_Conflict
  imports IsaSAT_Setup Watched_Literals_Heuristics
begin

subsubsection \<open>Refining Propagate And Conflict\<close>

paragraph \<open>Propagation, Inner Loop\<close>

(* TODO Move *)
definition (in -)length_aa_u64_o64 :: \<open>('a::heap array_list) array \<Rightarrow> uint64 \<Rightarrow> uint64 Heap\<close> where
  \<open>length_aa_u64_o64 xs i = length_aa_u64 xs i >>= (\<lambda>n. return (uint64_of_nat n))\<close>

definition arl_length_o64 where
  \<open>arl_length_o64 x = do {n \<leftarrow> arl_length x;  return (uint64_of_nat n)}\<close>
  
lemma length_aa_u64_o64_code[code]:
  \<open>length_aa_u64_o64 xs i = nth_u64_code xs i \<bind> arl_length_o64\<close>
  unfolding length_aa_u64_o64_def length_aa_u64_def nth_u_def[symmetric] nth_u64_code_def
   Array.nth'_def arl_length_o64_def length_aa_def
  by (auto simp: nat_of_uint32_code nat_of_uint64_code[symmetric])

lemma length_aa_u64_o64_hnr[sepref_fr_rules]:
   \<open>(uncurry length_aa_u64_o64, uncurry (RETURN \<circ>\<circ> length_ll)) \<in>
     [\<lambda>(xs, i). i < length xs \<and> length (xs ! i) \<le> uint64_max]\<^sub>a
    (arrayO_assn (arl_assn R))\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def length_aa_u64_o64_def br_def
     length_aa_u64_def uint64_nat_rel_def nat_of_uint64_uint64_of_nat_id
     length_ll_def)


definition (in -)length_aa_u32_o64 :: \<open>('a::heap array_list) array \<Rightarrow> uint32 \<Rightarrow> uint64 Heap\<close> where
  \<open>length_aa_u32_o64 xs i = length_aa_u xs i >>= (\<lambda>n. return (uint64_of_nat n))\<close>
  
lemma length_aa_u32_o64_code[code]:
  \<open>length_aa_u32_o64 xs i = nth_u_code xs i \<bind> arl_length_o64\<close>
  unfolding length_aa_u32_o64_def length_aa_u64_def nth_u_def[symmetric] nth_u_code_def
   Array.nth'_def arl_length_o64_def length_aa_u_def length_aa_def
  by (auto simp: nat_of_uint64_code[symmetric] nat_of_uint32_code[symmetric])

lemma length_aa_u32_o64_hnr[sepref_fr_rules]:
   \<open>(uncurry length_aa_u32_o64, uncurry (RETURN \<circ>\<circ> length_ll)) \<in>
     [\<lambda>(xs, i). i < length xs \<and> length (xs ! i) \<le> uint64_max]\<^sub>a
    (arrayO_assn (arl_assn R))\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint32_nat_rel_def length_aa_u32_o64_def br_def
     length_aa_u64_def uint64_nat_rel_def nat_of_uint64_uint64_of_nat_id
     length_ll_def length_aa_u_def)
(* End Move *)

context isasat_input_bounded
begin

lemma watched_by_app_watched_by_app_heur:
  \<open>(uncurry2 (RETURN ooo watched_by_app_heur), uncurry2 (RETURN ooo watched_by_app)) \<in>
    [\<lambda>((S, L), K). L \<in> snd ` D\<^sub>0 \<and> K < length (get_watched_wl S L)]\<^sub>f
     twl_st_heur \<times>\<^sub>f Id \<times>\<^sub>f Id \<rightarrow> \<langle>Id\<rangle> nres_rel\<close>
  by (intro frefI nres_relI)
     (auto simp: watched_by_app_heur_def watched_by_app_def twl_st_heur_def map_fun_rel_def)

sepref_thm watched_by_app_heur_code
  is \<open>uncurry2 (RETURN ooo watched_by_app_heur)\<close>
  :: \<open>[watched_by_app_heur_pre]\<^sub>a
        isasat_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> nat_assn\<close>
  supply [[goals_limit=1]] length_rll_def[simp]
  unfolding watched_by_app_heur_alt_def isasat_assn_def nth_rll_def[symmetric]
   watched_by_app_heur_pre_def
  by sepref

concrete_definition (in -) watched_by_app_heur_code
   uses isasat_input_bounded.watched_by_app_heur_code.refine_raw
   is \<open>(uncurry2 ?f, _) \<in> _\<close>

prepare_code_thms (in -) watched_by_app_heur_code_def

lemmas watched_by_app_heur_code_refine[sepref_fr_rules] =
   watched_by_app_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]

sepref_thm watched_by_app_heur_fast_code
  is \<open>uncurry2 (RETURN ooo watched_by_app_heur)\<close>
  :: \<open>[watched_by_app_heur_pre]\<^sub>a
        isasat_fast_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  supply [[goals_limit=1]] length_rll_def[simp]
  unfolding watched_by_app_heur_alt_def isasat_fast_assn_def nth_rll_def[symmetric]
   watched_by_app_heur_pre_def
  by sepref

concrete_definition (in -) watched_by_app_heur_fast_code
   uses isasat_input_bounded.watched_by_app_heur_fast_code.refine_raw
   is \<open>(uncurry2 ?f, _) \<in> _\<close>

prepare_code_thms (in -) watched_by_app_heur_fast_code_def

lemmas watched_by_app_heur_fast_code_refine[sepref_fr_rules] =
   watched_by_app_heur_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]


sepref_thm access_lit_in_clauses_heur_code
  is \<open>uncurry2 (RETURN ooo access_lit_in_clauses_heur)\<close>
  :: \<open>[access_lit_in_clauses_heur_pre]\<^sub>a
      isasat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k  *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  supply length_rll_def[simp] [[goals_limit=1]]
  unfolding isasat_assn_def access_lit_in_clauses_heur_alt_def
    fmap_rll_def[symmetric] access_lit_in_clauses_heur_pre_def
    fmap_rll_u64_def[symmetric]
  by sepref

concrete_definition (in -) access_lit_in_clauses_heur_code
   uses isasat_input_bounded.access_lit_in_clauses_heur_code.refine_raw
   is \<open>(uncurry2 ?f, _) \<in> _\<close>

prepare_code_thms (in -) access_lit_in_clauses_heur_code_def

lemmas access_lit_in_clauses_heur_code_refine[sepref_fr_rules] =
   access_lit_in_clauses_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]

sepref_thm access_lit_in_clauses_heur_fast_code
  is \<open>uncurry2 (RETURN ooo access_lit_in_clauses_heur)\<close>
  :: \<open>[access_lit_in_clauses_heur_pre]\<^sub>a
      isasat_fast_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k  *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  supply length_rll_def[simp] [[goals_limit=1]]
  unfolding isasat_fast_assn_def access_lit_in_clauses_heur_alt_def
    fmap_rll_def[symmetric] access_lit_in_clauses_heur_pre_def
    fmap_rll_u64_def[symmetric]
  by sepref

concrete_definition (in -) access_lit_in_clauses_heur_fast_code
   uses isasat_input_bounded.access_lit_in_clauses_heur_fast_code.refine_raw
   is \<open>(uncurry2 ?f, _) \<in> _\<close>

prepare_code_thms (in -) access_lit_in_clauses_heur_fast_code_def

lemmas access_lit_in_clauses_heur_fast_code_refine[sepref_fr_rules] =
   access_lit_in_clauses_heur_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]

end

lemma case_tri_bool_If:
  \<open>(case a of
       None \<Rightarrow> f1
     | Some v \<Rightarrow>
        (if v then f2 else f3)) =
   (let b = a in if b = UNSET
    then f1
    else if b = SET_TRUE then f2 else f3)\<close>
  by (auto split: option.splits)


definition two_uint64_nat where
  [simp]: \<open>two_uint64_nat = (2 :: nat)\<close>

lemma uint64_nat_assn_two_uint64_nat[sepref_fr_rules]:
  \<open>(uncurry0 (return 2), uncurry0 (RETURN two_uint64_nat)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint64_nat_rel_def br_def)

context isasat_input_bounded_nempty
begin

(* TODO most of the unfolding should move to the definition *)
sepref_thm find_unwatched_wl_st_heur_code
  is \<open>uncurry ((PR_CONST find_unwatched_wl_st_heur))\<close>
  :: \<open>[find_unwatched_wl_st_heur_pre]\<^sub>a
         isasat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> option_assn uint64_nat_assn\<close>
  supply [[goals_limit = 1]] literals_are_in_\<L>\<^sub>i\<^sub>n_heur_in_D\<^sub>0'[intro]
    fmap_length_rll_def[simp] fmap_length_rll_u64_def[simp]
  unfolding find_unwatched_wl_st_heur_def isasat_assn_def PR_CONST_def
  find_unwatched_def fmap_rll_def[symmetric] fmap_length_rll_u64_def[symmetric]
  length_u_def[symmetric]
  case_tri_bool_If find_unwatched_wl_st_heur_pre_def
  two_uint64_nat_def[symmetric]
  fmap_rll_u64_def[symmetric]
  one_uint64_nat_def[symmetric]
  by sepref

concrete_definition (in -) find_unwatched_wl_st_heur_code
   uses isasat_input_bounded_nempty.find_unwatched_wl_st_heur_code.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) find_unwatched_wl_st_heur_code_def

lemmas find_unwatched_wl_st_heur_code_find_unwatched_wl_st_heur[sepref_fr_rules] =
   find_unwatched_wl_st_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms,
     unfolded PR_CONST_def]

sepref_thm find_unwatched_wl_st_heur_fast_code
  is \<open>uncurry ((PR_CONST find_unwatched_wl_st_heur))\<close>
  :: \<open>[find_unwatched_wl_st_heur_pre]\<^sub>a
         isasat_fast_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> option_assn uint64_nat_assn\<close>
  supply [[goals_limit = 1]] literals_are_in_\<L>\<^sub>i\<^sub>n_heur_in_D\<^sub>0'[intro]
    fmap_length_rll_def[simp] fmap_length_rll_u64_def[simp]
  unfolding find_unwatched_wl_st_heur_def isasat_fast_assn_def PR_CONST_def
  find_unwatched_def fmap_rll_def[symmetric] fmap_length_rll_u64_def[symmetric]
  length_u_def[symmetric]
  case_tri_bool_If find_unwatched_wl_st_heur_pre_def
  two_uint64_nat_def[symmetric]
  fmap_rll_u64_def[symmetric]
  one_uint64_nat_def[symmetric]
  by sepref

concrete_definition (in -) find_unwatched_wl_st_heur_fast_code
   uses isasat_input_bounded_nempty.find_unwatched_wl_st_heur_fast_code.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) find_unwatched_wl_st_heur_fast_code_def

lemmas find_unwatched_wl_st_heur_code_find_unwatched_wl_st_fast_heur[sepref_fr_rules] =
   find_unwatched_wl_st_heur_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms,
     unfolded PR_CONST_def]

sepref_thm set_conflict_wl_heur_code
  is \<open>uncurry set_conflict_wl_heur\<close>
  :: \<open>[set_conflict_wl_heur_pre]\<^sub>a
    nat_assn\<^sup>k *\<^sub>a isasat_assn\<^sup>d \<rightarrow> isasat_assn\<close>
  supply [[goals_limit=1]]
  unfolding set_conflict_wl_heur_def isasat_assn_def IICF_List_Mset.lms_fold_custom_empty
    set_conflict_wl_heur_pre_def
  by sepref

concrete_definition (in -) set_conflict_wl_heur_code
  uses isasat_input_bounded_nempty.set_conflict_wl_heur_code.refine_raw
  is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) set_conflict_wl_heur_code_def

lemmas set_conflict_wl_heur_code[sepref_fr_rules] =
  set_conflict_wl_heur_code.refine[OF isasat_input_bounded_nempty_axioms]


sepref_thm set_conflict_wl_heur_fast_code
  is \<open>uncurry set_conflict_wl_heur\<close>
  :: \<open>[set_conflict_wl_heur_pre]\<^sub>a
    uint32_nat_assn\<^sup>k *\<^sub>a isasat_fast_assn\<^sup>d \<rightarrow> isasat_fast_assn\<close>
  supply [[goals_limit=1]]
  unfolding set_conflict_wl_heur_def isasat_fast_assn_def IICF_List_Mset.lms_fold_custom_empty
    set_conflict_wl_heur_pre_def
  by sepref

concrete_definition (in -) set_conflict_wl_heur_fast_code
  uses isasat_input_bounded_nempty.set_conflict_wl_heur_fast_code.refine_raw
  is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) set_conflict_wl_heur_fast_code_def

lemmas set_conflict_wl_heur_fast_code[sepref_fr_rules] =
  set_conflict_wl_heur_fast_code.refine[OF isasat_input_bounded_nempty_axioms]

sepref_thm update_clause_wl_code
  is \<open>uncurry5 update_clause_wl_heur\<close>
  :: \<open>[update_clause_wl_code_pre]\<^sub>a
     unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a isasat_assn\<^sup>d \<rightarrow>
       nat_assn *a isasat_assn\<close>
  supply [[goals_limit=1]] length_rll_def[simp] length_ll_def[simp]
  unfolding update_clause_wl_heur_def isasat_assn_def Array_List_Array.swap_ll_def[symmetric]
    fmap_rll_def[symmetric] delete_index_and_swap_update_def[symmetric]
    delete_index_and_swap_ll_def[symmetric] fmap_swap_ll_def[symmetric]
    append_ll_def[symmetric] update_clause_wl_code_pre_def
    fmap_rll_u64_def[symmetric]
    fmap_swap_ll_u64_def[symmetric]
  by sepref


concrete_definition (in -) update_clause_wl_code
  uses isasat_input_bounded_nempty.update_clause_wl_code.refine_raw
  is \<open>(uncurry5 ?f,_)\<in>_\<close>

prepare_code_thms (in -) update_clause_wl_code_def

lemmas update_clause_wl_code[sepref_fr_rules] =
  update_clause_wl_code.refine[OF isasat_input_bounded_nempty_axioms]

sepref_thm update_clause_wl_fast_code
  is \<open>uncurry5 update_clause_wl_heur\<close>
  :: \<open>[update_clause_wl_code_pre]\<^sub>a
     unat_lit_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a isasat_fast_assn\<^sup>d \<rightarrow>
       uint64_nat_assn *a isasat_fast_assn\<close>
  supply [[goals_limit=1]] length_rll_def[simp] length_ll_def[simp]
  unfolding update_clause_wl_heur_def isasat_fast_assn_def Array_List_Array.swap_ll_def[symmetric]
    fmap_rll_def[symmetric] delete_index_and_swap_update_def[symmetric]
    delete_index_and_swap_ll_def[symmetric] fmap_swap_ll_def[symmetric]
    append_ll_def[symmetric] update_clause_wl_code_pre_def
    fmap_rll_u64_def[symmetric]
    fmap_swap_ll_u64_def[symmetric]
  by sepref


concrete_definition (in -) update_clause_wl_fast_code
  uses isasat_input_bounded_nempty.update_clause_wl_fast_code.refine_raw
  is \<open>(uncurry5 ?f,_)\<in>_\<close>

prepare_code_thms (in -) update_clause_wl_fast_code_def

lemmas update_clause_wl_fast_code[sepref_fr_rules] =
  update_clause_wl_fast_code.refine[OF isasat_input_bounded_nempty_axioms]

sepref_thm propagate_lit_wl_code
  is \<open>uncurry3 (RETURN oooo (PR_CONST propagate_lit_wl_heur))\<close>
  :: \<open>[propagate_lit_wl_heur_pre]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a isasat_assn\<^sup>d \<rightarrow> isasat_assn\<close>
  unfolding PR_CONST_def propagate_lit_wl_heur_def isasat_assn_def
    cons_trail_Propagated_def[symmetric]
  supply [[goals_limit=1]]length_rll_def[simp] length_ll_def[simp]
  unfolding update_clause_wl_heur_def isasat_assn_def
    propagate_lit_wl_heur_pre_def fmap_swap_ll_def[symmetric]
    fmap_swap_ll_u64_def[symmetric]
    zero_uint64_nat_def[symmetric]
    one_uint64_nat_def[symmetric]
  by sepref


concrete_definition (in -) propagate_lit_wl_code
  uses isasat_input_bounded_nempty.propagate_lit_wl_code.refine_raw
  is \<open>(uncurry3 ?f, _) \<in> _\<close>

prepare_code_thms (in -) propagate_lit_wl_code_def

lemmas propagate_lit_wl_code[sepref_fr_rules] =
  propagate_lit_wl_code.refine[OF isasat_input_bounded_nempty_axioms, unfolded PR_CONST_def]

sepref_thm propagate_lit_wl_fast_code
  is \<open>uncurry3 (RETURN oooo (PR_CONST propagate_lit_wl_heur))\<close>
  :: \<open>[\<lambda>(((L', C), w), S). propagate_lit_wl_heur_pre (((L', C), w), S) \<and> 
        w + 1 \<le> uint64_max]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a isasat_fast_assn\<^sup>d \<rightarrow> isasat_fast_assn\<close>
  unfolding PR_CONST_def propagate_lit_wl_heur_def isasat_assn_def
    cons_trail_Propagated_def[symmetric]
  supply [[goals_limit=1]]length_rll_def[simp] length_ll_def[simp]
  unfolding update_clause_wl_heur_def isasat_fast_assn_def
    propagate_lit_wl_heur_pre_def fmap_swap_ll_def[symmetric]
    fmap_swap_ll_u64_def[symmetric]
    zero_uint64_nat_def[symmetric]
    one_uint64_nat_def[symmetric]
  by sepref


concrete_definition (in -) propagate_lit_wl_fast_code
  uses isasat_input_bounded_nempty.propagate_lit_wl_fast_code.refine_raw
  is \<open>(uncurry3 ?f, _) \<in> _\<close>

prepare_code_thms (in -) propagate_lit_wl_fast_code_def

lemmas propagate_lit_wl_fast_code[sepref_fr_rules] =
  propagate_lit_wl_fast_code.refine[OF isasat_input_bounded_nempty_axioms, unfolded PR_CONST_def]

end

text \<open>Find a less hack-like solution\<close>
setup \<open>map_theory_claset (fn ctxt => ctxt delSWrapper "split_all_tac")\<close>

context isasat_input_bounded_nempty
begin

context
begin

sepref_register find_unwatched_wl_st_heur
sepref_thm unit_propagation_inner_loop_body_wl_heur
  is \<open>uncurry2 (PR_CONST unit_propagation_inner_loop_body_wl_heur)\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a isasat_assn\<^sup>d \<rightarrow>\<^sub>a nat_assn *a isasat_assn\<close>
  supply
    if_splits[split]
    length_rll_def[simp]
    watched_by_app_heur_code_refine[sepref_fr_rules]
  supply undefined_lit_polarity_st_iff[iff]
    unit_prop_body_wl_D_find_unwatched_heur_inv_def[simp]
  unfolding unit_propagation_inner_loop_body_wl_heur_def length_rll_def[symmetric] PR_CONST_def
  unfolding fmap_rll_def[symmetric]
  unfolding fast_minus_def[symmetric]
    SET_FALSE_def[symmetric] SET_TRUE_def[symmetric]
  apply (rewrite in \<open>let _ = \<hole> in _\<close> zero_uint64_nat_def[symmetric])+
  apply (rewrite in \<open>let _ = \<hole> in _\<close> one_uint64_nat_def[symmetric])+
  by sepref

find_theorems "op +" uint64_max " _ < uint64_max"
thm uint64_nat_assn_plus
sepref_thm unit_propagation_inner_loop_body_wl_fast_heur
  is \<open>uncurry2 (PR_CONST unit_propagation_inner_loop_body_wl_heur)\<close>
  :: \<open>[\<lambda>((L, w), S). w+1 \<le> uint64_max]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a isasat_fast_assn\<^sup>d \<rightarrow> 
      uint64_nat_assn *a isasat_fast_assn\<close>
  supply
    if_splits[split]
    length_rll_def[simp]
    watched_by_app_heur_code_refine[sepref_fr_rules]
  supply undefined_lit_polarity_st_iff[iff]
    unit_prop_body_wl_D_find_unwatched_heur_inv_def[simp] uint64_max_def[simp]
  unfolding unit_propagation_inner_loop_body_wl_heur_def length_rll_def[symmetric] PR_CONST_def
  unfolding fmap_rll_def[symmetric]
  unfolding fast_minus_def[symmetric]
    SET_FALSE_def[symmetric] SET_TRUE_def[symmetric]
  apply (rewrite in \<open>let _ = \<hole> in _\<close> zero_uint64_nat_def[symmetric])+
  apply (rewrite in \<open>let _ = \<hole> in _\<close> one_uint64_nat_def[symmetric])+
  apply (rewrite in \<open>RETURN (_ + _, _)\<close> one_uint64_nat_def[symmetric])+
  by sepref

end


sepref_register unit_propagation_inner_loop_body_wl_D

concrete_definition (in -) unit_propagation_inner_loop_body_wl_heur_code
   uses isasat_input_bounded_nempty.unit_propagation_inner_loop_body_wl_heur.refine_raw
   is \<open>(uncurry2 ?f, _) \<in> _\<close>

prepare_code_thms (in -) unit_propagation_inner_loop_body_wl_heur_code_def

lemmas unit_propagation_inner_loop_body_wl_D_code_refine[sepref_fr_rules] =
   unit_propagation_inner_loop_body_wl_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

concrete_definition (in -) unit_propagation_inner_loop_body_wl_heur_fast_code
   uses isasat_input_bounded_nempty.unit_propagation_inner_loop_body_wl_fast_heur.refine_raw
   is \<open>(uncurry2 ?f, _) \<in> _\<close>

prepare_code_thms (in -) unit_propagation_inner_loop_body_wl_heur_fast_code_def

lemmas unit_propagation_inner_loop_body_wl_D_fast_code_refine[sepref_fr_rules] =
   unit_propagation_inner_loop_body_wl_heur_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]


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

sepref_thm length_ll_fs_heur_code
  is \<open>uncurry (RETURN oo length_ll_fs_heur)\<close>
  :: \<open>[\<lambda>(S, L). nat_of_lit L < length (get_watched_wl_heur S)]\<^sub>a
      isasat_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> nat_assn\<close>
  unfolding length_ll_fs_heur_alt_def get_watched_wl_heur_def isasat_assn_def
    length_ll_def[symmetric]
  supply [[goals_limit=1]]
  by sepref

concrete_definition (in -) length_ll_fs_heur_code
   uses isasat_input_bounded_nempty.length_ll_fs_heur_code.refine_raw
   is \<open>(uncurry ?f, _) \<in> _\<close>

prepare_code_thms (in -) length_ll_fs_heur_code_def

lemmas length_ll_fs_heur_code_refine[sepref_fr_rules] =
   length_ll_fs_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

term length_aa_u32
sepref_thm length_ll_fs_heur_fast_code
  is \<open>uncurry (RETURN oo length_ll_fs_heur)\<close>
  :: \<open>[\<lambda>(S, L). nat_of_lit L < length (get_watched_wl_heur S) \<and>
         length (get_watched_wl_heur S ! (nat_of_lit L)) \<le> uint64_max]\<^sub>a
      isasat_fast_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  unfolding length_ll_fs_heur_alt_def get_watched_wl_heur_def isasat_fast_assn_def
    length_ll_def[symmetric]
  supply [[goals_limit=1]] length_ll_def[simp]
  by sepref

concrete_definition (in -) length_ll_fs_heur_fast_code
   uses isasat_input_bounded_nempty.length_ll_fs_heur_fast_code.refine_raw
   is \<open>(uncurry ?f, _) \<in> _\<close>

prepare_code_thms (in -) length_ll_fs_heur_fast_code_def

lemmas length_ll_fs_heur_fast_code_refine[sepref_fr_rules] =
   length_ll_fs_heur_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

sepref_register unit_propagation_inner_loop_body_wl_heur

thm length_ll_fs_heur_def[symmetric]
lemma unit_propagation_inner_loop_wl_loop_D_heur_cond:
  \<open>unit_propagation_inner_loop_wl_loop_D_heur_inv S a s' \<Longrightarrow>  s' = (a1', a2') \<Longrightarrow>
       nat_of_lit a < length (get_watched_wl_heur a2')\<close>
  by (auto simp: unit_propagation_inner_loop_wl_loop_D_heur_inv_def
      twl_st_heur_def map_fun_rel_def)

sepref_thm unit_propagation_inner_loop_wl_loop_D
  is \<open>uncurry ((PR_CONST unit_propagation_inner_loop_wl_loop_D_heur))\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a isasat_assn\<^sup>d \<rightarrow>\<^sub>a nat_assn *a isasat_assn\<close>
  unfolding unit_propagation_inner_loop_wl_loop_D_heur_def PR_CONST_def
  unfolding watched_by_nth_watched_app watched_app_def[symmetric]
    length_ll_fs_heur_def[symmetric]
  unfolding nth_ll_def[symmetric]
  unfolding swap_ll_def[symmetric]
  unfolding delete_index_and_swap_update_def[symmetric] append_update_def[symmetric]
    is_None_def[symmetric] get_conflict_wl_is_None_heur_alt_def[symmetric]
    length_ll_fs_def[symmetric]
  supply [[goals_limit=1]] unit_propagation_inner_loop_wl_loop_D_heur_cond[simp]
  by sepref

concrete_definition (in -) unit_propagation_inner_loop_wl_loop_D_code
   uses isasat_input_bounded_nempty.unit_propagation_inner_loop_wl_loop_D.refine_raw
   is \<open>(uncurry ?f, _) \<in> _\<close>

prepare_code_thms (in -) unit_propagation_inner_loop_wl_loop_D_code_def

lemmas unit_propagation_inner_loop_wl_loop_D_code_refine[sepref_fr_rules] =
   unit_propagation_inner_loop_wl_loop_D_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

lemma (in isasat_input_ops) unit_propagation_inner_loop_wl_loop_D_heur_alt_def:
  \<open>unit_propagation_inner_loop_wl_loop_D_heur L S\<^sub>0 = do {
    let b = (zero_uint64_nat, S\<^sub>0);
    WHILE\<^sub>T\<^bsup>unit_propagation_inner_loop_wl_loop_D_heur_inv S\<^sub>0 L\<^esup>
      (\<lambda>(w, S). w < length (watched_by_int S L) \<and> get_conflict_wl_is_None_heur S)
      (\<lambda>(w, S). do {
        unit_propagation_inner_loop_body_wl_heur L w S
      })
      b
  }\<close>
  unfolding unit_propagation_inner_loop_wl_loop_D_heur_def Let_def zero_uint64_nat_def ..

lemma (in -) size_dom_m_Max_dom:
  \<open>size (dom_m N) \<le> Suc (Max_dom N)\<close>
proof -
  have \<open>dom_m N \<subseteq># mset_set {0..< Suc (Max_dom N)}\<close>
    apply (rule distinct_finite_set_mset_subseteq_iff[THEN iffD1])
    subgoal by (auto simp: distinct_mset_dom)
    subgoal by auto
    subgoal by (auto dest: Max_dom_le)
    done
  from size_mset_mono[OF this] show ?thesis by auto
qed

(* This bound absolutely not thight *)
lemma unit_propagation_inner_loop_wl_loop_D_heur_inv_length_watchlist:
  assumes \<open>unit_propagation_inner_loop_wl_loop_D_heur_inv S0 L (w, S)\<close> and
    fast: \<open>isasat_fast S0\<close>
  shows 
    \<open>length (get_watched_wl_heur S ! nat_of_lit L) \<le> uint64_max\<close> (is ?A) and
    \<open>length (get_watched_wl_heur S ! nat_of_lit L) < uint64_max\<close> (is ?B) and
    \<open>Suc w \<le> uint64_max\<close> (is ?C)
proof -
  obtain T where
    ST: \<open>(S, T) \<in> twl_st_heur\<close> and
    inner: \<open>unit_propagation_inner_loop_wl_loop_D_inv L (w, T)\<close> and
    L: \<open>L \<in> snd ` D\<^sub>0\<close> and
    dom_eq: \<open>dom_m (get_clauses_wl_heur S) = dom_m (get_clauses_wl_heur S0)\<close>
    using assms unfolding unit_propagation_inner_loop_wl_loop_D_heur_inv_def by blast
  obtain U V where 
    corr_w: \<open>correct_watching T\<close> and
    lits_in: \<open>literals_are_\<L>\<^sub>i\<^sub>n T\<close> and
    TU: \<open>(T, U) \<in> state_wl_l (Some (L, w))\<close> and
    UV: \<open>(U, V) \<in> twl_st_l (Some L)\<close> and
    struct_invs: \<open>twl_struct_invs V\<close> and
    \<open>twl_stgy_invs V\<close> and
    \<open>twl_list_invs U\<close> and
    w_le: \<open>w \<le> length (watched_by T L)\<close>
    using inner unfolding unit_propagation_inner_loop_wl_loop_D_inv_def
     unit_propagation_inner_loop_wl_loop_inv_def
     unit_propagation_inner_loop_l_inv_def 
     by fast+
  have alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of V)\<close>
    using struct_invs unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast
  have \<open>L \<in># all_lits_of_mm (mset `# ran_mf (get_clauses_wl T) + get_unit_clauses_wl T)\<close>
    using lits_in L by (auto simp: image_image is_\<L>\<^sub>a\<^sub>l\<^sub>l_def)
  moreover have \<open>set_mset (all_lits_of_mm (mset `# ran_mf (get_clauses_wl T) + get_unit_clauses_wl T)) =
      set_mset (all_lits_of_mm (mset `# ran_mf (get_clauses_wl T) + get_unit_init_clss_wl T))\<close>
    apply (subst all_clss_lf_ran_m[symmetric])+
    apply (subst image_mset_union)+
    using TU UV alien
    by (cases T; cases U; cases V)
      (auto simp: in_all_lits_of_mm_ain_atms_of_iff state_wl_l_def twl_st_l_def
      cdcl\<^sub>W_restart_mset.no_strange_atm_def mset_take_mset_drop_mset')
  ultimately have 1: \<open>mset ((get_watched_wl T) L) = {#C \<in># dom_m (get_clauses_wl T). L \<in> set (watched_l ((get_clauses_wl T) \<propto> C))#}\<close>
    using corr_w by (cases T)
      (auto simp: correct_watching.simps clause_to_update_def all_lits_of_mm_union)
  then have \<open>size (mset ((get_watched_wl T) L)) \<le> size (dom_m (get_clauses_wl T))\<close>
    unfolding 1
    by (cases T) (auto simp: correct_watching.simps clause_to_update_def)
  moreover {
    have \<open>Max_dom (get_clauses_wl T) \<le> uint_max\<close>
      using fast ST
      unfolding dom_eq[symmetric]
      by (cases T)
        (auto simp: twl_st_heur_def Max_dom_def dest!: multi_member_split)
    then have \<open>size (dom_m (get_clauses_wl T)) < uint64_max\<close>
      using fast ST size_dom_m_Max_dom[of \<open>get_clauses_wl T\<close>]
      by (cases T)
        (auto simp: twl_st_heur_def uint_max_def uint64_max_def)
  }
  ultimately have le_T: \<open>length ((get_watched_wl T) L) < uint64_max\<close>
    by simp
  moreover have \<open>length ((get_watched_wl T) L)  = length (get_watched_wl_heur S ! nat_of_lit L)\<close>
    using L ST by (cases S; cases T) (auto simp: twl_st_heur_def map_fun_rel_def)
  ultimately show ?A and ?B by simp_all
  then show ?C
    using w_le le_T by (cases T) auto
qed

sepref_thm unit_propagation_inner_loop_wl_loop_D_fast
  is \<open>uncurry ((PR_CONST unit_propagation_inner_loop_wl_loop_D_heur))\<close>
  :: \<open>[\<lambda>(L, S). isasat_fast S]\<^sub>a
       unat_lit_assn\<^sup>k *\<^sub>a isasat_fast_assn\<^sup>d \<rightarrow> uint64_nat_assn *a isasat_fast_assn\<close>
  supply unit_propagation_inner_loop_wl_loop_D_heur_inv_length_watchlist[intro]
  unfolding unit_propagation_inner_loop_wl_loop_D_heur_alt_def PR_CONST_def
  unfolding watched_by_nth_watched_app watched_app_def[symmetric]
    length_ll_fs_heur_def[symmetric]
  unfolding nth_ll_def[symmetric]
  unfolding swap_ll_def[symmetric]
  unfolding delete_index_and_swap_update_def[symmetric] append_update_def[symmetric]
    is_None_def[symmetric] get_conflict_wl_is_None_heur_alt_def[symmetric]
    length_ll_fs_def[symmetric]
  supply [[goals_limit=1]] unit_propagation_inner_loop_wl_loop_D_heur_cond[simp]
  supply unit_propagation_inner_loop_body_wl_D_fast_code_refine[sepref_fr_rules]
  by sepref

concrete_definition (in -) unit_propagation_inner_loop_wl_loop_D_fast_code
   uses isasat_input_bounded_nempty.unit_propagation_inner_loop_wl_loop_D_fast.refine_raw
   is \<open>(uncurry ?f, _) \<in> _\<close>

prepare_code_thms (in -) unit_propagation_inner_loop_wl_loop_D_fast_code_def

lemmas unit_propagation_inner_loop_wl_loop_D_fast_code_refine[sepref_fr_rules] =
   unit_propagation_inner_loop_wl_loop_D_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

sepref_register unit_propagation_inner_loop_wl_loop_D_heur
sepref_thm unit_propagation_inner_loop_wl_D
  is \<open>uncurry (PR_CONST unit_propagation_inner_loop_wl_D_heur)\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a isasat_assn\<^sup>d \<rightarrow>\<^sub>a isasat_assn\<close>
  supply [[goals_limit=1]]
  unfolding PR_CONST_def unit_propagation_inner_loop_wl_D_heur_def
  by sepref

concrete_definition (in -) unit_propagation_inner_loop_wl_D_code
   uses isasat_input_bounded_nempty.unit_propagation_inner_loop_wl_D.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) unit_propagation_inner_loop_wl_D_code_def

lemmas unit_propagation_inner_loop_wl_D_code_refine[sepref_fr_rules] =
   unit_propagation_inner_loop_wl_D_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

sepref_thm unit_propagation_inner_loop_wl_D_fast
  is \<open>uncurry (PR_CONST unit_propagation_inner_loop_wl_D_heur)\<close>
  :: \<open>[\<lambda>(L, S). isasat_fast S]\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a isasat_fast_assn\<^sup>d \<rightarrow> isasat_fast_assn\<close>
  supply [[goals_limit=1]]
  unfolding PR_CONST_def unit_propagation_inner_loop_wl_D_heur_def
  by sepref

concrete_definition (in -) unit_propagation_inner_loop_wl_D_fast_code
   uses isasat_input_bounded_nempty.unit_propagation_inner_loop_wl_D_fast.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) unit_propagation_inner_loop_wl_D_fast_code_def

lemmas unit_propagation_inner_loop_wl_D_fast_code_refine[sepref_fr_rules] =
   unit_propagation_inner_loop_wl_D_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]


paragraph \<open>Unit propagation, Outer Loop\<close>

definition (in -) select_and_remove_from_literals_to_update_wl_heur'
  :: \<open>twl_st_wl_heur_W_list \<Rightarrow> twl_st_wl_heur_W_list \<times> _\<close> where
  \<open>select_and_remove_from_literals_to_update_wl_heur' =
     (\<lambda>(M, N, D, Q, W, other).  ((M, N, D, tl Q, W, other), hd Q))\<close>

definition get_literals_to_update_wl where
   \<open>get_literals_to_update_wl = (\<lambda>(M, N, U, D, NE, UE, Q, W). Q)\<close>

definition get_literals_to_update_wl_heur_W_list where
   \<open>get_literals_to_update_wl_heur_W_list = (\<lambda>(M, N, D, Q, W, _). Q)\<close>

definition literals_to_update_wl_empty_heur' :: \<open>twl_st_wl_heur_W_list \<Rightarrow> bool\<close>  where
  \<open>literals_to_update_wl_empty_heur' = (\<lambda>(M, N, D, Q, W, oth). Q = [])\<close>

definition (in isasat_input_ops) twl_st_wl_heur_W_list_rel
  :: \<open>(twl_st_wl_heur_W_list \<times> twl_st_wl_heur) set\<close>
where
  \<open>twl_st_wl_heur_W_list_rel =
     (Id :: ((nat,nat) ann_lits \<times> _) set) \<times>\<^sub>r
     (Id :: (nat clauses_l  \<times> _) set) \<times>\<^sub>r
     (Id :: (nat cconflict \<times> _)set) \<times>\<^sub>r
     (list_mset_rel :: (nat literal list \<times> nat lit_queue_wl) set)  \<times>\<^sub>r
     (Id :: (nat list list \<times> _)set) \<times>\<^sub>r
     Id \<times>\<^sub>r
     Id \<times>\<^sub>r
     nat_rel \<times>\<^sub>r
     Id \<times>\<^sub>r
     Id \<times>\<^sub>r
     Id \<times>\<^sub>r
     Id\<close>

definition (in isasat_input_ops) twl_st_heur_W_list_assn
  :: \<open>twl_st_wl_heur_W_list \<Rightarrow> twl_st_wll_trail \<Rightarrow> assn\<close>
where
\<open>twl_st_heur_W_list_assn =
  (trail_assn *a clauses_ll_assn *a
  option_lookup_clause_assn *a
  (list_assn unat_lit_assn) *a
  arrayO_assn (arl_assn nat_assn) *a
  vmtf_remove_conc *a phase_saver_conc *a uint32_nat_assn *a cach_refinement_assn *a
  lbd_assn *a out_learned_assn *a stats_assn
  )\<close>

lemma (in isasat_input_ops) isasat_assn_W_list:
  \<open>isasat_assn = hr_comp twl_st_heur_W_list_assn twl_st_wl_heur_W_list_rel\<close>
  unfolding isasat_assn_def twl_st_heur_W_list_assn_def twl_st_wl_heur_W_list_rel_def
  by (auto simp: list_assn_list_mset_rel_eq_list_mset_assn)


definition (in isasat_input_ops) twl_st_heur_W_list_fast_assn
  :: \<open>_ \<Rightarrow> twl_st_wll_trail_fast \<Rightarrow> assn\<close>
where
\<open>twl_st_heur_W_list_fast_assn =
  (trail_fast_assn *a clauses_ll_assn *a
  option_lookup_clause_assn *a
  (list_assn unat_lit_assn) *a
  arrayO_assn (arl_assn uint32_nat_assn) *a
  vmtf_remove_conc *a phase_saver_conc *a uint32_nat_assn *a cach_refinement_assn *a
  lbd_assn *a out_learned_assn *a stats_assn
  )\<close>

lemma (in isasat_input_ops) isasat_fast_assn_W_list:
  \<open>isasat_fast_assn = hr_comp twl_st_heur_W_list_fast_assn twl_st_wl_heur_W_list_rel\<close>
  unfolding isasat_fast_assn_def twl_st_heur_W_list_fast_assn_def twl_st_wl_heur_W_list_rel_def
  by (auto simp: list_assn_list_mset_rel_eq_list_mset_assn)

sepref_thm select_and_remove_from_literals_to_update_wl_code
  is \<open>RETURN o select_and_remove_from_literals_to_update_wl_heur'\<close>
  :: \<open>[\<lambda>S. \<not>literals_to_update_wl_empty_heur' S]\<^sub>a
      twl_st_heur_W_list_assn\<^sup>d \<rightarrow> twl_st_heur_W_list_assn *a unat_lit_assn\<close>
  supply [[goals_limit=1]]
  unfolding select_and_remove_from_literals_to_update_wl_heur'_def twl_st_heur_W_list_assn_def
    literals_to_update_wl_empty_heur'_def
  supply [[goals_limit = 1]]
  by sepref


concrete_definition (in -) select_and_remove_from_literals_to_update_wl_code
   uses isasat_input_bounded_nempty.select_and_remove_from_literals_to_update_wl_code.refine_raw
   is \<open>(?f, _)\<in>_\<close>

prepare_code_thms (in -) select_and_remove_from_literals_to_update_wl_code_def

lemmas select_and_remove_from_literals_to_update_wl_code_refine[sepref_fr_rules] =
   select_and_remove_from_literals_to_update_wl_code.refine[of \<A>\<^sub>i\<^sub>n,
     OF isasat_input_bounded_nempty_axioms]


sepref_thm select_and_remove_from_literals_to_update_wl_fast_code
  is \<open>RETURN o select_and_remove_from_literals_to_update_wl_heur'\<close>
  :: \<open>[\<lambda>S. \<not>literals_to_update_wl_empty_heur' S]\<^sub>a
      twl_st_heur_W_list_fast_assn\<^sup>d \<rightarrow> twl_st_heur_W_list_fast_assn *a unat_lit_assn\<close>
  supply [[goals_limit=1]]
  unfolding select_and_remove_from_literals_to_update_wl_heur'_def twl_st_heur_W_list_fast_assn_def
    literals_to_update_wl_empty_heur'_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) select_and_remove_from_literals_to_update_wl_fast_code
   uses isasat_input_bounded_nempty.select_and_remove_from_literals_to_update_wl_fast_code.refine_raw
   is \<open>(?f, _)\<in>_\<close>

prepare_code_thms (in -) select_and_remove_from_literals_to_update_wl_fast_code_def

lemmas select_and_remove_from_literals_to_update_wl_fast_code_refine[sepref_fr_rules] =
   select_and_remove_from_literals_to_update_wl_fast_code.refine[of \<A>\<^sub>i\<^sub>n,
     OF isasat_input_bounded_nempty_axioms]

definition literals_to_update_wl_empty_heur :: \<open>twl_st_wl_heur \<Rightarrow> bool\<close>  where
  \<open>literals_to_update_wl_empty_heur S \<longleftrightarrow> literals_to_update_wl_heur S = {#}\<close>

lemma
  select_and_remove_from_literals_to_update_wl_heur_select_and_remove_from_literals_to_update_wl:
  \<open>(RETURN o select_and_remove_from_literals_to_update_wl_heur',
    select_and_remove_from_literals_to_update_wl_heur) \<in>
    [\<lambda>S. \<not>literals_to_update_wl_empty_heur S]\<^sub>f
      (twl_st_wl_heur_W_list_rel) \<rightarrow>
       \<langle>(twl_st_wl_heur_W_list_rel) \<times>\<^sub>r Id\<rangle>nres_rel\<close>
  unfolding select_and_remove_from_literals_to_update_wl_heur_def
    get_literals_to_update_wl_heur_W_list_def
    get_literals_to_update_wl_def
    literals_to_update_wl_empty_heur_def literals_to_update_wl_empty_heur_def
    select_and_remove_from_literals_to_update_wl_heur'_def literals_to_update_wl_empty_heur_def
  apply (intro frefI nres_relI)
  apply (rename_tac x y, case_tac x, case_tac y,
      case_tac \<open>literals_to_update_wl_empty_heur y\<close>)
  unfolding get_literals_to_update_wl_def get_literals_to_update_wl_heur_W_list_def
  by (auto intro!: RETURN_SPEC_refine simp: nempty_list_mset_rel_iff
      twl_st_wl_heur_W_list_rel_def
      literals_to_update_wl_empty_heur_def)

theorem
  select_and_remove_from_literals_to_update_wl_code_select_and_remove_from_literals_to_update_wl
  [sepref_fr_rules]:
  \<open>(select_and_remove_from_literals_to_update_wl_code,
     select_and_remove_from_literals_to_update_wl_heur)
    \<in> [\<lambda>S. \<not> literals_to_update_wl_empty_heur S]\<^sub>a isasat_assn\<^sup>d \<rightarrow> isasat_assn *a
          unat_lit_assn\<close>
    (is ?slow is \<open>?fun \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>) and
  select_and_remove_from_literals_to_update_wl_fast_code_select_and_remove_from_literals_to_update_wl
  [sepref_fr_rules]:
  \<open>(select_and_remove_from_literals_to_update_wl_fast_code,
     select_and_remove_from_literals_to_update_wl_heur)
    \<in> [\<lambda>S. \<not> literals_to_update_wl_empty_heur S]\<^sub>a isasat_fast_assn\<^sup>d \<rightarrow> isasat_fast_assn *a
          unat_lit_assn\<close>
    (is ?fast is \<open>?cfast \<in> [?pre]\<^sub>a ?imfast \<rightarrow> ?ffast\<close>)
proof -
  have H: \<open>?fun
    \<in> [comp_PRE twl_st_wl_heur_W_list_rel (\<lambda>S. \<not> literals_to_update_wl_empty_heur S)
     (\<lambda>_ S. \<not> literals_to_update_wl_empty_heur' S)
     (\<lambda>_. True)]\<^sub>a hrp_comp (twl_st_heur_W_list_assn\<^sup>d)
                    twl_st_wl_heur_W_list_rel \<rightarrow> hr_comp (twl_st_heur_W_list_assn *a unat_lit_assn)
                                                  (twl_st_wl_heur_W_list_rel \<times>\<^sub>f nat_lit_lit_rel)\<close>
     (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF select_and_remove_from_literals_to_update_wl_code_refine
     select_and_remove_from_literals_to_update_wl_heur_select_and_remove_from_literals_to_update_wl]
    .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    apply (cases x)
    using that unfolding comp_PRE_def twl_st_heur_def literals_to_update_wl_empty_heur_def
      literals_to_update_wl_empty_def twl_st_wl_heur_W_list_rel_def literals_to_update_wl_empty_heur'_def
    by (auto simp: image_image map_fun_rel_def Nil_list_mset_rel_iff)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    isasat_assn_W_list[symmetric]
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    isasat_assn_W_list[symmetric] hr_comp_prod_conv
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?slow
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
  have H: \<open>?cfast
    \<in> [comp_PRE twl_st_wl_heur_W_list_rel (\<lambda>S. \<not> literals_to_update_wl_empty_heur S)
     (\<lambda>_ S. \<not> literals_to_update_wl_empty_heur' S)
     (\<lambda>_. True)]\<^sub>a hrp_comp (twl_st_heur_W_list_fast_assn\<^sup>d)
                    twl_st_wl_heur_W_list_rel \<rightarrow>
     hr_comp (twl_st_heur_W_list_fast_assn *a unat_lit_assn)
                                                  (twl_st_wl_heur_W_list_rel \<times>\<^sub>f nat_lit_lit_rel)\<close>
     (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF select_and_remove_from_literals_to_update_wl_fast_code_refine
     select_and_remove_from_literals_to_update_wl_heur_select_and_remove_from_literals_to_update_wl]
    .
  have im: \<open>?im' = ?imfast\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    isasat_fast_assn_W_list[symmetric]
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?ffast\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    isasat_fast_assn_W_list[symmetric] hr_comp_prod_conv
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?fast
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed

sepref_thm literals_to_update_wl_empty_heur_code
  is \<open>RETURN o literals_to_update_wl_empty_heur'\<close>
  :: \<open>twl_st_heur_W_list_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  supply [[goals_limit=1]]
  unfolding select_and_remove_from_literals_to_update_wl_heur'_def twl_st_heur_W_list_assn_def
    literals_to_update_wl_empty_heur'_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) literals_to_update_wl_empty_heur_code
   uses isasat_input_bounded_nempty.literals_to_update_wl_empty_heur_code.refine_raw
   is \<open>(?f, _)\<in>_\<close>

prepare_code_thms (in -) literals_to_update_wl_empty_heur_code_def

lemmas literals_to_update_wl_empty_heur_code_refine[sepref_fr_rules] =
   literals_to_update_wl_empty_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]


sepref_thm literals_to_update_wl_empty_heur_fast_code
  is \<open>RETURN o literals_to_update_wl_empty_heur'\<close>
  :: \<open>twl_st_heur_W_list_fast_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  supply [[goals_limit=1]]
  unfolding select_and_remove_from_literals_to_update_wl_heur'_def twl_st_heur_W_list_fast_assn_def
    literals_to_update_wl_empty_heur'_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) literals_to_update_wl_empty_heur_fast_code
   uses isasat_input_bounded_nempty.literals_to_update_wl_empty_heur_fast_code.refine_raw
   is \<open>(?f, _)\<in>_\<close>

prepare_code_thms (in -) literals_to_update_wl_empty_heur_fast_code_def

lemmas literals_to_update_wl_empty_heur_fast_code_refine[sepref_fr_rules] =
   literals_to_update_wl_empty_heur_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

lemma literals_to_update_wl_empty_heur_literals_to_update_wl_empty:
  \<open>(RETURN o literals_to_update_wl_empty_heur', RETURN o literals_to_update_wl_empty_heur) \<in>
    twl_st_wl_heur_W_list_rel \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  unfolding literals_to_update_wl_empty_heur_def literals_to_update_wl_empty_heur_def
    literals_to_update_wl_empty_heur'_def
  apply (intro frefI nres_relI)
  apply (rename_tac x y, case_tac x, case_tac y)
  by (auto simp: Nil_list_mset_rel_iff empty_list_mset_rel_iff
      twl_st_wl_heur_W_list_rel_def)

lemma literals_to_update_wl_empty_heur_code_literals_to_update_wl_empty[sepref_fr_rules]:
  \<open>(literals_to_update_wl_empty_heur_code, RETURN \<circ> literals_to_update_wl_empty_heur)
     \<in> isasat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  using literals_to_update_wl_empty_heur_code_refine[FCOMP
      literals_to_update_wl_empty_heur_literals_to_update_wl_empty]
  unfolding isasat_assn_W_list[symmetric]
  .


lemma literals_to_update_wl_empty_heur_fast_code_literals_to_update_wl_empty[sepref_fr_rules]:
  \<open>(literals_to_update_wl_empty_heur_fast_code, RETURN \<circ> literals_to_update_wl_empty_heur)
     \<in> isasat_fast_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  using literals_to_update_wl_empty_heur_fast_code_refine[FCOMP
      literals_to_update_wl_empty_heur_literals_to_update_wl_empty]
  unfolding isasat_fast_assn_W_list[symmetric]
  .

lemma literals_to_update_wl_literals_to_update_wl_empty:
  \<open>literals_to_update_wl_heur S = {#} \<longleftrightarrow> literals_to_update_wl_empty_heur S\<close>
  by (cases S) (auto simp: literals_to_update_wl_empty_def literals_to_update_wl_empty_heur_def)

sepref_register unit_propagation_inner_loop_wl_D_heur
  select_and_remove_from_literals_to_update_wl_heur

sepref_thm unit_propagation_outer_loop_wl_D
  is \<open>PR_CONST unit_propagation_outer_loop_wl_D_heur\<close>
  :: \<open>isasat_assn\<^sup>d \<rightarrow>\<^sub>a isasat_assn\<close>
  supply [[goals_limit=1]]
  apply (subst PR_CONST_def)
  unfolding unit_propagation_outer_loop_wl_D_heur_def
    literals_to_update_wl_literals_to_update_wl_empty
  by sepref

concrete_definition (in -) unit_propagation_outer_loop_wl_D
   uses isasat_input_bounded_nempty.unit_propagation_outer_loop_wl_D.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) unit_propagation_outer_loop_wl_D_def

lemmas unit_propagation_outer_loop_wl_D[sepref_fr_rules] =
   unit_propagation_outer_loop_wl_D.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

lemma unit_propagation_outer_loop_wl_D_fast_still_fast:
  assumes 
    fast: \<open>\<forall>L\<in>#dom_m (get_clauses_wl_heur x). L < uint_max\<close> and
    inv: \<open>unit_propagation_outer_loop_wl_D_heur_inv x s'\<close> and
    le: \<open>RETURN (a1', a2') \<le> select_and_remove_from_literals_to_update_wl_heur s'\<close> and
    L: \<open>L \<in># dom_m (get_clauses_wl_heur a1')\<close>
  shows \<open>L < uint_max\<close>
proof -
  show ?thesis
    using le fast L inv by (cases s')
      (auto simp: select_and_remove_from_literals_to_update_wl_heur_def
      unit_propagation_outer_loop_wl_D_heur_inv_def)
qed


sepref_thm unit_propagation_outer_loop_wl_D_fast
  is \<open>PR_CONST unit_propagation_outer_loop_wl_D_heur\<close>
  :: \<open>[isasat_fast]\<^sub>a isasat_fast_assn\<^sup>d \<rightarrow> isasat_fast_assn\<close>
  supply [[goals_limit=1]] unit_propagation_outer_loop_wl_D_fast_still_fast[intro]
  apply (subst PR_CONST_def)
  unfolding unit_propagation_outer_loop_wl_D_heur_def
    literals_to_update_wl_literals_to_update_wl_empty
  by sepref

concrete_definition (in -) unit_propagation_outer_loop_wl_D_fast
   uses isasat_input_bounded_nempty.unit_propagation_outer_loop_wl_D_fast.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) unit_propagation_outer_loop_wl_D_fast_def

lemmas unit_propagation_outer_loop_wl_D_fast[sepref_fr_rules] =
   unit_propagation_outer_loop_wl_D_fast.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

end

end
