theory IsaSAT_Propagate_Conflict
  imports IsaSAT_Setup Watched_Literals_Heuristics
begin

subsubsection \<open>Refining Propagate And Conflict\<close>

paragraph \<open>Propagation, Inner Loop\<close>

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
        twl_st_heur_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> nat_assn\<close>
  supply [[goals_limit=1]]
  unfolding watched_by_app_heur_alt_def twl_st_heur_assn_def nth_rll_def[symmetric]
   watched_by_app_heur_pre_def
  by sepref

concrete_definition (in -) watched_by_app_heur_code
   uses isasat_input_bounded.watched_by_app_heur_code.refine_raw
   is \<open>(uncurry2 ?f, _) \<in> _\<close>

prepare_code_thms (in -) watched_by_app_heur_code_def

lemmas watched_by_app_heur_code_refine[sepref_fr_rules] =
   watched_by_app_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]

sepref_thm access_lit_in_clauses_heur_code
  is \<open>uncurry2 (RETURN ooo access_lit_in_clauses_heur)\<close>
  :: \<open>[access_lit_in_clauses_heur_pre]\<^sub>a
      twl_st_heur_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k  *\<^sub>a nat_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  supply length_rll_def[simp]
  unfolding twl_st_heur_assn_def access_lit_in_clauses_heur_alt_def
    fmap_rll_def[symmetric] access_lit_in_clauses_heur_pre_def
  by sepref

concrete_definition (in -) access_lit_in_clauses_heur_code
   uses isasat_input_bounded.access_lit_in_clauses_heur_code.refine_raw
   is \<open>(uncurry2 ?f, _) \<in> _\<close>

prepare_code_thms (in -) access_lit_in_clauses_heur_code_def

lemmas access_lit_in_clauses_heur_code_refine[sepref_fr_rules] =
   access_lit_in_clauses_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]

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

context isasat_input_bounded_nempty
begin

sepref_thm find_unwatched_wl_st_heur_code
  is \<open>uncurry ((PR_CONST find_unwatched_wl_st_heur))\<close>
  :: \<open>[find_unwatched_wl_st_heur_pre]\<^sub>a
         twl_st_heur_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> option_assn nat_assn\<close>
  supply [[goals_limit = 1]] literals_are_in_\<L>\<^sub>i\<^sub>n_heur_in_D\<^sub>0'[intro] fmap_rll_def[simp]
    length_rll_def[simp] fmap_length_rll_def[simp]
  unfolding find_unwatched_wl_st_heur_def twl_st_heur_assn_def PR_CONST_def
  find_unwatched_def fmap_rll_def[symmetric] fmap_length_rll_def[symmetric]
  case_tri_bool_If find_unwatched_wl_st_heur_pre_def
  by sepref

concrete_definition (in -) find_unwatched_wl_st_heur_code
   uses isasat_input_bounded_nempty.find_unwatched_wl_st_heur_code.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) find_unwatched_wl_st_heur_code_def

lemmas find_unwatched_wl_st_heur_code_find_unwatched_wl_st_heur[sepref_fr_rules] =
   find_unwatched_wl_st_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms,
     unfolded PR_CONST_def]

sepref_thm set_conflict_wl_heur_code
  is \<open>uncurry set_conflict_wl_heur\<close>
  :: \<open>[set_conflict_wl_heur_pre]\<^sub>a
    nat_assn\<^sup>k *\<^sub>a twl_st_heur_assn\<^sup>d \<rightarrow> twl_st_heur_assn\<close>
  supply [[goals_limit=1]]
  unfolding set_conflict_wl_heur_def twl_st_heur_assn_def IICF_List_Mset.lms_fold_custom_empty
    set_conflict_wl_heur_pre_def
  by sepref

concrete_definition (in -) set_conflict_wl_heur_code
  uses isasat_input_bounded_nempty.set_conflict_wl_heur_code.refine_raw
  is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) set_conflict_wl_heur_code_def

lemmas set_conflict_wl_heur_code[sepref_fr_rules] =
  set_conflict_wl_heur_code.refine[OF isasat_input_bounded_nempty_axioms]

sepref_thm update_clause_wl_code
  is \<open>uncurry5 update_clause_wl_heur\<close>
  :: \<open>
    [update_clause_wl_code_pre]\<^sub>a
     unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a twl_st_heur_assn\<^sup>d \<rightarrow>
       nat_assn *a twl_st_heur_assn\<close>
  supply [[goals_limit=1]] length_rll_def[simp] length_ll_def[simp]
  unfolding update_clause_wl_heur_def twl_st_heur_assn_def Array_List_Array.swap_ll_def[symmetric]
    fmap_rll_def[symmetric] delete_index_and_swap_update_def[symmetric]
    delete_index_and_swap_ll_def[symmetric]
    append_ll_def[symmetric] update_clause_wl_code_pre_def
  by sepref


concrete_definition (in -) update_clause_wl_code
  uses isasat_input_bounded_nempty.update_clause_wl_code.refine_raw
  is \<open>(uncurry5 ?f,_)\<in>_\<close>

prepare_code_thms (in -) update_clause_wl_code_def

lemmas update_clause_wl_code[sepref_fr_rules] =
  update_clause_wl_code.refine[OF isasat_input_bounded_nempty_axioms]

sepref_thm propagate_lit_wl_code
  is \<open>uncurry3 (RETURN oooo (PR_CONST propagate_lit_wl_heur))\<close>
  :: \<open>[propagate_lit_wl_heur_pre]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a twl_st_heur_assn\<^sup>d \<rightarrow> twl_st_heur_assn\<close>
  unfolding PR_CONST_def propagate_lit_wl_heur_def twl_st_heur_assn_def
    cons_trail_Propagated_def[symmetric]
  supply [[goals_limit=1]]length_rll_def[simp] length_ll_def[simp]
  unfolding update_clause_wl_heur_def twl_st_heur_assn_def Array_List_Array.swap_ll_def[symmetric]
    propagate_lit_wl_heur_pre_def
  by sepref


concrete_definition (in -) propagate_lit_wl_code
  uses isasat_input_bounded_nempty.propagate_lit_wl_code.refine_raw
  is \<open>(uncurry3 ?f, _) \<in> _\<close>

prepare_code_thms (in -) propagate_lit_wl_code_def

lemmas propagate_lit_wl_code[sepref_fr_rules] =
  propagate_lit_wl_code.refine[OF isasat_input_bounded_nempty_axioms, unfolded PR_CONST_def]

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
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a twl_st_heur_assn\<^sup>d \<rightarrow>\<^sub>a nat_assn *a twl_st_heur_assn\<close>
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
  supply [[goals_limit=1]]
  by sepref

end

concrete_definition (in -) unit_propagation_inner_loop_body_wl_heur_code
   uses isasat_input_bounded_nempty.unit_propagation_inner_loop_body_wl_heur.refine_raw
   is \<open>(uncurry2 ?f, _) \<in> _\<close>

prepare_code_thms (in -) unit_propagation_inner_loop_body_wl_heur_code_def

sepref_register unit_propagation_inner_loop_body_wl_D

lemmas unit_propagation_inner_loop_body_wl_D_code_refine[sepref_fr_rules] =
   unit_propagation_inner_loop_body_wl_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]


paragraph \<open>Unit Propagation, Inner Loop\<close>

definition (in -) length_ll_fs :: \<open>nat twl_st_wl \<Rightarrow> nat literal \<Rightarrow> nat\<close> where
  \<open>length_ll_fs = (\<lambda>(_, _, _, _, _, _, _, W) L. length (W L))\<close>

definition (in -) length_ll_fs_heur :: \<open>twl_st_wl_heur \<Rightarrow> nat literal \<Rightarrow> nat\<close> where
  \<open>length_ll_fs_heur S L = length (watched_by_int S L)\<close>

lemma length_ll_fs_heur_alt_def:
  \<open>length_ll_fs_heur = (\<lambda>(M, N, U, D, Q, W, _) L. length (W ! nat_of_lit L))\<close>
  unfolding length_ll_fs_heur_def
  apply (intro ext)
  apply (case_tac S)
  by auto

lemma (in -) get_watched_wl_heur_def: \<open>get_watched_wl_heur = (\<lambda>(M, N, U, D, Q, W, _). W)\<close>
  by (intro ext, rename_tac x, case_tac x) auto

sepref_thm length_ll_fs_heur_code
  is \<open>uncurry (RETURN oo length_ll_fs_heur)\<close>
  :: \<open>[\<lambda>(S, L). nat_of_lit L < length (get_watched_wl_heur S)]\<^sub>a
      twl_st_heur_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> nat_assn\<close>
  unfolding length_ll_fs_heur_alt_def get_watched_wl_heur_def twl_st_heur_assn_def
    length_ll_def[symmetric]
  supply [[goals_limit=1]]
  by sepref

concrete_definition (in -) length_ll_fs_heur_code
   uses isasat_input_bounded_nempty.length_ll_fs_heur_code.refine_raw
   is \<open>(uncurry ?f, _) \<in> _\<close>

prepare_code_thms (in -) length_ll_fs_heur_code_def

lemmas length_ll_fs_heur_code_refine[sepref_fr_rules] =
   length_ll_fs_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

sepref_register unit_propagation_inner_loop_body_wl_heur

thm length_ll_fs_heur_def[symmetric]
lemma unit_propagation_inner_loop_wl_loop_D_heur_cond:
  \<open>unit_propagation_inner_loop_wl_loop_D_heur_inv a s' \<Longrightarrow>  s' = (a1', a2') \<Longrightarrow>
       nat_of_lit a < length (get_watched_wl_heur a2')\<close>
  by (auto simp: unit_propagation_inner_loop_wl_loop_D_heur_inv_def
      twl_st_heur_def map_fun_rel_def)

sepref_thm unit_propagation_inner_loop_wl_loop_D
  is \<open>uncurry ((PR_CONST unit_propagation_inner_loop_wl_loop_D_heur))\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a twl_st_heur_assn\<^sup>d \<rightarrow>\<^sub>a nat_assn *a twl_st_heur_assn\<close>
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

sepref_register unit_propagation_inner_loop_wl_loop_D_heur
sepref_thm unit_propagation_inner_loop_wl_D
  is \<open>uncurry (PR_CONST unit_propagation_inner_loop_wl_D_heur)\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a twl_st_heur_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_heur_assn\<close>
  supply [[goals_limit=1]]
  unfolding PR_CONST_def unit_propagation_inner_loop_wl_D_heur_def
  by sepref

concrete_definition (in -) unit_propagation_inner_loop_wl_D_code
   uses isasat_input_bounded_nempty.unit_propagation_inner_loop_wl_D.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) unit_propagation_inner_loop_wl_D_code_def

lemmas unit_propagation_inner_loop_wl_D_code_refine[sepref_fr_rules] =
   unit_propagation_inner_loop_wl_D_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]


paragraph \<open>Unit propagation, Outer Loop\<close>

definition (in -) select_and_remove_from_literals_to_update_wl_heur'
  :: \<open>twl_st_wl_heur_W_list \<Rightarrow> twl_st_wl_heur_W_list \<times> _\<close> where
  \<open>select_and_remove_from_literals_to_update_wl_heur' =
     (\<lambda>(M, N, U, D, Q, W, other).  ((M, N, U, D, tl Q, W, other), hd Q))\<close>

definition get_literals_to_update_wl where
   \<open>get_literals_to_update_wl = (\<lambda>(M, N, U, D, NE, UE, Q, W). Q)\<close>

definition get_literals_to_update_wl_heur_W_list where
   \<open>get_literals_to_update_wl_heur_W_list = (\<lambda>(M, N, U, D, Q, W, _). Q)\<close>

definition literals_to_update_wl_empty_heur' :: \<open>twl_st_wl_heur_W_list \<Rightarrow> bool\<close>  where
  \<open>literals_to_update_wl_empty_heur' = (\<lambda>(M, N, U, D, Q, W, oth). Q = [])\<close>

definition (in isasat_input_ops) twl_st_wl_heur_W_list_rel
  :: \<open>(twl_st_wl_heur_W_list \<times> twl_st_wl_heur) set\<close>
where
  \<open>twl_st_wl_heur_W_list_rel =
     (Id :: ((nat,nat) ann_lits \<times> _) set) \<times>\<^sub>r
     (Id :: (nat clauses_l  \<times> _) set) \<times>\<^sub>r
     nat_rel \<times>\<^sub>r
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
  (trail_assn *a clauses_ll_assn *a nat_assn *a
  option_lookup_clause_assn *a
  (list_assn unat_lit_assn) *a
  arrayO_assn (arl_assn nat_assn) *a
  vmtf_remove_conc *a phase_saver_conc *a uint32_nat_assn *a cach_refinement_assn *a
  lbd_assn *a out_learned_assn *a stats_assn
  )\<close>

lemma (in isasat_input_ops) twl_st_heur_assn_W_list:
  \<open>twl_st_heur_assn = hr_comp twl_st_heur_W_list_assn twl_st_wl_heur_W_list_rel\<close>
  unfolding twl_st_heur_assn_def twl_st_heur_W_list_assn_def twl_st_wl_heur_W_list_rel_def
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
    \<in> [\<lambda>S. \<not> literals_to_update_wl_empty_heur S]\<^sub>a twl_st_heur_assn\<^sup>d \<rightarrow> twl_st_heur_assn *a
          unat_lit_assn\<close>
    (is \<open>?fun \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
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
    twl_st_heur_assn_W_list[symmetric]
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    twl_st_heur_assn_W_list[symmetric] hr_comp_prod_conv
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
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
     \<in> twl_st_heur_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  using literals_to_update_wl_empty_heur_code_refine[FCOMP
      literals_to_update_wl_empty_heur_literals_to_update_wl_empty]
  unfolding twl_st_heur_assn_W_list[symmetric]
  .

lemma literals_to_update_wl_literals_to_update_wl_empty:
  \<open>literals_to_update_wl_heur S = {#} \<longleftrightarrow> literals_to_update_wl_empty_heur S\<close>
  by (cases S) (auto simp: literals_to_update_wl_empty_def literals_to_update_wl_empty_heur_def)

sepref_register unit_propagation_inner_loop_wl_D_heur
  select_and_remove_from_literals_to_update_wl_heur

sepref_thm unit_propagation_outer_loop_wl_D
  is \<open>PR_CONST unit_propagation_outer_loop_wl_D_heur\<close>
  :: \<open>twl_st_heur_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_heur_assn\<close>
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

end

end
