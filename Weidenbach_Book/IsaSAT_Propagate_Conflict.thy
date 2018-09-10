theory IsaSAT_Propagate_Conflict
  imports IsaSAT_Setup IsaSAT_Inner_Propagation
begin


subsubsection \<open>Refining Propagate And Conflict\<close>

paragraph \<open>Unit Propagation, Inner Loop\<close>

context isasat_input_bounded_nempty
begin

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

sepref_thm unit_propagation_inner_loop_wl_loop_D
  is \<open>uncurry ((PR_CONST unit_propagation_inner_loop_wl_loop_D_heur))\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a isasat_assn\<^sup>d \<rightarrow>\<^sub>a nat_assn *a nat_assn *a isasat_assn\<close>
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

concrete_definition (in -) unit_propagation_inner_loop_wl_loop_D_code
   uses isasat_input_bounded_nempty.unit_propagation_inner_loop_wl_loop_D.refine_raw
   is \<open>(uncurry ?f, _) \<in> _\<close>

prepare_code_thms (in -) unit_propagation_inner_loop_wl_loop_D_code_def

lemmas unit_propagation_inner_loop_wl_loop_D_code_refine[sepref_fr_rules] =
   unit_propagation_inner_loop_wl_loop_D_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

lemma (in isasat_input_ops) unit_propagation_inner_loop_wl_loop_D_heur_alt_def:
  \<open>unit_propagation_inner_loop_wl_loop_D_heur L S\<^sub>0 = do {
    ASSERT (nat_of_lit L < length (get_watched_wl_heur S\<^sub>0));
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
(*
(* This bound absolutely not thight *)
lemma unit_propagation_inner_loop_wl_loop_D_heur_inv_length_watchlist:
  assumes \<open>unit_propagation_inner_loop_wl_loop_D_heur_inv S0 L (j, w, S)\<close> and
    fast: \<open>isasat_fast S0\<close>
  shows
    \<open>length (get_watched_wl_heur S ! nat_of_lit L) \<le> uint64_max\<close> (is ?A) and
    \<open>length (get_watched_wl_heur S ! nat_of_lit L) < uint64_max\<close> (is ?B) and
    \<open>Suc w \<le> uint64_max\<close> (is ?C)
proof -
  obtain T where
    ST: \<open>(S, T) \<in> twl_st_heur\<close> and
    inner: \<open>unit_propagation_inner_loop_wl_loop_D_inv L (j, w, T)\<close> and
    L: \<open>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close> and
    dom_eq: \<open>dom_m (get_clauses_wl_heur S) = dom_m (get_clauses_wl_heur S0)\<close>
    using assms unfolding unit_propagation_inner_loop_wl_loop_D_heur_inv_def by blast
  obtain U V where
    corr_w: \<open>correct_watching_except j w L T\<close> and
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
     prod.case
     by fast+
  have alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of V)\<close>
    using struct_invs unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast
  have \<open>L \<in># all_lits_of_mm (mset `# ran_mf (get_clauses_wl T) + get_unit_clauses_wl T)\<close>
    using lits_in L by (auto simp: image_image is_\<L>\<^sub>a\<^sub>l\<^sub>l_def literals_are_\<L>\<^sub>i\<^sub>n_def)
  moreover have
    \<open>set_mset (all_lits_of_mm (mset `# ran_mf (get_clauses_wl T) + get_unit_clauses_wl T)) =
      set_mset (all_lits_of_mm (mset `# ran_mf (get_clauses_wl T) + get_unit_init_clss_wl T))\<close>
    apply (subst all_clss_lf_ran_m[symmetric])+
    apply (subst image_mset_union)+
    using TU UV alien
    by (cases T; cases U; cases V)
      (auto simp: in_all_lits_of_mm_ain_atms_of_iff state_wl_l_def twl_st_l_def
      cdcl\<^sub>W_restart_mset.no_strange_atm_def mset_take_mset_drop_mset')
  ultimately have 1: \<open>fst `# mset ((get_watched_wl T) L) =
      {#C \<in># dom_m (get_clauses_wl T). L \<in> set (watched_l ((get_clauses_wl T) \<propto> C))#}\<close>
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
qed *)

(* sepref_thm unit_propagation_inner_loop_wl_loop_D_fast
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
   unit_propagation_inner_loop_wl_loop_D_fast_code.refine[of \<A>\<^sub>i\<^sub>n,
     OF isasat_input_bounded_nempty_axioms] *)

sepref_register unit_propagation_inner_loop_wl_loop_D_heur
sepref_thm cut_watch_list_heur2
  is \<open>uncurry3 cut_watch_list_heur2\<close>
  :: \<open>nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a
     isasat_assn\<^sup>d \<rightarrow>\<^sub>a isasat_assn\<close>
  supply [[goals_limit=1]] length_ll_def[simp]
  unfolding cut_watch_list_heur2_def isasat_assn_def length_ll_def[symmetric]
  update_ll_def[symmetric] nth_rll_def[symmetric] shorten_take_ll_def[symmetric]
  by sepref

concrete_definition (in -) cut_watch_list_heur2_code
   uses isasat_input_bounded_nempty.cut_watch_list_heur2.refine_raw
   is \<open>(uncurry3 ?f, _)\<in>_\<close>

prepare_code_thms (in -) cut_watch_list_heur2_code_def

lemmas cut_watch_list_heur2_refine[sepref_fr_rules] =
   cut_watch_list_heur2_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

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

(* sepref_thm unit_propagation_inner_loop_wl_D_fast
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
   unit_propagation_inner_loop_wl_D_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms] *)


paragraph \<open>Unit propagation, Outer Loop\<close>

lemma select_and_remove_from_literals_to_update_wl_heur_alt_def:
  \<open>select_and_remove_from_literals_to_update_wl_heur =
   (\<lambda>(M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema, ccount,
       vdom, lcount). do {
      ASSERT(j < length M');
      ASSERT(j + 1 \<le> uint32_max);
      let L = - rev_trail_nth M' j;
      RETURN ((M', N', D', j+1, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema, ccount,
       vdom, lcount), L)
     })
    \<close>
  unfolding select_and_remove_from_literals_to_update_wl_heur_def
  apply (intro ext)
  apply (rename_tac S; case_tac S)
  by (auto intro!: ext simp: rev_trail_nth_def Let_def)

sepref_thm select_and_remove_from_literals_to_update_wl_code
  is \<open>select_and_remove_from_literals_to_update_wl_heur\<close>
  :: \<open>isasat_assn\<^sup>d \<rightarrow>\<^sub>a isasat_assn *a unat_lit_assn\<close>
  supply [[goals_limit=1]] uint32_nat_assn_plus[sepref_fr_rules]
  unfolding select_and_remove_from_literals_to_update_wl_heur_alt_def isasat_assn_def
    one_uint32_nat_def[symmetric]
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) select_and_remove_from_literals_to_update_wl_code
   uses isasat_input_bounded_nempty.select_and_remove_from_literals_to_update_wl_code.refine_raw
   is \<open>(?f, _)\<in>_\<close>

prepare_code_thms (in -) select_and_remove_from_literals_to_update_wl_code_def

lemmas select_and_remove_from_literals_to_update_wl_code_refine[sepref_fr_rules] =
   select_and_remove_from_literals_to_update_wl_code.refine[of \<A>\<^sub>i\<^sub>n,
     OF isasat_input_bounded_nempty_axioms]

definition (in -) literals_to_update_wl_literals_to_update_wl_empty :: \<open>twl_st_wl_heur \<Rightarrow> bool\<close> where
  \<open>literals_to_update_wl_literals_to_update_wl_empty S \<longleftrightarrow>
    literals_to_update_wl_heur S < length (get_trail_wl_heur S)\<close>


lemma literals_to_update_wl_literals_to_update_wl_empty_alt_def:
  \<open>literals_to_update_wl_literals_to_update_wl_empty =
    (\<lambda>(M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema, ccount,
       vdom, lcount). j < length_u M')\<close>
  unfolding literals_to_update_wl_literals_to_update_wl_empty_def
  by (auto intro!: ext)

sepref_thm literals_to_update_wl_literals_to_update_wl_empty_code
  is \<open>RETURN o literals_to_update_wl_literals_to_update_wl_empty\<close>
  :: \<open>isasat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding literals_to_update_wl_literals_to_update_wl_empty_alt_def
    isasat_assn_def
  by sepref

concrete_definition (in -) literals_to_update_wl_literals_to_update_wl_empty_code
   uses isasat_input_bounded_nempty.literals_to_update_wl_literals_to_update_wl_empty_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) literals_to_update_wl_literals_to_update_wl_empty_code_def

lemmas literals_to_update_wl_literals_to_update_wl_empty_code_hnr[sepref_fr_rules] =
   literals_to_update_wl_literals_to_update_wl_empty_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

sepref_register literals_to_update_wl_literals_to_update_wl_empty
  select_and_remove_from_literals_to_update_wl_heur
  unit_propagation_inner_loop_wl_D_heur

sepref_thm unit_propagation_outer_loop_wl_D
  is \<open>PR_CONST unit_propagation_outer_loop_wl_D_heur\<close>
  :: \<open>isasat_assn\<^sup>d \<rightarrow>\<^sub>a isasat_assn\<close>
  supply [[goals_limit=1]]
  apply (subst PR_CONST_def)
  unfolding unit_propagation_outer_loop_wl_D_heur_def
    literals_to_update_wl_literals_to_update_wl_empty_def[symmetric]
  by sepref

concrete_definition (in -) unit_propagation_outer_loop_wl_D
   uses isasat_input_bounded_nempty.unit_propagation_outer_loop_wl_D.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) unit_propagation_outer_loop_wl_D_def

lemmas unit_propagation_outer_loop_wl_D[sepref_fr_rules] =
   unit_propagation_outer_loop_wl_D.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

(* lemma unit_propagation_outer_loop_wl_D_fast_still_fast:
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
qed *)

(*
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
   unit_propagation_outer_loop_wl_D_fast.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms] *)

end

end
