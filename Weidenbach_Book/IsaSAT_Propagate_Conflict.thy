theory IsaSAT_Propagate_Conflict
  imports IsaSAT_Setup Watched_Literals_Heuristics
begin

subsubsection \<open>Refining Propagate And Conflict\<close>

paragraph \<open>Propagation, Inner Loop\<close>

context isasat_input_bounded
begin

lemma (in -)[sepref_fr_rules]:
  \<open>(return o id, RETURN o nat_of_lit) \<in> unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  by sepref_to_hoare
     (sep_auto simp: uint32_nat_rel_def br_def unat_lit_rel_def nat_lit_rel_def
      lit_of_natP_def)


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

(* TODO Kill *)
lemma watched_by_app_code_refine[sepref_fr_rules]:
  \<open>(uncurry2 watched_by_app_heur_code, uncurry2 (RETURN ooo watched_by_app)) \<in>
    [\<lambda>((S, L), K).  L \<in> snd ` D\<^sub>0 \<and> K < length (watched_by S L)]\<^sub>a
       twl_st_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>
    nat_assn\<close>
    (is \<open>_ \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>(uncurry2 watched_by_app_heur_code, uncurry2 (RETURN \<circ>\<circ>\<circ> watched_by_app))
  \<in> [comp_PRE (twl_st_heur \<times>\<^sub>f Id \<times>\<^sub>f nat_rel)
      (\<lambda>((S, L), K). L \<in> snd ` D\<^sub>0 \<and> K < length (get_watched_wl S L))
      (\<lambda>_ ((S, L), K).
          nat_of_lit L < length (get_watched_wl_heur S) \<and>
          K < length (watched_by_int S L)) (\<lambda>_. True)]\<^sub>a
    hrp_comp (twl_st_heur_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k)
             (twl_st_heur \<times>\<^sub>f Id \<times>\<^sub>f nat_rel) \<rightarrow>
    hr_comp nat_assn nat_rel\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF watched_by_app_heur_code_refine[unfolded PR_CONST_def]
        watched_by_app_watched_by_app_heur[unfolded PR_CONST_def],
        unfolded watched_by_app_heur_pre_def] .
  have pre: \<open>?pre' = ?pre\<close>
    by (intro ext) (auto simp: comp_PRE_def twl_st_assn_def twl_st_heur_def map_fun_rel_def)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def[symmetric]
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    using H unfolding im pre f .
qed


sepref_thm access_lit_in_clauses_heur_code
  is \<open>uncurry2 (RETURN ooo access_lit_in_clauses_heur)\<close>
  :: \<open>[access_lit_in_clauses_heur_pre]\<^sub>a
      twl_st_heur_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k  *\<^sub>a nat_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  supply length_rll_def[simp]
  unfolding twl_st_heur_assn_def access_lit_in_clauses_heur_alt_def
    nth_rll_def[symmetric] access_lit_in_clauses_heur_pre_def
  by sepref

concrete_definition (in -) access_lit_in_clauses_heur_code
   uses isasat_input_bounded.access_lit_in_clauses_heur_code.refine_raw
   is \<open>(uncurry2 ?f, _) \<in> _\<close>

prepare_code_thms (in -) access_lit_in_clauses_heur_code_def

lemmas access_lit_in_clauses_heur_code_refine[sepref_fr_rules] =
   access_lit_in_clauses_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]

lemma access_lit_in_clauses_heur_access_lit_in_clauses:
  \<open>(uncurry2 (RETURN ooo access_lit_in_clauses_heur),
      uncurry2 (RETURN ooo access_lit_in_clauses)) \<in>
   twl_st_heur \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<rightarrow>\<^sub>f \<langle>Id\<rangle> nres_rel\<close>
  by (intro frefI nres_relI)
     (auto simp: access_lit_in_clauses_heur_def twl_st_heur_def access_lit_in_clauses_def)

(* TODO Kill *)
lemma access_lit_in_clauses_refine[sepref_fr_rules]:
  \<open>(uncurry2 access_lit_in_clauses_heur_code, uncurry2 (RETURN ooo access_lit_in_clauses)) \<in>
    [\<lambda>((S, i), j). i < length (get_clauses_wl S) \<and> j < length_rll (get_clauses_wl S) i]\<^sub>a
       twl_st_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>
    unat_lit_assn\<close>
    (is \<open>_ \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>(uncurry2 access_lit_in_clauses_heur_code, uncurry2 (RETURN \<circ>\<circ>\<circ> access_lit_in_clauses))
  \<in> [comp_PRE (twl_st_heur \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel) (\<lambda>_. True)
      (\<lambda>_ (((_, N, _), i), j). i < length N \<and> j < length_rll N i) (\<lambda>_. True)]\<^sub>a
    hrp_comp (twl_st_heur_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k)
             (twl_st_heur \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel) \<rightarrow>
    hr_comp unat_lit_assn Id\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF access_lit_in_clauses_heur_code_refine[unfolded PR_CONST_def]
        access_lit_in_clauses_heur_access_lit_in_clauses[unfolded PR_CONST_def],
        unfolded access_lit_in_clauses_heur_pre_def] .
  have pre: \<open>?pre x \<Longrightarrow> ?pre' x\<close> for x
    unfolding comp_PRE_def
      by (auto simp: comp_PRE_def twl_st_assn_def twl_st_heur_def
          map_fun_rel_def intro!: ext)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def[symmetric]
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f apply assumption
    using pre ..
qed

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
  supply [[goals_limit = 1]] literals_are_in_\<L>\<^sub>i\<^sub>n_heur_in_D\<^sub>0'[intro] nth_rll_def[simp]
    length_rll_def[simp]
  unfolding find_unwatched_wl_st_heur_def twl_st_heur_assn_def PR_CONST_def
  find_unwatched_def nth_rll_def[symmetric] length_rll_def[symmetric]
  case_tri_bool_If find_unwatched_wl_st_heur_pre_def
  by sepref

concrete_definition (in -) find_unwatched_wl_st_heur_code
   uses isasat_input_bounded_nempty.find_unwatched_wl_st_heur_code.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) find_unwatched_wl_st_heur_code_def

lemmas find_unwatched_wl_st_heur_code_find_unwatched_wl_st_heur[sepref_fr_rules] =
   find_unwatched_wl_st_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms,
     unfolded PR_CONST_def]

(* TODO Kill *)
theorem find_unwatched_wl_st_heur_code_find_unwatched_wl_s[sepref_fr_rules]:
  \<open>(uncurry find_unwatched_wl_st_heur_code, uncurry find_unwatched_wl_st)
    \<in> [\<lambda>(S, i). \<exists>w L. unit_prop_body_wl_D_inv S w L \<and> i = watched_by_app S L w]\<^sub>a
      twl_st_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> option_assn nat_assn\<close>
    (is \<open>_ \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>(uncurry find_unwatched_wl_st_heur_code, uncurry find_unwatched_wl_st)
    \<in> [comp_PRE (twl_st_heur \<times>\<^sub>f nat_rel)
         (\<lambda>(S, i). i < length (get_clauses_wl S) \<and> 0 < i \<and> literals_are_\<L>\<^sub>i\<^sub>n S \<and>
            2 \<le> length (get_clauses_wl S ! i))
         (\<lambda>_ (S, i). i < length (get_clauses_wl_heur S) \<and> 0 < i \<and> literals_are_in_\<L>\<^sub>i\<^sub>n_heur S)
         (\<lambda>_. True)]\<^sub>a
       hrp_comp (twl_st_heur_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k)
                   (twl_st_heur \<times>\<^sub>f nat_rel) \<rightarrow>
       hr_comp (option_assn nat_assn) Id\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF
        find_unwatched_wl_st_heur_code_find_unwatched_wl_st_heur[unfolded PR_CONST_def]
        find_unwatched_wl_st_heur_find_unwatched_wl_s,
         unfolded find_unwatched_wl_st_heur_pre_def] .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
  proof -
    have [simp]: \<open>mset `# mset (take ai (tl ah)) + ak + (mset `# mset (drop (Suc ai) ah) + al) =
      mset `# mset (tl ah) + ak + al\<close> for ai ah ak al
      apply (subst (6) append_take_drop_id[of ai, symmetric])
      unfolding mset_append drop_Suc
      by auto
    have [intro]: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_heur T\<close> and
       \<open>get_clauses_wl_heur T = get_clauses_wl S\<close> if
       \<open>is_\<L>\<^sub>a\<^sub>l\<^sub>l (all_lits_of_mm (cdcl\<^sub>W_restart_mset.clauses
           (state\<^sub>W_of (twl_st_of None (st_l_of_wl None S)))))\<close> and
       \<open>(T, S) \<in> twl_st_heur\<close>
      for S and T
      using that apply (auto simp: twl_st_heur_def mset_take_mset_drop_mset
          mset_take_mset_drop_mset' clauses_def literals_are_in_\<L>\<^sub>i\<^sub>n_heur_def)
      apply (auto simp add: all_lits_of_mm_union literals_are_in_\<L>\<^sub>i\<^sub>n_mm_def is_\<L>\<^sub>a\<^sub>l\<^sub>l_def)
      done
    show ?thesis
      unfolding comp_PRE_def
      apply (intro ext impI conjI)
      subgoal
        using that by (auto dest: simp: unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def
            unit_propagation_inner_loop_body_l_inv_def watched_by_app_def)
      subgoal
        by (use that in \<open>auto simp: comp_PRE_def unit_prop_body_wl_D_inv_def
            mset_take_mset_drop_mset clauses_def mset_take_mset_drop_mset' drop_Suc
            unit_prop_body_wl_inv_def watched_by_app_def
            unit_propagation_inner_loop_body_l_inv_def twl_st_heur_def
          simp del: twl_st_of.simps st_l_of_wl.simps\<close>)
      done
  qed
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def[symmetric]
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed


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

lemma set_conflict_wl_heur_code_set_conflict_wl'[sepref_fr_rules]:
  \<open>(uncurry set_conflict_wl_heur_code, uncurry (RETURN oo set_conflict_wl')) \<in>
    [\<lambda>(C, S). get_conflict_wl S = None \<and> C < length (get_clauses_wl S) \<and>
      distinct (get_clauses_wl S ! C) \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (mset (get_clauses_wl S ! C)) \<and>
      \<not> tautology (mset (get_clauses_wl S ! C)) \<and>
      literals_are_in_\<L>\<^sub>i\<^sub>n_trail (get_trail_wl S)]\<^sub>a nat_assn\<^sup>k *\<^sub>a twl_st_assn\<^sup>d \<rightarrow>
    twl_st_assn\<close>
    (is \<open>_ \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>(uncurry set_conflict_wl_heur_code, uncurry (RETURN \<circ>\<circ> set_conflict_wl'))
  \<in> [comp_PRE (nat_rel \<times>\<^sub>f twl_st_heur) (\<lambda>_. True)
       (\<lambda>_. set_conflict_wl_heur_pre)
       (\<lambda>_. True)]\<^sub>a hrp_comp
                       (nat_assn\<^sup>k *\<^sub>a twl_st_heur_assn\<^sup>d)
                       (nat_rel \<times>\<^sub>f
                        twl_st_heur) \<rightarrow> hr_comp
           twl_st_heur_assn twl_st_heur\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF set_conflict_wl_heur_code set_conflict_wl_heur_set_conflict_wl']
    .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that unfolding comp_PRE_def twl_st_heur_def set_conflict_wl_heur_pre_def by auto
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def[symmetric]
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed

sepref_thm update_clause_wl_code
  is \<open>uncurry5 update_clause_wl_heur\<close>
  :: \<open>
    [update_clause_wl_code_pre]\<^sub>a
     unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a twl_st_heur_assn\<^sup>d \<rightarrow>
       nat_assn *a twl_st_heur_assn\<close>
  supply [[goals_limit=1]] length_rll_def[simp] length_ll_def[simp]
  unfolding update_clause_wl_heur_def twl_st_heur_assn_def Array_List_Array.swap_ll_def[symmetric]
    nth_rll_def[symmetric] delete_index_and_swap_update_def[symmetric]
    delete_index_and_swap_ll_def[symmetric]
    append_ll_def[symmetric] update_clause_wl_code_pre_def
  by sepref


concrete_definition (in -) update_clause_wl_code
  uses isasat_input_bounded_nempty.update_clause_wl_code.refine_raw
  is \<open>(uncurry5 ?f,_)\<in>_\<close>

prepare_code_thms (in -) update_clause_wl_code_def

lemmas update_clause_wl_code[sepref_fr_rules] =
  update_clause_wl_code.refine[OF isasat_input_bounded_nempty_axioms]

(* TODO Kill *)
lemma update_clause_wl_code_update_clause_wl[sepref_fr_rules]:
  \<open>(uncurry5 update_clause_wl_code, uncurry5 update_clause_wl) \<in>
    [\<lambda>(((((L, C), w), i), f), S).
      unit_prop_body_wl_D_inv S w L \<and>
      unit_prop_body_wl_D_find_unwatched_inv (Some f) C S \<and>
      C = watched_by S L ! w \<and>
      i = (if get_clauses_wl S ! C ! 0 = L then 0 else 1)]\<^sub>a
     unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a twl_st_assn\<^sup>d \<rightarrow>
       nat_assn *a twl_st_assn\<close>
    (is \<open>_ \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>(uncurry5 update_clause_wl_code, uncurry5 update_clause_wl) \<in>
    [comp_PRE (Id \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f twl_st_heur)
       (\<lambda>(((((L, C), w), i), f), S). get_clauses_wl S ! C ! f \<noteq> L)
       (\<lambda>_ (((((L, C), w), i), f), S).
           C < length (get_clauses_wl_heur S) \<and>
           f < length (get_clauses_wl_heur S ! C) \<and>
           i < length (get_clauses_wl_heur S ! C) \<and>
           nat_of_lit L < length (get_watched_wl_heur S) \<and>
           nat_of_lit (get_clauses_wl_heur S ! C ! f)
           < length (get_watched_wl_heur S) \<and>
           w < length (get_watched_wl_heur S ! nat_of_lit L)) (\<lambda>_. True)]\<^sub>a
    hrp_comp (unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a
        twl_st_heur_assn\<^sup>d)
      (Id \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f twl_st_heur) \<rightarrow>
    hr_comp (nat_assn *a twl_st_heur_assn) (nat_rel \<times>\<^sub>f twl_st_heur)\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF update_clause_wl_code update_clause_wl_heur_update_clause_wl]
    unfolding update_clause_wl_code_pre_def
    .
  have [dest]: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_mm (mset `# mset (tl (get_clauses_wl S)))\<close>
    if \<open>unit_prop_body_wl_D_inv S w L\<close>
    for S w L
  proof -
    have \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close>
      using that unfolding twl_st_heur_def map_fun_rel_def
        unit_prop_body_wl_D_find_unwatched_inv_def
        unit_prop_body_wl_find_unwatched_inv_def unit_prop_body_wl_D_inv_def
        unit_prop_body_wl_inv_def
        unit_propagation_inner_loop_body_l_inv_def by fast
    then have \<open> set_mset (all_lits_of_mm (mset `# mset (tl (get_clauses_wl S)))) \<subseteq>
       set_mset \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
      apply (subst append_take_drop_id[symmetric, of _ \<open>get_learned_wl S\<close>])
      unfolding mset_append all_lits_of_mm_union
      apply (cases S)
      by (auto simp:  mset_take_mset_drop_mset' literals_are_in_\<L>\<^sub>i\<^sub>n_mm_def clauses_def
           drop_Suc all_lits_of_mm_union is_\<L>\<^sub>a\<^sub>l\<^sub>l_def)
    then show ?thesis
      unfolding literals_are_in_\<L>\<^sub>i\<^sub>n_mm_def by blast
  qed
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    unfolding comp_PRE_def
    apply (cases x)
    apply (clarify)
    apply (intro conjI impI allI)
    subgoal for L C w i f M N U D NE UE Q W
      using that find_unwatched_get_clause_neq_L[of f \<open>(M, N, U, D, NE, UE, Q, W)\<close> L w]
      by (auto simp add: watched_by_app_def)
    subgoal for L C w i f M N U D NE UE Q W y
      apply (subgoal_tac \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_mm (mset `# mset (tl N))\<close>)
      subgoal
        using literals_are_in_\<L>\<^sub>i\<^sub>n_mm_in_\<L>\<^sub>a\<^sub>l\<^sub>l[of \<open>tl N\<close> \<open>(W L ! w - 1)\<close> f]
        using that unfolding comp_PRE_def twl_st_heur_def map_fun_rel_def
          unit_prop_body_wl_D_find_unwatched_inv_def
          unit_prop_body_wl_find_unwatched_inv_def unit_prop_body_wl_D_inv_def
          unit_prop_body_wl_inv_def
          unit_propagation_inner_loop_body_l_inv_def
        by (auto dest: simp: nth_tl)[]
      subgoal
        using that by auto
      done
    done
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def[symmetric]
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed


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

lemma propagate_lit_wl_code_propagate_lit_wl[sepref_fr_rules]:
  \<open>(uncurry3 propagate_lit_wl_code, uncurry3 (RETURN oooo propagate_lit_wl)) \<in>
    [\<lambda>(((L, C), i), S). undefined_lit (get_trail_wl S) L \<and> L \<in> snd ` D\<^sub>0 \<and>
          get_conflict_wl S = None \<and> 1 - i < length (get_clauses_wl S ! C) \<and> i \<le> 1 \<and>
          C < length (get_clauses_wl S)]\<^sub>a
     unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a twl_st_assn\<^sup>d \<rightarrow> twl_st_assn\<close>
    (is \<open>?fun \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?fun \<in>
     [comp_PRE (Id \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f twl_st_heur)
       (\<lambda>(((L, C), i), S). undefined_lit (get_trail_wl S) L \<and> get_conflict_wl S = None)
       (\<lambda>_ (((L, C), i), S). undefined_lit (get_trail_wl_heur S) L \<and> L \<in> snd ` D\<^sub>0 \<and>
          1 - i < length (get_clauses_wl_heur S ! C) \<and> i \<le> 1 \<and> C < length (get_clauses_wl_heur S))
       (\<lambda>_. True)]\<^sub>a
     hrp_comp (unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a twl_st_heur_assn\<^sup>d)
                      (Id \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f twl_st_heur) \<rightarrow>
     hr_comp twl_st_heur_assn twl_st_heur\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF propagate_lit_wl_code[unfolded PR_CONST_def]
       propagate_lit_wl_heur_propagate_lit_wl]
    unfolding propagate_lit_wl_heur_pre_def
    .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that unfolding comp_PRE_def twl_st_heur_def
    by (auto simp: image_image)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def[symmetric]
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed

end

text \<open>Find a less hack-like solution\<close>
setup \<open>map_theory_claset (fn ctxt => ctxt delSWrapper "split_all_tac")\<close>

context isasat_input_bounded_nempty
begin

context
begin

lemma unit_propagation_inner_loop_body_wl_D_helper:
  \<open>unit_prop_body_wl_D_inv b ba a \<Longrightarrow> literals_are_in_\<L>\<^sub>i\<^sub>n_trail (get_trail_wl b)\<close>
  unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def
  by (rule literals_are_\<L>\<^sub>i\<^sub>n_literals_are_in_\<L>\<^sub>i\<^sub>n_trail[of _ \<open>Some (a, ba)\<close>])
    auto

sepref_thm unit_propagation_inner_loop_body_wl_D
  is \<open>uncurry2 ((PR_CONST unit_propagation_inner_loop_body_wl_D) :: nat literal \<Rightarrow> nat \<Rightarrow>
           nat twl_st_wl \<Rightarrow> (nat \<times> nat twl_st_wl) nres)\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a twl_st_assn\<^sup>d \<rightarrow>\<^sub>a nat_assn *a twl_st_assn\<close>
  supply
    if_splits[split] unit_prop_body_wl_D_invD[intro,dest]
    watched_by_app_def[symmetric,simp]
    access_lit_in_clauses_def[simp] unit_prop_body_wl_D_invD'[intro]
    length_rll_def[simp] find_unwatched_not_tauto[dest]
    unit_propagation_inner_loop_body_wl_D_helper[intro]
  supply undefined_lit_polarity_st_iff[iff]
  unfolding unit_propagation_inner_loop_body_wl_D_def length_rll_def[symmetric] PR_CONST_def
  unfolding watched_by_app_def[symmetric] access_lit_in_clauses_def[symmetric]
    find_unwatched_l_find_unwatched_wl_s
  unfolding nth_rll_def[symmetric]
  unfolding lms_fold_custom_empty swap_ll_def[symmetric]
  unfolding delete_index_and_swap_update_def[symmetric] append_update_def[symmetric]
    find_unwatched_wl_st_heur_def[symmetric] polarity_st_def[symmetric]
    set_conflict_wl'_alt_def[symmetric] fast_minus_def[symmetric]
    SET_FALSE_def[symmetric] SET_TRUE_def[symmetric]
  supply [[goals_limit=1]]
  by sepref


sepref_register find_unwatched_wl_st_heur
sepref_thm unit_propagation_inner_loop_body_wl_heur
  is \<open>uncurry2 (PR_CONST unit_propagation_inner_loop_body_wl_heur)\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a twl_st_heur_assn\<^sup>d \<rightarrow>\<^sub>a nat_assn *a twl_st_heur_assn\<close>
  supply
    if_splits[split] unit_prop_body_wl_D_invD[intro,dest]
    watched_by_app_def[symmetric,simp]
    access_lit_in_clauses_def[simp] unit_prop_body_wl_D_invD'[intro]
    length_rll_def[simp] find_unwatched_not_tauto[dest]
    unit_propagation_inner_loop_body_wl_D_helper[intro]
    watched_by_app_heur_code_refine[sepref_fr_rules]
  supply undefined_lit_polarity_st_iff[iff]
    unit_prop_body_wl_D_find_unwatched_heur_inv_def[simp]
  unfolding unit_propagation_inner_loop_body_wl_heur_def length_rll_def[symmetric] PR_CONST_def
  unfolding nth_rll_def[symmetric]
  unfolding lms_fold_custom_empty swap_ll_def[symmetric]
  unfolding delete_index_and_swap_update_def[symmetric] append_update_def[symmetric]
    set_conflict_wl'_alt_def[symmetric] fast_minus_def[symmetric]
    SET_FALSE_def[symmetric] SET_TRUE_def[symmetric]
  supply [[goals_limit=1]]
  by sepref

end

concrete_definition (in -) unit_propagation_inner_loop_body_wl_D_code
   uses isasat_input_bounded_nempty.unit_propagation_inner_loop_body_wl_D.refine_raw
   is \<open>(uncurry2 ?f, _) \<in> _\<close>

prepare_code_thms (in -) unit_propagation_inner_loop_body_wl_D_code_def

sepref_register unit_propagation_inner_loop_body_wl_D

lemmas unit_propagation_inner_loop_body_wl_D_code_refine[sepref_fr_rules] =
   unit_propagation_inner_loop_body_wl_D_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]


paragraph \<open>Unit Propagation, Inner Loop\<close>

definition (in -) length_ll_fs :: \<open>nat twl_st_wl \<Rightarrow> nat literal \<Rightarrow> nat\<close> where
  \<open>length_ll_fs = (\<lambda>(_, _, _, _, _, _, _, W) L. length (W L))\<close>

definition (in -) length_ll_fs_heur :: \<open>twl_st_wl_heur \<Rightarrow> nat literal \<Rightarrow> nat\<close> where
  \<open>length_ll_fs_heur = (\<lambda>(M, N, U, D, Q, W, _) L. length (W ! nat_of_lit L))\<close>

lemma length_ll_fs_heur_length_ll_fs:
    \<open>(uncurry (RETURN oo length_ll_fs_heur), uncurry (RETURN oo length_ll_fs)) \<in>
    [\<lambda>(S, L). L \<in> snd ` D\<^sub>0]\<^sub>f twl_st_heur \<times>\<^sub>r Id \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (rename_tac x y, case_tac x, case_tac y)
  by (auto simp: length_ll_fs_def length_ll_fs_heur_def twl_st_heur_def map_fun_rel_def)

lemma (in -) get_watched_wl_heur_def: \<open>get_watched_wl_heur = (\<lambda>(M, N, U, D, Q, W, _). W)\<close>
  by (intro ext, rename_tac x, case_tac x) (auto intro!: ext)

sepref_thm length_ll_fs_heur_code
  is \<open>uncurry (RETURN oo length_ll_fs_heur)\<close>
  :: \<open>[\<lambda>(S, L). nat_of_lit L < length (get_watched_wl_heur S)]\<^sub>a
      twl_st_heur_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> nat_assn\<close>
  unfolding length_ll_fs_heur_def get_watched_wl_heur_def twl_st_heur_assn_def
    length_ll_def[symmetric]
  supply [[goals_limit=1]]
  by sepref

concrete_definition (in -) length_ll_fs_heur_code
   uses isasat_input_bounded_nempty.length_ll_fs_heur_code.refine_raw
   is \<open>(uncurry ?f, _) \<in> _\<close>

prepare_code_thms (in -) length_ll_fs_heur_code_def

lemmas length_ll_fs_heur_code_refine[sepref_fr_rules] =
   length_ll_fs_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

lemma length_ll_fs_heur_code_length_ll_fs[sepref_fr_rules]:
  \<open>(uncurry length_ll_fs_heur_code, uncurry (RETURN oo length_ll_fs)) \<in>
    [\<lambda>(S, L). L \<in> snd ` D\<^sub>0]\<^sub>a
     twl_st_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> nat_assn\<close>
    (is \<open>?fun \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
thm hfref_compI_PRE_aux[OF length_ll_fs_heur_code_refine length_ll_fs_heur_length_ll_fs]
  have H: \<open>?fun \<in> [comp_PRE (twl_st_heur \<times>\<^sub>f Id) (\<lambda>(S, L). L \<in> snd ` D\<^sub>0)
    (\<lambda>_ (S, L). nat_of_lit L < length (get_watched_wl_heur S))
    (\<lambda>_. True)]\<^sub>a hrp_comp (twl_st_heur_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k)
                   (twl_st_heur \<times>\<^sub>f Id) \<rightarrow> hr_comp nat_assn nat_rel\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF length_ll_fs_heur_code_refine length_ll_fs_heur_length_ll_fs]
    .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that unfolding comp_PRE_def twl_st_heur_def
    by (auto simp: image_image map_fun_rel_def)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def[symmetric]
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed

lemma length_ll_fs_alt_def: \<open>length_ll_fs S L = length_ll_f (watched_by S) L\<close>
  by (cases S) (auto simp: length_ll_fs_def length_ll_f_def)

sepref_register unit_propagation_inner_loop_wl_loop_D

sepref_thm unit_propagation_inner_loop_wl_loop_D
  is \<open>uncurry ((PR_CONST unit_propagation_inner_loop_wl_loop_D) :: nat literal \<Rightarrow>
           nat twl_st_wl \<Rightarrow> (nat \<times> nat twl_st_wl) nres)\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a twl_st_assn\<^sup>d \<rightarrow>\<^sub>a nat_assn *a twl_st_assn\<close>
  unfolding unit_propagation_inner_loop_wl_loop_D_def PR_CONST_def
  unfolding watched_by_nth_watched_app watched_app_def[symmetric]
    length_ll_f_def[symmetric] length_ll_fs_alt_def[symmetric]
  unfolding nth_ll_def[symmetric]
  unfolding swap_ll_def[symmetric]
  unfolding delete_index_and_swap_update_def[symmetric] append_update_def[symmetric]
    is_None_def[symmetric] get_conflict_wl_is_None length_ll_fs_def[symmetric]
  supply [[goals_limit=1]]
  by sepref


concrete_definition (in -) unit_propagation_inner_loop_wl_loop_D_code
   uses isasat_input_bounded_nempty.unit_propagation_inner_loop_wl_loop_D.refine_raw
   is \<open>(uncurry ?f, _) \<in> _\<close>

prepare_code_thms (in -) unit_propagation_inner_loop_wl_loop_D_code_def

lemmas unit_propagation_inner_loop_wl_loop_D_code_refine[sepref_fr_rules] =
   unit_propagation_inner_loop_wl_loop_D_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

sepref_register unit_propagation_inner_loop_wl_D
sepref_thm unit_propagation_inner_loop_wl_D
  is \<open>uncurry (PR_CONST unit_propagation_inner_loop_wl_D)\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a twl_st_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_assn\<close>
  supply [[goals_limit=1]]
  unfolding PR_CONST_def unit_propagation_inner_loop_wl_D_def
  by sepref

concrete_definition (in -) unit_propagation_inner_loop_wl_D_code
   uses isasat_input_bounded_nempty.unit_propagation_inner_loop_wl_D.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) unit_propagation_inner_loop_wl_D_code_def

lemmas unit_propagation_inner_loop_wl_D_code_refine[sepref_fr_rules] =
   unit_propagation_inner_loop_wl_D_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]


paragraph \<open>Unit propagation, Outer Loop\<close>

definition (in -) select_and_remove_from_literals_to_update_wl_heur
  :: \<open>twl_st_wl_heur_W_list \<Rightarrow> twl_st_wl_heur_W_list \<times> _\<close> where
  \<open>select_and_remove_from_literals_to_update_wl_heur =
     (\<lambda>(M, N, U, D, Q, W, other).  ((M, N, U, D, tl Q, W, other), hd Q))\<close>

definition get_literals_to_update_wl where
   \<open>get_literals_to_update_wl = (\<lambda>(M, N, U, D, NE, UE, Q, W). Q)\<close>

definition get_literals_to_update_wl_heur_W_list where
   \<open>get_literals_to_update_wl_heur_W_list = (\<lambda>(M, N, U, D, Q, W, _). Q)\<close>

definition literals_to_update_wl_empty_heur :: \<open>twl_st_wl_heur_W_list \<Rightarrow> bool\<close>  where
  \<open>literals_to_update_wl_empty_heur = (\<lambda>(M, N, U, D, Q, W, oth). Q = [])\<close>

lemma
  select_and_remove_from_literals_to_update_wl_heur_select_and_remove_from_literals_to_update_wl:
  \<open>(RETURN o select_and_remove_from_literals_to_update_wl_heur,
    select_and_remove_from_literals_to_update_wl) \<in>
    [\<lambda>S. \<not>literals_to_update_wl_empty S]\<^sub>f
      (twl_st_wl_heur_W_list_rel O twl_st_heur) \<rightarrow>
       \<langle>(twl_st_wl_heur_W_list_rel O twl_st_heur) \<times>\<^sub>r Id\<rangle>nres_rel\<close>
  unfolding select_and_remove_from_literals_to_update_wl_heur_def
  select_and_remove_from_literals_to_update_wl_def get_literals_to_update_wl_heur_W_list_def
  twl_st_wl_heur_W_list_rel_twl_st_rel get_literals_to_update_wl_def
  literals_to_update_wl_empty_def
  apply (intro frefI nres_relI)
  apply (rename_tac x y, case_tac x, case_tac y,
      case_tac \<open>get_literals_to_update_wl_heur_W_list y\<close>)
  unfolding get_literals_to_update_wl_def get_literals_to_update_wl_heur_W_list_def
  by (auto intro!: RETURN_SPEC_refine simp: nempty_list_mset_rel_iff)

sepref_thm select_and_remove_from_literals_to_update_wl_code
  is \<open>RETURN o select_and_remove_from_literals_to_update_wl_heur\<close>
  :: \<open>[\<lambda>S. \<not>literals_to_update_wl_empty_heur S]\<^sub>a
      twl_st_heur_W_list_assn\<^sup>d \<rightarrow> twl_st_heur_W_list_assn *a unat_lit_assn\<close>
  supply [[goals_limit=1]]
  unfolding select_and_remove_from_literals_to_update_wl_heur_def twl_st_heur_W_list_assn_def
    literals_to_update_wl_empty_heur_def
  supply [[goals_limit = 1]]
  by sepref


concrete_definition (in -) select_and_remove_from_literals_to_update_wl_code
   uses isasat_input_bounded_nempty.select_and_remove_from_literals_to_update_wl_code.refine_raw
   is \<open>(?f, _)\<in>_\<close>

prepare_code_thms (in -) select_and_remove_from_literals_to_update_wl_code_def

lemmas select_and_remove_from_literals_to_update_wl_code_refine[sepref_fr_rules] =
   select_and_remove_from_literals_to_update_wl_code.refine[of \<A>\<^sub>i\<^sub>n,
     OF isasat_input_bounded_nempty_axioms]

theorem
  select_and_remove_from_literals_to_update_wl_code_select_and_remove_from_literals_to_update_wl
  [sepref_fr_rules]:
  \<open>(select_and_remove_from_literals_to_update_wl_code,
     select_and_remove_from_literals_to_update_wl)
    \<in> [\<lambda>S. \<not> literals_to_update_wl_empty S]\<^sub>a twl_st_assn\<^sup>d \<rightarrow> twl_st_assn *a
          unat_lit_assn\<close>
    (is \<open>?fun \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?fun
    \<in> [comp_PRE (twl_st_wl_heur_W_list_rel O twl_st_heur)
         (\<lambda>S. \<not> literals_to_update_wl_empty S)
         (\<lambda>_ S. \<not> literals_to_update_wl_empty_heur S)
         (\<lambda>_. True)]\<^sub>a
      hrp_comp (twl_st_heur_W_list_assn\<^sup>d) (twl_st_wl_heur_W_list_rel O twl_st_heur) \<rightarrow>
      hr_comp (twl_st_heur_W_list_assn *a unat_lit_assn)
           ((twl_st_wl_heur_W_list_rel O twl_st_heur) \<times>\<^sub>f Id)\<close>
     (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF select_and_remove_from_literals_to_update_wl_code_refine
     select_and_remove_from_literals_to_update_wl_heur_select_and_remove_from_literals_to_update_wl]
    .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that unfolding comp_PRE_def twl_st_heur_def literals_to_update_wl_empty_heur_def
      literals_to_update_wl_empty_def twl_st_wl_heur_W_list_rel_def
    by (auto simp: image_image map_fun_rel_def Nil_list_mset_rel_iff)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def[symmetric]
    twl_st_assn_W_list[symmetric]
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def
    twl_st_assn_W_list[symmetric] hr_comp_prod_conv
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed

sepref_thm literals_to_update_wl_empty_heur_code
  is \<open>RETURN o literals_to_update_wl_empty_heur\<close>
  :: \<open>twl_st_heur_W_list_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  supply [[goals_limit=1]]
  unfolding select_and_remove_from_literals_to_update_wl_heur_def twl_st_heur_W_list_assn_def
    literals_to_update_wl_empty_heur_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) literals_to_update_wl_empty_heur_code
   uses isasat_input_bounded_nempty.literals_to_update_wl_empty_heur_code.refine_raw
   is \<open>(?f, _)\<in>_\<close>

prepare_code_thms (in -) literals_to_update_wl_empty_heur_code_def

lemmas literals_to_update_wl_empty_heur_code_refine[sepref_fr_rules] =
   literals_to_update_wl_empty_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

lemma literals_to_update_wl_empty_heur_literals_to_update_wl_empty:
  \<open>(RETURN o literals_to_update_wl_empty_heur, RETURN o literals_to_update_wl_empty) \<in>
    twl_st_wl_heur_W_list_rel O twl_st_heur \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  unfolding literals_to_update_wl_empty_heur_def literals_to_update_wl_empty_def
    twl_st_wl_heur_W_list_rel_twl_st_rel
  apply (intro frefI nres_relI)
  apply (rename_tac x y, case_tac x, case_tac y)
  by (auto simp: Nil_list_mset_rel_iff empty_list_mset_rel_iff)

lemma literals_to_update_wl_empty_heur_code_literals_to_update_wl_empty[sepref_fr_rules]:
  \<open>(literals_to_update_wl_empty_heur_code, RETURN \<circ> literals_to_update_wl_empty)
     \<in> twl_st_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  using literals_to_update_wl_empty_heur_code_refine[FCOMP
      literals_to_update_wl_empty_heur_literals_to_update_wl_empty]
  unfolding twl_st_assn_W_list[symmetric]
  .

sepref_register unit_propagation_outer_loop_wl_D
sepref_thm unit_propagation_outer_loop_wl_D
  is \<open>((PR_CONST unit_propagation_outer_loop_wl_D) :: nat twl_st_wl \<Rightarrow> (nat twl_st_wl) nres)\<close>
  :: \<open>twl_st_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_assn\<close>
  supply [[goals_limit=1]]
  apply (subst PR_CONST_def)
  unfolding unit_propagation_outer_loop_wl_D_def
    literals_to_update_wl_literals_to_update_wl_empty
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) unit_propagation_outer_loop_wl_D
   uses isasat_input_bounded_nempty.unit_propagation_outer_loop_wl_D.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) unit_propagation_outer_loop_wl_D_def

lemmas unit_propagation_outer_loop_wl_D[sepref_fr_rules] =
   unit_propagation_outer_loop_wl_D.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

end

end