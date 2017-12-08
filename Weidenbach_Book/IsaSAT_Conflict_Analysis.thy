theory IsaSAT_Conflict_Analysis
  imports IsaSAT_Setup Watched_Literals_Heuristics
begin

paragraph \<open>Skip and resolve\<close>

context isasat_input_bounded_nempty
begin


sepref_thm get_conflict_wll_is_Nil_code
  is \<open>(PR_CONST get_conflict_wll_is_Nil_heur)\<close>
  :: \<open>twl_st_heur_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  supply [[goals_limit=1]]
  apply (subst PR_CONST_def)
  unfolding get_conflict_wll_is_Nil_heur_def twl_st_heur_assn_def
    short_circuit_conv the_is_empty_def[symmetric]
  by sepref

concrete_definition (in -) get_conflict_wll_is_Nil_code
   uses isasat_input_bounded_nempty.get_conflict_wll_is_Nil_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) get_conflict_wll_is_Nil_code_def

lemmas get_conflict_wll_is_Nil_code[sepref_fr_rules] =
  get_conflict_wll_is_Nil_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

lemma get_conflict_wll_is_Nil_code_get_conflict_wll_is_Nil[sepref_fr_rules]:
  \<open>(get_conflict_wll_is_Nil_code, get_conflict_wll_is_Nil) \<in> twl_st_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  using get_conflict_wll_is_Nil_code[FCOMP get_conflict_wll_is_Nil_heur_get_conflict_wll_is_Nil]
  unfolding twl_st_assn_def[symmetric] .

lemma get_conflict_wll_is_Nil_code_get_conflict_wl_is_Nil[sepref_fr_rules]:
  \<open>(get_conflict_wll_is_Nil_code, RETURN \<circ> get_conflict_wl_is_Nil) \<in> twl_st_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  using get_conflict_wll_is_Nil_code_get_conflict_wll_is_Nil[FCOMP
   get_conflict_wll_is_Nil_get_conflict_wl_is_Nil[unfolded PR_CONST_def]]
  by auto

definition (in -) get_count_max_lvls_code where
  \<open>get_count_max_lvls_code = (\<lambda>(_, _, _, _, _, _, _, _, clvls, _). clvls)\<close>


lemma get_count_max_lvls_heur_hnr[sepref_fr_rules]:
  \<open>(return o get_count_max_lvls_code, RETURN o get_count_max_lvls_heur) \<in>
     twl_st_heur_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  apply sepref_to_hoare
  subgoal for x x'
    by (cases x; cases x')
     (sep_auto simp: twl_st_heur_assn_def get_count_max_lvls_code_def
        elim!: mod_starE)
  done

sepref_thm maximum_level_removed_eq_count_dec_code
  is \<open>uncurry (RETURN oo maximum_level_removed_eq_count_dec_heur)\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a twl_st_heur_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding maximum_level_removed_eq_count_dec_heur_def
  by sepref

concrete_definition (in -) maximum_level_removed_eq_count_dec_code
   uses isasat_input_bounded_nempty.maximum_level_removed_eq_count_dec_code.refine_raw
   is \<open>(uncurry ?f,_)\<in>_\<close>

prepare_code_thms (in -) maximum_level_removed_eq_count_dec_code_def

lemmas maximum_level_removed_eq_count_dec_code_hnr[sepref_fr_rules] =
   maximum_level_removed_eq_count_dec_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]


sepref_thm is_decided_hd_trail_wl_code
  is \<open>RETURN o is_decided_hd_trail_wl_heur\<close>
  :: \<open>[\<lambda>S. get_trail_wl_heur S \<noteq> []]\<^sub>a twl_st_heur_assn\<^sup>k \<rightarrow> bool_assn\<close>
  unfolding is_decided_hd_trail_wl_heur_def twl_st_heur_assn_def
    supply get_trail_wl_heur_def[simp]
  by sepref


concrete_definition (in -) is_decided_hd_trail_wl_code
   uses isasat_input_bounded_nempty.is_decided_hd_trail_wl_code.refine_raw
   is \<open>(?f, _) \<in> _\<close>

prepare_code_thms is_decided_hd_trail_wl_code_def

lemmas is_decided_hd_trail_wl_code[sepref_fr_rules] =
   is_decided_hd_trail_wl_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]


sepref_thm lit_and_ann_of_propagated_st_heur_code
  is \<open>RETURN o lit_and_ann_of_propagated_st_heur\<close>
  :: \<open>[\<lambda>S. is_proped (hd (get_trail_wl_heur S)) \<and> get_trail_wl_heur S \<noteq> []]\<^sub>a
       twl_st_heur_assn\<^sup>k \<rightarrow> (unat_lit_assn *a nat_assn)\<close>
  supply [[goals_limit=1]]
  supply get_trail_wl_heur_def[simp]
  unfolding lit_and_ann_of_propagated_st_heur_def twl_st_heur_assn_def
  by sepref

concrete_definition (in -) lit_and_ann_of_propagated_st_heur_code
   uses isasat_input_bounded_nempty.lit_and_ann_of_propagated_st_heur_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) lit_and_ann_of_propagated_st_heur_code_def

lemmas lit_and_ann_of_propagated_st_heur_code_refine[sepref_fr_rules] =
   lit_and_ann_of_propagated_st_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

end


setup \<open>map_theory_claset (fn ctxt => ctxt addSbefore ("split_all_tac", split_all_tac))\<close>

context isasat_input_bounded_nempty
begin


sepref_thm tl_state_wl_heur_code
  is \<open>RETURN o tl_state_wl_heur\<close>
  :: \<open>[\<lambda>(M, N, U, D, WS, Q, ((A, m, fst_As, lst_As, next_search), _), \<phi>, _). M \<noteq> [] \<and>
         atm_of (lit_of (hd M)) < length \<phi> \<and>
         atm_of (lit_of (hd M)) < length A \<and> (next_search \<noteq> None \<longrightarrow>  the next_search < length A)]\<^sub>a
      twl_st_heur_assn\<^sup>d \<rightarrow> twl_st_heur_assn\<close>
  supply [[goals_limit=1]] option.splits[split] if_splits[split]
  option.splits[split]
  supply [[goals_limit=1]] option.splits[split] literals_are_\<L>\<^sub>i\<^sub>n_hd_trail_in_D\<^sub>0[intro]
  unfolding tl_state_wl_heur_alt_def[abs_def] twl_st_heur_assn_def get_trail_wl_heur_def[simp]
    vmtf_unset_def bind_ref_tag_def[simp]
    short_circuit_conv
  by sepref


concrete_definition (in -) tl_state_wl_heur_code
  uses isasat_input_bounded_nempty.tl_state_wl_heur_code.refine_raw
  is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) tl_state_wl_heur_code_def

lemmas tl_state_wl_heur_code_refine[sepref_fr_rules] =
   tl_state_wl_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]


sepref_thm conflict_remove1_code
  is \<open>uncurry (RETURN oo lookup_conflict_remove1)\<close>
  :: \<open>[\<lambda>(L, (n,xs)). n > 0 \<and> atm_of L < length xs]\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a lookup_clause_rel_assn\<^sup>d \<rightarrow>
     lookup_clause_rel_assn\<close>
  supply [[goals_limit=2]] one_uint32_nat[sepref_fr_rules]
  unfolding lookup_conflict_remove1_def one_uint32_nat_def[symmetric] fast_minus_def[symmetric]
  by sepref

concrete_definition (in -) conflict_remove1_code
  uses isasat_input_bounded_nempty.conflict_remove1_code.refine_raw
  is \<open>(uncurry ?f,_)\<in>_\<close>

prepare_code_thms (in -) conflict_remove1_code_def

lemmas conflict_remove1_code_refine[sepref_fr_rules] =
   conflict_remove1_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

lemma conflict_remove1_code_op_nset_delete[sepref_fr_rules]:
  \<open>(uncurry conflict_remove1_code, uncurry (RETURN \<circ>\<circ> op_mset_delete))
    \<in> [\<lambda>(L, C). L \<in> snd ` D\<^sub>0 \<and> L \<in># C \<and> -L \<notin># C]\<^sub>a
       unat_lit_assn\<^sup>k *\<^sub>a lookup_clause_assn\<^sup>d \<rightarrow> lookup_clause_assn\<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c \<in>
    [comp_PRE (Id \<times>\<^sub>f lookup_clause_rel) (\<lambda>(L, C). L \<in># C \<and> - L \<notin># C \<and> L \<in> snd ` D\<^sub>0)
              (\<lambda>_ (L, n, xs). 0 < n \<and> atm_of L < length xs)
              (\<lambda>_. True)]\<^sub>a
    hrp_comp (unat_lit_assn\<^sup>k *\<^sub>a lookup_clause_rel_assn\<^sup>d) (Id \<times>\<^sub>f lookup_clause_rel) \<rightarrow>
    hr_comp lookup_clause_rel_assn lookup_clause_rel\<close>
      (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using  hfref_compI_PRE_aux[OF conflict_remove1_code_refine lookup_conflict_remove1]
    unfolding op_mset_delete_def
    .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that neq0_conv
    unfolding comp_PRE_def option_lookup_clause_rel_def lookup_clause_rel_def
    by (fastforce simp: image_image twl_st_heur_def phase_saving_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
      vmtf_def)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep lookup_clause_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def hr_comp_prod_conv
      lookup_clause_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed

lemma option_lookup_clause_assn_the[sepref_fr_rules]:
  \<open>(return o snd, RETURN o the) \<in> [\<lambda>C. C \<noteq> None]\<^sub>a option_lookup_clause_assn\<^sup>d \<rightarrow> lookup_clause_assn\<close>
  by sepref_to_hoare
     (sep_auto simp: lookup_clause_assn_def option_lookup_clause_assn_def lookup_clause_rel_def hr_comp_def
    option_lookup_clause_rel_def)

lemma option_lookup_clause_assn_Some[sepref_fr_rules]:
  \<open>(return o (\<lambda>C. (False, C)), RETURN o Some) \<in> lookup_clause_assn\<^sup>d \<rightarrow>\<^sub>a option_lookup_clause_assn\<close>
  by sepref_to_hoare
     (sep_auto simp: lookup_clause_assn_def option_lookup_clause_assn_def lookup_clause_rel_def hr_comp_def
    option_lookup_clause_rel_def bool_assn_alt_def)


lemma lookup_clause_assn_op_nset_is_emty[sepref_fr_rules]:
  \<open>(return o (\<lambda>(n, _). n = 0), RETURN o op_mset_is_empty) \<in> lookup_clause_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  apply sepref_to_hoare
  apply (rename_tac x xi, case_tac xi)
  by (sep_auto simp: lookup_clause_assn_def lookup_clause_rel_def hr_comp_def
    uint32_nat_assn_0_eq uint32_nat_rel_def br_def pure_def nat_of_uint32_0_iff)+


sepref_thm update_confl_tl_wl_code
  is \<open>uncurry2 update_confl_tl_wl_heur\<close>
  :: \<open>[\<lambda>((i, L), (M, N, U, D, W, Q, ((A, m, fst_As, lst_As, next_search), _), \<phi>, clvls, cach)).
      (i > 0 \<longrightarrow> distinct (N ! i)) \<and>
      (i > 0 \<longrightarrow> literals_are_in_\<L>\<^sub>i\<^sub>n (mset (N! i))) \<and>
      (i > 0 \<longrightarrow> \<not> tautology (mset (N ! i))) \<and>
      i < length N \<and> \<not> tautology (the D) \<and>
      literals_are_in_\<L>\<^sub>i\<^sub>n (the D) \<and> D \<noteq> None \<and>
      M \<noteq> [] \<and>
      L \<in> snd ` D\<^sub>0 \<and> -L \<in># the D \<and> L \<notin># the D \<and>
      (i > 0 \<longrightarrow> (L \<in> set (N ! i) \<and> -L \<notin> set (N ! i))) \<and>
      (i > 0 \<longrightarrow> (\<forall>L \<in> set (tl (N ! i)). - L \<notin># the D)) \<and>
      (i > 0 \<longrightarrow> card_max_lvl M (mset (tl (N ! i)) \<union># the D) \<ge> 1) \<and>
      atm_of (lit_of (hd M)) < length \<phi> \<and>
      atm_of (lit_of (hd M)) < length A \<and> (next_search \<noteq> None \<longrightarrow>  the next_search < length A) \<and>
      L = lit_of (hd M) \<and>
      clvls = card_max_lvl M (the D) \<and>
      literals_are_in_\<L>\<^sub>i\<^sub>n_trail M \<and>
      no_dup M
         ]\<^sub>a
  nat_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a twl_st_heur_assn\<^sup>d \<rightarrow> bool_assn *a twl_st_heur_assn\<close>
  supply image_image[simp] uminus_\<A>\<^sub>i\<^sub>n_iff[iff] in_diffD[dest] option.splits[split]
  supply [[goals_limit=1]]
  unfolding update_confl_tl_wl_heur_def twl_st_heur_assn_def save_phase_def
  supply merge_conflict_m_def[simp]
  by sepref (* slow *)

concrete_definition (in -) update_confl_tl_wl_code
  uses isasat_input_bounded_nempty.update_confl_tl_wl_code.refine_raw
  is \<open>(uncurry2 ?f,_)\<in>_\<close>

prepare_code_thms (in -) update_confl_tl_wl_code_def

lemmas update_confl_tl_wl_code_refine[sepref_fr_rules] =
   update_confl_tl_wl_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]
(* 
lemma update_confl_tl_wl_code_update_confl_tl_wl[sepref_fr_rules]:
  \<open>(uncurry2 update_confl_tl_wl_code, uncurry2 (RETURN ooo update_confl_tl_wl))
    \<in> [\<lambda>((C, L), S). twl_struct_invs (twl_st_of_wl None S) \<and>
        twl_stgy_invs (twl_st_of_wl None S) \<and>
        get_conflict_wl S \<noteq> None \<and>
        get_trail_wl S \<noteq> [] \<and>
        - L \<in># the (get_conflict_wl S) \<and>
        (L, C) = lit_and_ann_of_propagated_st S \<and>
        literals_are_\<L>\<^sub>i\<^sub>n S \<and>
        is_proped (hd (get_trail_wl S)) \<and>
        twl_list_invs (st_l_of_wl None S)]\<^sub>a
       nat_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a twl_st_assn\<^sup>d \<rightarrow> bool_assn *a twl_st_assn\<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c \<in>  [comp_PRE (nat_rel \<times>\<^sub>f nat_lit_lit_rel \<times>\<^sub>f twl_st_heur)
     (\<lambda>((C, L), S).
         twl_struct_invs (twl_st_of_wl None S) \<and>
         twl_stgy_invs (twl_st_of_wl None S) \<and>
         twl_list_invs (st_l_of_wl None S) \<and>
         C < length (get_clauses_wl S) \<and>
         get_conflict_wl S \<noteq> None \<and>
         get_trail_wl S \<noteq> [] \<and>
         - L \<in># the (get_conflict_wl S) \<and>
         (L, C) =
         lit_and_ann_of_propagated (hd (get_trail_wl S)) \<and>
         L \<in> snd ` D\<^sub>0 \<and> is_proped (hd (get_trail_wl S)))
     (\<lambda>_ ((i, L), M, N, U, D, W, Q, ((A, m, fst_As, lst_As,
         next_search), _), \<phi>, clvls, cach).
         (0 < i \<longrightarrow> distinct (N ! i)) \<and>
         (0 < i \<longrightarrow> literals_are_in_\<L>\<^sub>i\<^sub>n (mset (N ! i))) \<and>
         (0 < i \<longrightarrow> \<not> tautology (mset (N ! i))) \<and>
         i < length N \<and>
         \<not> tautology (the D) \<and>
         literals_are_in_\<L>\<^sub>i\<^sub>n (the D) \<and>
         D \<noteq> None \<and>
         M \<noteq> [] \<and>
         L \<in> snd ` D\<^sub>0 \<and>
         - L \<in># the D \<and>
         L \<notin># the D \<and>
         (0 < i \<longrightarrow> L \<in> set (N ! i) \<and> - L \<notin> set (N ! i)) \<and>
         (0 < i \<longrightarrow> (\<forall>L\<in>set (tl (N ! i)). - L \<notin># the D)) \<and>
         (0 < i \<longrightarrow>
          1 \<le> card_max_lvl M (mset (tl (N ! i)) \<union># the D)) \<and>
         atm_of (lit_of (hd M)) < length \<phi> \<and>
         atm_of (lit_of (hd M)) < length A \<and>
         (next_search \<noteq> None \<longrightarrow> the next_search < length A) \<and>
         L = lit_of (hd M) \<and>
         clvls = card_max_lvl M (the D) \<and>
         literals_are_in_\<L>\<^sub>i\<^sub>n_trail M \<and> no_dup M)
     (\<lambda>_. True)]\<^sub>a hrp_comp
                     (nat_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a
                      twl_st_heur_assn\<^sup>d)
                     (nat_rel \<times>\<^sub>f nat_lit_lit_rel \<times>\<^sub>f
                      twl_st_heur) \<rightarrow> hr_comp
      (bool_assn *a twl_st_heur_assn) (bool_rel \<times>\<^sub>f twl_st_heur)\<close>
      (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF update_confl_tl_wl_code_refine
       update_confl_tl_wl_heur_update_confl_tl_wl]
    .
  have pre: \<open>?pre' x\<close> (is \<open>comp_PRE ?rel ?\<Phi> ?\<Psi> _ x\<close>) if pre: \<open>?pre x\<close> for x
  unfolding comp_PRE_def
  proof (intro allI impI conjI)
    obtain C L S where
      [simp]: \<open>x = ((C,L), S)\<close>
      by (cases x) auto
    obtain M N U D W Q NE UE where
      [simp]: \<open>S = (M, N, U, D, NE, UE, W, Q)\<close>
      by (cases S) auto
    have LC: \<open>(L, C) = lit_and_ann_of_propagated (hd (get_trail_wl S))\<close> and
      lits_\<A>\<^sub>i\<^sub>n: \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close> and
      struct_invs: \<open>twl_struct_invs (twl_st_of None (st_l_of_wl None S))\<close> and
      list_invs: \<open>twl_list_invs (st_l_of_wl None S)\<close> and
      trail_nempty: \<open>get_trail_wl S \<noteq> []\<close> and
      add_invs: \<open>twl_list_invs (st_l_of_wl None S)\<close> and
      proped: \<open>is_proped (hd (get_trail_wl S))\<close> and
      confl: \<open>get_conflict_wl S \<noteq> None\<close> and
      L_confl: \<open>-L \<in># the(get_conflict_wl S)\<close>
      using that by (auto simp: lit_and_ann_of_propagated_st_def)
    have lits_D: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (the (get_conflict_wl S))\<close>
      by (rule literals_are_\<L>\<^sub>i\<^sub>n_conflict_literals_are_in_\<L>\<^sub>i\<^sub>n[of _ None])
       (use lits_\<A>\<^sub>i\<^sub>n confl struct_invs in auto)
    have C_le: \<open>C < length (get_clauses_wl S)\<close>
      using trail_nempty LC proped add_invs trail_nempty unfolding twl_list_invs_def
      by (cases M; cases \<open>hd M\<close>) auto
    moreover have L_D\<^sub>0: \<open>L \<in> snd ` D\<^sub>0\<close>
      using L_confl confl lits_D
      by (cases \<open>get_conflict_wl S\<close>)
        (auto simp: image_image literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset uminus_\<A>\<^sub>i\<^sub>n_iff
            dest: multi_member_split)
    ultimately show \<open>?\<Phi> x\<close>
      using that by (auto simp: lit_and_ann_of_propagated_st_def)
    have
      trail: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail( get_trail_wl S)\<close>
      using literals_are_\<L>\<^sub>i\<^sub>n_literals_are_in_\<L>\<^sub>i\<^sub>n_trail[OF lits_\<A>\<^sub>i\<^sub>n, of None ] struct_invs
      by auto

    fix x'
    assume x'x: \<open>(x', x) \<in> nat_rel \<times>\<^sub>f Id \<times>\<^sub>f twl_st_heur\<close>
    then obtain S' where
      [simp]: \<open>x' = ((C, L), S')\<close>
      by (cases x') auto
    obtain Q' A m fst_As lst_As next_search oth \<phi> clvls cach where
      [simp]: \<open>S' = (M, N, U, D, W, Q', ((A, m, fst_As, lst_As, next_search), oth), \<phi>, clvls, cach)\<close> and
      n_d: \<open>no_dup (get_trail_wl S)\<close>
      using x'x by (cases S') (auto simp: twl_st_heur_def)
    have in_atms_le: \<open>\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length A\<close> and \<phi>: \<open>phase_saving \<phi>\<close> and
      vmtf: \<open>\<exists>xs' ys'. vmtf_ns (ys' @ xs') m A \<and> fst_As = hd (ys' @ xs') \<and>
           lst_As = last (ys' @ xs') \<and> next_search = option_hd xs'\<close> and
      clvls: \<open>clvls \<in> counts_maximum_level M D\<close>
      using x'x unfolding twl_st_heur_def vmtf_def by auto
    then have atm_L_le_A: \<open>atm_of L < length A\<close>
      using L_D\<^sub>0 by (auto simp: image_image in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)
    have atm_L_le_\<phi>: \<open>atm_of L < length \<phi>\<close>
      using L_D\<^sub>0 \<phi> unfolding phase_saving_def by (auto simp: image_image in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)
    obtain xs' ys' where
      \<open>vmtf_ns (ys' @ xs') m A\<close> and \<open>fst_As = hd (ys' @ xs')\<close> and \<open>next_search = option_hd xs'\<close> and
      \<open>lst_As = last (ys' @ xs')\<close>
      using vmtf by blast
    then have next_search: \<open>the next_search < length A\<close> if \<open>next_search \<noteq> None\<close>
      apply - by (rule vmtf_ns_le_length[of \<open>ys' @ xs'\<close> m A]) (use that in auto)
    have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of (twl_st_of None (st_l_of_wl None S)))\<close>
      using struct_invs unfolding twl_struct_invs_def by fast
    then have \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of (twl_st_of None (st_l_of_wl None S)))\<close>
      unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def by fast+
    then have \<open>distinct_mset_set (mset ` set (tl N))\<close>
      apply (subst append_take_drop_id[of U, symmetric])
      unfolding set_append image_Un
      by (auto simp: cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def mset_take_mset_drop_mset drop_Suc)
    then have dist_NC: \<open>distinct (N ! C)\<close> if \<open>C > 0\<close>
      using that C_le nth_in_set_tl[of C N] by (auto simp: distinct_mset_set_def)

    have lits_NC: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset (N ! C))\<close> if \<open>C > 0\<close>
      by (rule literals_are_in_\<L>\<^sub>i\<^sub>n_nth) (use C_le that lits_\<A>\<^sub>i\<^sub>n in auto)
    have L_hd_M: \<open>L = lit_of (hd M)\<close>
      by (cases M; cases \<open>hd M\<close>) (use trail_nempty LC proped in auto)

    have tauto_confl: \<open>\<not> tautology (the (get_conflict_wl S))\<close>
      using resolve_cls_wl'_not_tauto_confl[of S C L] struct_invs confl L_confl C_le trail_nempty
      proped LC list_invs by auto
    have L_notin_D: \<open>L \<notin># the D\<close>
      using resolve_cls_wl'_not_tauto_confl[of S C L] struct_invs confl L_confl C_le trail_nempty
      proped LC list_invs by auto
    have tauto: \<open>\<not>tautology (mset (N ! C))\<close> if \<open>C > 0\<close>
      using resolve_cls_wl'_not_tauto_cls[of S C L] struct_invs confl L_confl C_le trail_nempty
      proped LC that list_invs
      by auto
    have L_NC: \<open>L \<in> set (N ! C)\<close> if \<open>C > 0\<close>
      using resolve_cls_wl'_L_in_cls[of S C L] struct_invs confl L_confl C_le trail_nempty
      proped LC that list_invs by auto
    have L_NC': \<open>-L \<notin> set (N ! C)\<close> if \<open>C > 0\<close>
      using tauto that L_NC apply (auto simp: tautology_decomp)
      by (metis (full_types) nat_of_lit.cases uminus_Pos uminus_of_uminus_id)
    have [simp]: \<open>Suc 0 \<le> card_max_lvl M (mset (tl (N ! C)) \<union># the D)\<close>
      if \<open>C > 0\<close>
      using resolve_cls_wl'_card_max_lvl[of S C L] LC confl C_le L_D\<^sub>0 clvls that pre
      by (auto simp: counts_maximum_level_def)
    have \<open>C > 0 \<Longrightarrow> La \<in> set (tl (N ! C)) \<Longrightarrow> - La \<in># the D \<Longrightarrow> False\<close> for La
      using resolve_helper_seperated[of S C L] struct_invs confl L_confl C_le trail_nempty
      proped LC that list_invs
      by auto
    then show \<open>?\<Psi> x x'\<close>
      using confl L_confl dist_NC lits_NC C_le trail_nempty L_D\<^sub>0 tauto lits_D L_notin_D L_NC
      atm_L_le_A atm_L_le_\<phi> next_search clvls tauto_confl
      trail n_d
      by (auto simp: L_hd_M[symmetric] counts_maximum_level_def)
  qed
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def hr_comp_prod_conv
      lookup_clause_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed
 *)

end


setup \<open>map_theory_claset (fn ctxt => ctxt delSWrapper ("split_all_tac"))\<close>

context isasat_input_bounded_nempty
begin

sepref_register skip_and_resolve_loop_wl_D is_in_conflict_st
sepref_thm skip_and_resolve_loop_wl_D
  is \<open>PR_CONST skip_and_resolve_loop_wl_D\<close>
  :: \<open>twl_st_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_assn\<close>
  supply [[goals_limit=1]] get_trail_twl_st_of_wl_get_trail_wl_empty_iff[simp]
    is_decided_hd_trail_wl_def[simp]
    is_decided_no_proped_iff[simp] skip_and_resolve_hd_in_D\<^sub>0[intro]
    literals_are_\<L>\<^sub>i\<^sub>n_conflict_literals_are_in_\<L>\<^sub>i\<^sub>n[of _ None, intro]
    get_conflict_l_st_l_of_wl[simp] is_in_conflict_st_def[simp]  neq_NilE[elim!]
    annotated_lit.splits[split] lit_and_ann_of_propagated_st_def[simp]
    annotated_lit.disc_eq_case(2)[simp]
    skip_and_resolde_hd_D\<^sub>0[simp]
    not_None_eq[simp del] maximum_level_removed_eq_count_dec_def[simp]
  apply (subst PR_CONST_def)
  unfolding skip_and_resolve_loop_wl_D_def
  apply (rewrite at \<open>\<not>_ \<and> \<not> _\<close> short_circuit_conv)
  apply (rewrite at \<open>let _ = the _ in _\<close> Let_def)
  unfolding
    maximum_level_removed_eq_count_dec_def[unfolded get_maximum_level_remove_def, symmetric]
  unfolding
    literals_to_update_wl_literals_to_update_wl_empty
    get_conflict_wl.simps get_trail_wl.simps
    maximum_level_removed_eq_count_dec_def[symmetric]
    is_decided_hd_trail_wl_def[symmetric]
    skip_and_resolve_loop_inv_def
    Multiset.is_empty_def[symmetric]
    get_maximum_level_remove_def[symmetric]
    is_in_conflict_st_def[symmetric]
    lit_and_ann_of_propagated_st_def[symmetric]
    get_max_lvl_st_def[symmetric]
    count_decided_st_alt_def[symmetric]
    get_conflict_wl_get_conflict_wl_is_Nil
    is_in_conflict_def[symmetric]
  by sepref (* slow *)

concrete_definition (in -) skip_and_resolve_loop_wl_D_code
  uses isasat_input_bounded_nempty.skip_and_resolve_loop_wl_D.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) skip_and_resolve_loop_wl_D_code_def

lemmas skip_and_resolve_loop_wl_D_code_refine[sepref_fr_rules] =
   skip_and_resolve_loop_wl_D_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]
end

setup \<open>map_theory_claset (fn ctxt => ctxt addSbefore ("split_all_tac", split_all_tac))\<close>

end