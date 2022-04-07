theory IsaSAT_Inprocessing_LLVM
  imports IsaSAT_Setup_LLVM IsaSAT_Trail_LLVM
    IsaSAT_Restart_Inprocessing
begin

sepref_register 0 1

sepref_register mop_arena_update_lit

sepref_def isa_simplify_clause_with_unit2_code
  is \<open>uncurry2 isa_simplify_clause_with_unit2\<close>
  :: \<open>[\<lambda>((_, _), N). length (N) \<le> sint64_max]\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a trail_pol_fast_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>d \<rightarrow>
  bool1_assn \<times>\<^sub>a arena_fast_assn \<times>\<^sub>a unat_lit_assn \<times>\<^sub>a  bool1_assn \<times>\<^sub>a uint32_nat_assn\<close>
  unfolding isa_simplify_clause_with_unit2_def
    length_avdom_def[symmetric] Suc_eq_plus1[symmetric]
    mop_arena_status_st_def[symmetric] isasat_bounded_assn_def
    SET_TRUE_def[symmetric] SET_FALSE_def[symmetric]
    tri_bool_eq_def[symmetric]
  apply (rewrite at \<open>(\<hole>, _, _)\<close> unat_const_fold[where 'a=32])
  apply (rewrite at \<open>(_ \<le> \<hole>)\<close> unat_const_fold[where 'a=32])

  apply (annot_snat_const \<open>TYPE(64)\<close>)
  apply (rewrite at \<open>mop_arena_update_lit _ \<hole>\<close> annot_unat_snat_upcast[where 'l=64])
  apply (rewrite at \<open>If (\<hole> = _)\<close> annot_unat_snat_upcast[where 'l=64])
  supply [[goals_limit=1]]
  by sepref

sepref_register cons_trail_Propagated_tr set_conflict_to_false

lemma set_conflict_to_false_alt_def:
  \<open>RETURN o set_conflict_to_false = (\<lambda>(b, n, xs). RETURN (False, 0, xs))\<close>
  unfolding set_conflict_to_false_def by auto

sepref_def set_conflict_to_false_code
  is \<open>RETURN o set_conflict_to_false\<close>
  :: \<open>conflict_option_rel_assn\<^sup>d \<rightarrow>\<^sub>a conflict_option_rel_assn\<close>
  unfolding set_conflict_to_false_alt_def conflict_option_rel_assn_def
    lookup_clause_rel_assn_def
  apply (annot_unat_const \<open>TYPE(32)\<close>)
  supply [[goals_limit=1]]
  by sepref

lemma isa_simplify_clause_with_unit_st2_alt_def:
  \<open>isa_simplify_clause_with_unit_st2 =  (\<lambda>C S\<^sub>0. do {
  let (lcount, S) = extract_lcount_wl_heur S\<^sub>0; let (N, S) = extract_arena_wl_heur S; let (M, S) = extract_trail_wl_heur S;
  ASSERT (N = get_clauses_wl_heur S\<^sub>0 \<and> lcount = get_learned_count S\<^sub>0 \<and> M = get_trail_wl_heur S\<^sub>0);
  E \<leftarrow> mop_arena_status N C;
   ASSERT(E = LEARNED \<longrightarrow> 1 \<le> clss_size_lcount lcount);
  (unc, N, L, b, i) \<leftarrow> isa_simplify_clause_with_unit2 C M N;
   if unc then RETURN (update_arena_wl_heur N (update_trail_wl_heur M (update_lcount_wl_heur lcount S)))
   else if b then
   let (stats, S) = extract_stats_wl_heur S in
   RETURN  (update_trail_wl_heur M
     (update_arena_wl_heur N
     (update_stats_wl_heur (if E=LEARNED then stats else decr_irred_clss (stats))
     (update_lcount_wl_heur (if E = LEARNED then clss_size_decr_lcount (lcount) else lcount)
     S))))
   else if i = 1
   then do {
     M \<leftarrow> cons_trail_Propagated_tr L 0 M;
    let (stats, S) = extract_stats_wl_heur S;
     RETURN (update_arena_wl_heur N
     (update_trail_wl_heur M
     (update_stats_wl_heur (if E=LEARNED then incr_uset stats else incr_uset (decr_irred_clss stats))
     (update_lcount_wl_heur (if E = LEARNED then clss_size_decr_lcount (clss_size_incr_lcountUEk lcount) else lcount)
     S)))) }
   else if i = 0
   then do {
     j \<leftarrow> mop_isa_length_trail M;
     let (stats, S) = extract_stats_wl_heur S; let (confl, S) = extract_conflict_wl_heur S;
     RETURN (update_trail_wl_heur M
     (update_arena_wl_heur N
     (update_conflict_wl_heur (set_conflict_to_false confl)
     (update_clvls_wl_heur 0
     (update_literals_to_update_wl_heur j
     (update_stats_wl_heur (if E=LEARNED then stats else decr_irred_clss stats)
     (update_lcount_wl_heur (if E = LEARNED then clss_size_decr_lcount lcount else lcount)
     S)))))))
   }
   else
     RETURN (update_trail_wl_heur M
     (update_lcount_wl_heur lcount
     (update_arena_wl_heur N
     S)))
     })\<close>
     unfolding isa_simplify_clause_with_unit_st2_def
     by (auto simp: state_extractors  split: isasat_int.splits intro!: ext bind_cong[OF refl])

sepref_def isa_simplify_clause_with_unit_st2_code
  is \<open>uncurry isa_simplify_clause_with_unit_st2\<close>
  :: \<open>[\<lambda>(_, S). length (get_clauses_wl_heur S) \<le> sint64_max \<and> learned_clss_count S \<le> uint64_max]\<^sub>a
  sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [simp] = learned_clss_count_def
  unfolding isa_simplify_clause_with_unit_st2_alt_def
    length_avdom_def[symmetric] Suc_eq_plus1[symmetric]
    mop_arena_status_st_def[symmetric]
    fold_tuple_optimizations
  apply (rewrite at \<open>(cons_trail_Propagated_tr _ \<hole>)\<close> snat_const_fold[where 'a=64])
  apply (annot_unat_const \<open>TYPE(32)\<close>)
  supply [[goals_limit=1]]
  by sepref

lemma isa_simplify_clauses_with_unit_st2_alt_def:
  \<open>isa_simplify_clauses_with_unit_st2 S =
  do {
    ASSERT(length (get_avdom S)+length (get_ivdom S) \<le> length (get_vdom S) \<and>
      length (get_vdom S) \<le> length (get_clauses_wl_heur S));
    let m = length (get_avdom S);
    let n = length (get_ivdom S);
    let mn = m+n;
    (_, T) \<leftarrow> WHILE\<^sub>T
      (\<lambda>(i, T). i < mn \<and> get_conflict_wl_is_None_heur T)
      (\<lambda>(i,T). do {
           ASSERT((i < length (get_avdom T) \<longrightarrow> access_avdom_at_pre T i) \<and>
           (i \<ge> length (get_avdom T) \<longrightarrow> access_ivdom_at_pre T (i - length_avdom S)) \<and>
           length_avdom T = length_avdom S \<and>
           length (get_clauses_wl_heur T) = length (get_clauses_wl_heur S) \<and>
            learned_clss_count T \<le> learned_clss_count S);
          let C = (if i < m then access_avdom_at T i else access_ivdom_at T (i - m));
          E \<leftarrow> mop_arena_status (get_clauses_wl_heur T) C;
          if E \<noteq> DELETED then do {
          T \<leftarrow> isa_simplify_clause_with_unit_st2 C T;
          ASSERT(i < length (get_avdom S)+length (get_ivdom S));
          RETURN (i+1, T)
        }
        else do {ASSERT(i < length (get_avdom S)+length (get_ivdom S)); RETURN (i+1,T)}
      })
     (0, S);
    RETURN (reset_units_since_last_GC_st T)
  }\<close>
   unfolding isa_simplify_clauses_with_unit_st2_def bind_to_let_conv Let_def length_avdom_def
  by (auto cong: if_cong intro!: bind_cong[OF refl])

sepref_register length_ivdom access_ivdom_at

sepref_register isa_simplify_clauses_with_unit_st2
sepref_def isa_simplify_clauses_with_unit_st2_code
  is isa_simplify_clauses_with_unit_st2
  :: \<open>[\<lambda>S. length (get_clauses_wl_heur S) \<le> sint64_max \<and> learned_clss_count S \<le> uint64_max]\<^sub>a
     isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  unfolding isa_simplify_clauses_with_unit_st2_alt_def
    length_avdom_def[symmetric] Suc_eq_plus1[symmetric] length_ivdom_def[symmetric]
    mop_arena_status_st_def[symmetric]
   apply (annot_snat_const \<open>TYPE(64)\<close>)
   supply [[goals_limit=1]]
  by sepref

sepref_def isa_simplify_clauses_with_unit_st_wl2_code
  is isa_simplify_clauses_with_unit_st_wl2
  :: \<open>[\<lambda>S. length (get_clauses_wl_heur S) \<le> sint64_max \<and> learned_clss_count S \<le> uint64_max]\<^sub>a
     isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  unfolding isa_simplify_clauses_with_unit_st_wl2_def
  supply [[goals_limit=1]]
  by sepref


sepref_def isa_simplify_clauses_with_units_st_wl2_code
  is isa_simplify_clauses_with_units_st_wl2
  :: \<open>[\<lambda>S. length (get_clauses_wl_heur S) \<le> sint64_max \<and> learned_clss_count S \<le> uint64_max]\<^sub>a
     isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  unfolding isa_simplify_clauses_with_units_st_wl2_def
  supply [[goals_limit=1]]
  by sepref

find_theorems ahm_create create
sepref_def ahm_create_code
  is \<open>ahm_create\<close>
  :: \<open>(snat_assn' TYPE(64))\<^sup>k \<rightarrow>\<^sub>a larray64_assn (sint_assn' TYPE(64))\<close>
  unfolding ahm_create_def larray_fold_custom_replicate
  apply (annot_sint_const \<open>TYPE(64)\<close>)
  by sepref

definition encoded_irred_indices where
  \<open>encoded_irred_indices = {(a, b::nat \<times> bool). a \<le> int sint64_max \<and> -a \<le> int sint64_max \<and> (snd b \<longleftrightarrow> a > 0) \<and> fst b = (if a < 0 then nat (-a) else nat a) \<and> fst b \<noteq> 0}\<close>

sepref_def ahm_is_marked_code
  is \<open>uncurry ahm_is_marked\<close>
  :: \<open>(larray64_assn (sint_assn' TYPE(64)))\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding ahm_is_marked_def
  apply (annot_sint_const \<open>TYPE(64)\<close>)
  by sepref


lemma ahm_is_marked_is_marked2:
   \<open>(uncurry ahm_is_marked, uncurry is_marked)
    \<in>  (array_hash_map_rel R) \<times>\<^sub>f nat_lit_lit_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel\<close>
  apply (subst fref_param1)
   using ahm_is_marked_is_marked
  unfolding ahm_is_marked_def is_marked_def uncurry_def
  apply (intro frefI nres_relI)
  apply refine_vcg
  apply (auto simp: array_hash_map_rel_def ahm_is_marked_def is_marked_def
    intro!: ASSERT_leI)[]
  apply simp
  by(auto simp: array_hash_map_rel_def ahm_is_marked_def is_marked_def
    intro!: ASSERT_leI)

lemma ahm_get_marked_get_marked:
   \<open>(uncurry ahm_get_marked, uncurry get_marked)
    \<in>  (array_hash_map_rel R) \<times>\<^sub>f nat_lit_lit_rel \<rightarrow> \<langle>R\<rangle>nres_rel\<close>
  unfolding ahm_get_marked_def get_marked_def uncurry_def
  apply refine_vcg
  apply (auto simp: array_hash_map_rel_def ahm_is_marked_def is_marked_def
    intro!: ASSERT_leI)[]
  apply clarsimp
  apply (auto simp: array_hash_map_rel_def ahm_is_marked_def is_marked_def
    intro!: ASSERT_leI)[]
  done

sepref_def ahm_get_marked_code
  is \<open>uncurry ahm_get_marked\<close>
  :: \<open>(larray64_assn (sint_assn' TYPE(64)))\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a sint_assn' TYPE(64)\<close>
  unfolding ahm_get_marked_def
  by sepref

sepref_def ahm_empty_code
  is \<open>ahm_empty\<close>
  :: \<open>(larray64_assn (sint_assn' TYPE(64)))\<^sup>d \<rightarrow>\<^sub>a larray64_assn (sint_assn' TYPE(64))\<close>
  unfolding ahm_empty_def
  apply (annot_sint_const \<open>TYPE(64)\<close>)
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

sepref_register empty
lemma ahm_empty_empty:
   \<open>(ahm_empty, empty) \<in> (array_hash_map_rel R) \<rightarrow> \<langle>array_hash_map_rel R\<rangle>nres_rel\<close>
  unfolding ahm_empty_def empty_def uncurry_def fref_param1
  apply (intro ext frefI nres_relI)
  subgoal for x y
    apply (refine_vcg WHILET_rule[where I = \<open>\<lambda>(i, CS). (\<forall>j<i. CS!j = 0) \<and> length CS = length x\<close> and R = \<open>measure (\<lambda>(i,_). length x -i)\<close>])
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: array_hash_map_rel_def)
    done
  done


sepref_def length_watchlist_full_impl
  is \<open>RETURN o length\<close>
  :: \<open>watchlist_fast_assn\<^sup>k \<rightarrow>\<^sub>a sint64_nat_assn\<close>
  unfolding op_list_list_len_def[symmetric]
  by sepref

definition encoded_irred_index_irred where
  \<open>encoded_irred_index_irred a = snd a\<close>

definition encoded_irred_index_irred_int where
  \<open>encoded_irred_index_irred_int a = (a > 0)\<close>

lemma encoded_irred_index_irred:
  \<open>(encoded_irred_index_irred_int, encoded_irred_index_irred) \<in> encoded_irred_indices \<rightarrow> bool_rel\<close>
  by (auto simp: encoded_irred_indices_def encoded_irred_index_irred_int_def
    encoded_irred_index_irred_def)

definition encoded_irred_index_get where
  \<open>encoded_irred_index_get a = fst a\<close>

definition encoded_irred_index_get_int where
  \<open>encoded_irred_index_get_int a = do {ASSERT (a \<le> int sint64_max \<and> -a \<le> int sint64_max); RETURN (if a > 0 then nat a else nat (-a))}\<close>

lemma encoded_irred_index_get:
  \<open>(encoded_irred_index_get_int, RETURN o encoded_irred_index_get) \<in> encoded_irred_indices \<rightarrow> \<langle>nat_rel\<rangle>nres_rel\<close>
  by (auto simp: encoded_irred_indices_def encoded_irred_index_get_int_def
    encoded_irred_index_get_def intro!: nres_relI)

sepref_def encoded_irred_index_irred_int_impl
  is \<open>RETURN o encoded_irred_index_irred_int\<close>
  :: \<open>(sint_assn' TYPE(64))\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding encoded_irred_index_irred_int_def
  apply (annot_sint_const \<open>TYPE(64)\<close>)
  by sepref

lemma nat_sint_snat: \<open>0 \<le> sint xi \<Longrightarrow> (nat (sint xi) = snat xi)\<close>
  by (auto simp: snat_def)

lemma [sepref_fr_rules]:
  \<open>(Mreturn, RETURN o nat) \<in> [\<lambda>a. a \<ge> 0]\<^sub>a (sint_assn' TYPE(64))\<^sup>k \<rightarrow> sint64_nat_assn\<close>
  apply sepref_to_hoare
  apply vcg
  apply (auto simp: sint_rel_def ENTAILS_def snat_rel_def snat.rel_def br_def sint.rel_def
    pure_true_conv Exists_eq_simp snat_invar_def word_msb_sint nat_sint_snat)
  done
lemma [sepref_fr_rules]:
  \<open>(Mreturn o (\<lambda>x. -x), RETURN o uminus) \<in> [\<lambda>a. a \<le> int sint64_max \<and> -a \<le> int sint64_max]\<^sub>a (sint_assn' TYPE(64))\<^sup>k \<rightarrow> (sint_assn' TYPE(64))\<close>
  apply sepref_to_hoare
  apply vcg
  subgoal for x xi asf s
    using sdiv_word_min'[of xi 1] sdiv_word_max'[of xi 1]
  apply (auto simp: sint_rel_def ENTAILS_def snat_rel_def snat.rel_def br_def sint.rel_def
    pure_true_conv Exists_eq_simp snat_invar_def word_msb_sint nat_sint_snat
    signed_arith_ineq_checks_to_eq word_size sint64_max_def word_size)
  apply (subst signed_arith_ineq_checks_to_eq[symmetric])
  apply (auto simp: word_size pure_true_conv)
  done
  done

sepref_def encoded_irred_index_irred_get_impl
  is \<open>encoded_irred_index_get_int\<close>
  :: \<open>(sint_assn' TYPE(64))\<^sup>k \<rightarrow>\<^sub>a sint64_nat_assn\<close>
  unfolding encoded_irred_index_get_int_def
  apply (annot_sint_const \<open>TYPE(64)\<close>)
  by sepref

lemmas [sepref_fr_rules] =
  encoded_irred_index_irred_get_impl.refine[FCOMP encoded_irred_index_get]
  encoded_irred_index_irred_int_impl.refine[FCOMP encoded_irred_index_irred]


definition encoded_irred_index_set where
  \<open>encoded_irred_index_set a b = (a::nat, b::bool)\<close>

definition encoded_irred_index_set_int where
  \<open>encoded_irred_index_set_int a b = do { (if b then RETURN (int a) else RETURN (- int a))}\<close>

no_notation WB_More_Refinement.fref (\<open>[_]\<^sub>f _ \<rightarrow> _\<close> [0,60,60] 60)

lemma encoded_irred_index_set:
  \<open>(uncurry encoded_irred_index_set_int, uncurry (RETURN oo encoded_irred_index_set)) \<in> [\<lambda>(a,b). a \<noteq> 0 \<and> a \<le> sint64_max]\<^sub>f nat_rel \<times>\<^sub>r bool_rel \<rightarrow> \<langle>encoded_irred_indices\<rangle>nres_rel\<close>
  by (clarsimp simp: encoded_irred_indices_def encoded_irred_index_set_int_def
    encoded_irred_index_set_def  intro!: nres_relI frefI)


lemma int_snat_sint: \<open>\<not> sint xi < 0 \<Longrightarrow> int (snat (xi::64 word)) = sint xi\<close>
  by (auto simp: snat_def)

lemma [sepref_fr_rules]:
  \<open>(Mreturn, RETURN o int) \<in> (snat_assn' TYPE(64))\<^sup>k \<rightarrow>\<^sub>a (sint_assn' TYPE(64))\<close>
  apply sepref_to_hoare
  apply vcg
  apply (auto simp: sint_rel_def ENTAILS_def snat_rel_def snat.rel_def br_def sint.rel_def
    pure_true_conv Exists_eq_simp snat_invar_def word_msb_sint nat_sint_snat int_snat_sint)
  done

sepref_register "uminus :: int \<Rightarrow> int" int
lemma encoded_irred_index_set_int_alt_def:
  \<open>encoded_irred_index_set_int a b = do { (if b then RETURN (int a) else RETURN (0 - int a))}\<close>
  by (auto simp: encoded_irred_index_set_int_def)

sepref_def encoded_irred_index_set_int_impl
  is \<open>uncurry encoded_irred_index_set_int\<close>
  :: \<open>sint64_nat_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k \<rightarrow>\<^sub>a (sint_assn' TYPE(64))\<close>
  unfolding encoded_irred_index_set_int_alt_def
  apply (annot_sint_const \<open>TYPE(64)\<close>)
  by sepref

lemmas [sepref_fr_rules] =
  encoded_irred_index_set_int_impl.refine[FCOMP encoded_irred_index_set]

sepref_register is_marked set_marked

term ahm_set_marked
sepref_def ahm_set_marked_code
  is \<open>uncurry2 ahm_set_marked\<close>
  :: \<open>(larray64_assn (sint_assn' TYPE(64)))\<^sup>d *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a (sint_assn' TYPE(64))\<^sup>k \<rightarrow>\<^sub>a (larray64_assn (sint_assn' TYPE(64)))\<close>
  unfolding ahm_set_marked_def
  by sepref

no_notation WB_More_Refinement.fref (\<open>[_]\<^sub>f _ \<rightarrow> _\<close> [0,60,60] 60)
no_notation WB_More_Refinement.freft (\<open>_ \<rightarrow>\<^sub>f _\<close> [60,60] 60)

lemma ahm_set_marked_set_marked:
 \<open>(uncurry2 ahm_set_marked, uncurry2 set_marked)
    \<in>  (array_hash_map_rel encoded_irred_indices) \<times>\<^sub>f nat_lit_lit_rel \<times>\<^sub>f encoded_irred_indices \<rightarrow> \<langle>array_hash_map_rel encoded_irred_indices\<rangle>nres_rel\<close>
proof -
  have H: \<open>(0, a) \<notin> encoded_irred_indices\<close> for a
    by (auto simp: encoded_irred_indices_def)
  show ?thesis
    unfolding fref_param1
    apply (rule ahm_set_marked_set_marked[unfolded convert_fref])
    apply (rule H)
    done
qed

lemmas [sepref_fr_rules] =
  ahm_create_code.refine[FCOMP ahm_create_create, where R11 = encoded_irred_indices]
  ahm_empty_code.refine[FCOMP ahm_empty_empty, where R19 = encoded_irred_indices]
  ahm_is_marked_code.refine[FCOMP ahm_is_marked_is_marked2[where R = encoded_irred_indices]]
  ahm_get_marked_code.refine[FCOMP ahm_get_marked_get_marked[where R = encoded_irred_indices]]
  ahm_empty_code.refine[FCOMP ahm_empty_empty, where R19 = encoded_irred_indices]
  ahm_set_marked_code.refine[FCOMP ahm_set_marked_set_marked]

definition length_watchlist_raw where
  \<open>length_watchlist_raw S = length (get_watched_wl_heur S)\<close>

definition length_watchlist_raw_code where
  \<open>length_watchlist_raw_code = read_watchlist_wl_heur_code (length_watchlist_full_impl)\<close>

global_interpretation watchlist_length_raw: read_watchlist_param_adder0 where
  f' = \<open>RETURN o length\<close> and
  f = \<open>length_watchlist_full_impl\<close> and
  x_assn = sint64_nat_assn and
  P = \<open>(\<lambda>_. True)\<close>
  rewrites
    \<open>read_watchlist_wl_heur (RETURN \<circ> length) = RETURN o length_watchlist_raw\<close> and
    \<open>read_watchlist_wl_heur_code (length_watchlist_full_impl) = length_watchlist_raw_code\<close>
  apply unfold_locales
  apply (rule length_watchlist_full_impl.refine)
  subgoal
     by (auto intro!: ext simp: length_watchlist_raw_def read_all_st_def length_watchlist_def
         length_ll_def
       split: isasat_int.splits)
  subgoal by (auto simp: length_watchlist_raw_code_def)
  done

lemmas [sepref_fr_rules] = watchlist_length_raw.refine
lemmas [unfolded inline_direct_return_node_case, llvm_code] =
  length_watchlist_raw_code_def[unfolded read_all_st_code_def]

sepref_register create encoded_irred_index_set encoded_irred_index_get
sepref_register uminus_lit:  "uminus :: nat literal \<Rightarrow> _"

lemma isa_clause_remove_duplicate_clause_wl_alt_def:
  \<open>isa_clause_remove_duplicate_clause_wl C S = (do{
    let (N', S) = extract_arena_wl_heur S;
    st \<leftarrow> mop_arena_status N' C;
    let st = st = IRRED;
    ASSERT (mark_garbage_pre (N', C) \<and> arena_is_valid_clause_vdom (N') C);
    let N' = extra_information_mark_to_delete (N') C;
    let (lcount, S) = extract_lcount_wl_heur S;
    ASSERT(\<not>st \<longrightarrow> clss_size_lcount lcount \<ge> 1);
    let lcount = (if st then lcount else (clss_size_decr_lcount lcount));
    let (stats, S) = extract_stats_wl_heur S;
    let stats = (if st then decr_irred_clss stats else stats);
    let S = update_arena_wl_heur N' S;
    let S = update_lcount_wl_heur lcount S;
    let S = update_stats_wl_heur stats S;
    RETURN S
   })\<close>
    by (auto simp: isa_clause_remove_duplicate_clause_wl_def
        state_extractors split: isasat_int.splits)


sepref_def isa_clause_remove_duplicate_clause_wl_impl
  is \<open>uncurry isa_clause_remove_duplicate_clause_wl\<close>
  :: \<open>[\<lambda>(L, S). length (get_clauses_wl_heur S) \<le> sint64_max \<and> learned_clss_count S \<le> uint64_max]\<^sub>a
  sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding isa_clause_remove_duplicate_clause_wl_alt_def
  by sepref
sepref_register isa_binary_clause_subres_wl


lemma isa_binary_clause_subres_wl_alt_def:
  \<open>isa_binary_clause_subres_wl C L L' S\<^sub>0 = do {
      ASSERT (isa_binary_clause_subres_lits_wl_pre C L L' S\<^sub>0);
      let (M, S) = extract_trail_wl_heur S\<^sub>0;
      M \<leftarrow> cons_trail_Propagated_tr L 0 M;
      let (lcount, S) = extract_lcount_wl_heur S;
      ASSERT (lcount = get_learned_count S\<^sub>0);
      let (N', S) = extract_arena_wl_heur S;
      st \<leftarrow> mop_arena_status N' C;
      let st = st = IRRED;
      ASSERT (mark_garbage_pre (N', C) \<and> arena_is_valid_clause_vdom (N') C);
      let N' = extra_information_mark_to_delete (N') C;
      ASSERT(\<not>st \<longrightarrow> (clss_size_lcount lcount \<ge> 1 \<and> clss_size_lcountUEk (clss_size_decr_lcount lcount) < learned_clss_count S\<^sub>0));
      let lcount = (if st then lcount else (clss_size_incr_lcountUEk (clss_size_decr_lcount lcount)));
      let (stats, S) = extract_stats_wl_heur S;
      let stats = (if st then decr_irred_clss stats else stats);
      let stats = incr_units_since_last_GC (incr_uset stats);
      let S = update_trail_wl_heur M S;
      let S = update_arena_wl_heur N' S;
      let S = update_lcount_wl_heur lcount S;
      let S = update_stats_wl_heur stats S;
      RETURN S
  }\<close>
  by (auto simp: isa_binary_clause_subres_wl_def learned_clss_count_def
        state_extractors split: isasat_int.splits)

sepref_def isa_binary_clause_subres_wl_impl
  is \<open>uncurry3 isa_binary_clause_subres_wl\<close>
  :: \<open>[\<lambda>(((C,L), L'), S). length (get_clauses_wl_heur S) \<le> sint64_max \<and> learned_clss_count S \<le> uint64_max]\<^sub>a
  sint64_nat_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding isa_binary_clause_subres_wl_alt_def[abs_def]
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

sepref_def isa_deduplicate_binary_clauses_wl_code
  is \<open>uncurry2 isa_deduplicate_binary_clauses_wl\<close>
  :: \<open>[\<lambda>((L, CS), S). length (get_clauses_wl_heur S) \<le> sint64_max \<and> learned_clss_count S \<le> uint64_max]\<^sub>a
  unat_lit_assn\<^sup>k *\<^sub>a (hr_comp (larray_assn' TYPE(64) (sint_assn' TYPE(64))) (array_hash_map_rel encoded_irred_indices))\<^sup>d *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>
  hr_comp (larray_assn' TYPE(64) (sint_assn' TYPE(64))) (array_hash_map_rel encoded_irred_indices) \<times>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding isa_deduplicate_binary_clauses_wl_def
    mop_polarity_st_heur_def[symmetric]
    mop_arena_status_st_def[symmetric]
    tri_bool_eq_def[symmetric]
    encoded_irred_index_set_def[symmetric]
    encoded_irred_index_irred_def[symmetric]
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref


sepref_register get_vmtf_heur_array_nth get_vmtf_heur_fst
  isa_deduplicate_binary_clauses_wl

lemma Massign_split: \<open>do{ x \<leftarrow> (M :: _ nres); f x} = do{(a,b) \<leftarrow> M; f (a,b)}\<close>
  by auto


lemma isa_mark_duplicated_binary_clauses_as_garbage_wl2_alt_def:
  \<open>isa_mark_duplicated_binary_clauses_as_garbage_wl2 S\<^sub>0 = (do {
     let ns = get_vmtf_heur_array S\<^sub>0;
    ASSERT (mark_duplicated_binary_clauses_as_garbage_pre_wl_heur S\<^sub>0);
    CS \<leftarrow> create (length (get_watched_wl_heur S\<^sub>0));
    (_, CS, S) \<leftarrow> WHILE\<^sub>T\<^bsup> \<lambda>(n,CS, S). get_vmtf_heur_array S\<^sub>0 = (get_vmtf_heur_array S)\<^esup>(\<lambda>(n, CS, S). n \<noteq> None \<and> get_conflict_wl_is_None_heur S)
      (\<lambda>(n, CS, S). do {
        ASSERT (n \<noteq> None);
        let A = the n;
        ASSERT (A < length (get_vmtf_heur_array S));
        ASSERT (A \<le> uint32_max div 2);
        let skip = False;
        if skip then RETURN (get_next (get_vmtf_heur_array S ! A), CS, S)
        else do {
          ASSERT (length (get_clauses_wl_heur S) \<le> length (get_clauses_wl_heur S\<^sub>0) \<and> learned_clss_count S \<le> learned_clss_count S\<^sub>0);
          (CS, S) \<leftarrow> isa_deduplicate_binary_clauses_wl (Pos A) CS S;
          ASSERT (length (get_clauses_wl_heur S) \<le> length (get_clauses_wl_heur S\<^sub>0) \<and> learned_clss_count S \<le> learned_clss_count S\<^sub>0);
          (CS, S) \<leftarrow> isa_deduplicate_binary_clauses_wl (Neg A) CS S;
          ASSERT (ns = get_vmtf_heur_array S);
         RETURN (get_next (get_vmtf_heur_array S ! A), CS, S)
       }
     })
     (Some (get_vmtf_heur_fst S\<^sub>0), CS, S\<^sub>0);
    RETURN S
          })\<close>
   unfolding isa_mark_duplicated_binary_clauses_as_garbage_wl2_def
   apply (simp add: case_prod_beta)
   apply (subst Massign_split[of \<open>_ :: (_ \<times> isasat) nres\<close>])
   apply (subst (2) Massign_split[of \<open>_ :: (_ \<times> isasat) nres\<close>])
   unfolding prod.simps
   apply simp
   done

sepref_def isa_deduplicate_binary_clauses_code
  is isa_mark_duplicated_binary_clauses_as_garbage_wl2
  :: \<open>[\<lambda>S. length (get_clauses_wl_heur S) \<le> sint64_max \<and> learned_clss_count S \<le> uint64_max]\<^sub>a
     isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  unfolding isa_mark_duplicated_binary_clauses_as_garbage_wl2_alt_def
    get_vmtf_heur_array_nth_def[symmetric] atom.fold_option nres_monad3
    length_watchlist_def[unfolded length_ll_def, symmetric]
    length_watchlist_raw_def[symmetric]
  apply (rewrite at \<open>let _ = get_vmtf_heur_array _ in _\<close> Let_def)
  apply (rewrite at \<open>let _ = False in _\<close> Let_def)
  unfolding if_False nres_monad3
  supply [[goals_limit=1]]
  by sepref

experiment
begin
 export_llvm isa_simplify_clauses_with_unit_st2_code
    isa_simplify_clauses_with_unit_st_wl2_code
    isa_simplify_clauses_with_units_st_wl2_code
    isa_deduplicate_binary_clauses_code
end

end
