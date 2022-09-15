theory IsaSAT_Simplify_Binaries_LLVM
  imports 
    IsaSAT_Simplify_Clause_Units_LLVM
    IsaSAT_Simplify_Binaries
begin

no_notation WB_More_Refinement.fref (\<open>[_]\<^sub>f _ \<rightarrow> _\<close> [0,60,60] 60)
no_notation WB_More_Refinement.freft (\<open>_ \<rightarrow>\<^sub>f _\<close> [60,60] 60)


abbreviation ahm_assn :: \<open>_\<close> where
  \<open>ahm_assn \<equiv> larray64_assn (sint_assn' TYPE(64)) \<times>\<^sub>a al_assn' TYPE(64) (snat_assn' TYPE(64))\<close>

sepref_def ahm_create_code
  is \<open>ahm_create\<close>
  :: \<open>(snat_assn' TYPE(64))\<^sup>k \<rightarrow>\<^sub>a ahm_assn\<close>
  unfolding ahm_create_def larray_fold_custom_replicate al_fold_custom_empty[where 'l=64]
  apply (annot_sint_const \<open>TYPE(64)\<close>)
  by sepref

definition encoded_irred_indices where
  \<open>encoded_irred_indices = {(a, b::nat \<times> bool). a \<le> int sint64_max \<and> -a \<le> int sint64_max \<and> (snd b \<longleftrightarrow> a > 0) \<and> fst b = (if a < 0 then nat (-a) else nat a) \<and> fst b \<noteq> 0}\<close>

sepref_def ahm_is_marked_code
  is \<open>uncurry ahm_is_marked\<close>
  :: \<open>(ahm_assn)\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
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
  :: \<open>(ahm_assn)\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a sint_assn' TYPE(64)\<close>
  unfolding ahm_get_marked_def
  by sepref

sepref_def ahm_empty_code
  is \<open>ahm_empty\<close>
  :: \<open>(ahm_assn)\<^sup>d \<rightarrow>\<^sub>a ahm_assn\<close>
  unfolding ahm_empty_def
  apply (annot_sint_const \<open>TYPE(64)\<close>)
  apply (annot_snat_const \<open>TYPE(64)\<close>)
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

sepref_register is_marked set_marked update_marked

sepref_def ahm_set_marked_code
  is \<open>uncurry2 ahm_set_marked\<close>
  :: \<open>ahm_assn\<^sup>d *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a (sint_assn' TYPE(64))\<^sup>k \<rightarrow>\<^sub>a ahm_assn\<close>
  unfolding ahm_set_marked_def
  by sepref

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

sepref_def ahm_update_marked_code
  is \<open>uncurry2 ahm_update_marked\<close>
  :: \<open>ahm_assn\<^sup>d *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a (sint_assn' TYPE(64))\<^sup>k \<rightarrow>\<^sub>a ahm_assn\<close>
  unfolding ahm_update_marked_def
  by sepref

lemma ahm_update_marked_update_marked:
 \<open>(uncurry2 ahm_update_marked, uncurry2 update_marked)
    \<in>  (array_hash_map_rel encoded_irred_indices) \<times>\<^sub>f nat_lit_lit_rel \<times>\<^sub>f encoded_irred_indices \<rightarrow> \<langle>array_hash_map_rel encoded_irred_indices\<rangle>nres_rel\<close>
proof -
  have H: \<open>(0, a) \<notin> encoded_irred_indices\<close> for a
    by (auto simp: encoded_irred_indices_def)
  show ?thesis
    unfolding fref_param1
    apply (rule ahm_update_marked_update_marked[unfolded convert_fref])
    apply (rule H)
    done
qed

definition ahm_full_assn :: \<open>_\<close> where
  \<open>ahm_full_assn =  hr_comp (larray64_assn (sint_assn' TYPE(64)) \<times>\<^sub>a Size_Ordering_it.arr_assn)
                 (array_hash_map_rel encoded_irred_indices)\<close>

schematic_goal ahm_full_assn_assn[sepref_frame_free_rules]: \<open>MK_FREE ahm_full_assn ?a\<close>
  unfolding ahm_full_assn_def by synthesize_free

lemmas [unfolded ahm_full_assn_def[symmetric], sepref_fr_rules] =
  ahm_create_code.refine[FCOMP ahm_create_create, where R11 = encoded_irred_indices]
  ahm_empty_code.refine[FCOMP ahm_empty_empty, where R19 = encoded_irred_indices]
  ahm_is_marked_code.refine[FCOMP ahm_is_marked_is_marked2[where R = encoded_irred_indices]]
  ahm_get_marked_code.refine[FCOMP ahm_get_marked_get_marked[where R = encoded_irred_indices]]
  ahm_empty_code.refine[FCOMP ahm_empty_empty, where R19 = encoded_irred_indices]
  ahm_set_marked_code.refine[FCOMP ahm_set_marked_set_marked]
  ahm_update_marked_code.refine[FCOMP ahm_update_marked_update_marked]


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
    let stats = incr_binary_red_removed_clss (if st then decr_irred_clss stats else stats);
    let S = update_arena_wl_heur N' S;
    let S = update_lcount_wl_heur lcount S;
    let S = update_stats_wl_heur stats S;
    RETURN S
   })\<close>
    by (auto simp: isa_clause_remove_duplicate_clause_wl_def
        state_extractors split: isasat_int_splits)


sepref_def isa_clause_remove_duplicate_clause_wl_impl
  is \<open>uncurry isa_clause_remove_duplicate_clause_wl\<close>
  :: \<open>[\<lambda>(L, S). length (get_clauses_wl_heur S) \<le> sint64_max \<and> learned_clss_count S \<le> uint64_max]\<^sub>a
  sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding isa_clause_remove_duplicate_clause_wl_alt_def
  by sepref
sepref_register isa_binary_clause_subres_wl

sepref_register incr_binary_unit_derived_clss
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
      let stats = incr_binary_unit_derived_clss (if st then decr_irred_clss stats else stats);
      let stats = incr_units_since_last_GC (incr_uset stats);
      let S = update_trail_wl_heur M S;
      let S = update_arena_wl_heur N' S;
      let S = update_lcount_wl_heur lcount S;
      let S = update_stats_wl_heur stats S;
      let _ = log_unit_clause L;
      RETURN S
  }\<close>
  apply (subst Let_def[of \<open>log_unit_clause L\<close>])
  by (auto simp: isa_binary_clause_subres_wl_def learned_clss_count_def
        state_extractors split: isasat_int_splits)

sepref_def isa_binary_clause_subres_wl_impl
  is \<open>uncurry3 isa_binary_clause_subres_wl\<close>
  :: \<open>[\<lambda>(((C,L), L'), S). length (get_clauses_wl_heur S) \<le> sint64_max \<and> learned_clss_count S \<le> uint64_max]\<^sub>a
  sint64_nat_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding isa_binary_clause_subres_wl_alt_def[abs_def]
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

sepref_register binary_deduplicate_required
sepref_def binary_deduplicate_required_fast_code
  is \<open>binary_deduplicate_required\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  supply [[goals_limit=1]] of_nat_snat[sepref_import_param]
  unfolding binary_deduplicate_required_def should_inprocess_st_def
  by sepref

sepref_def isa_deduplicate_binary_clauses_wl_code
  is \<open>uncurry2 isa_deduplicate_binary_clauses_wl\<close>
  :: \<open>[\<lambda>((L, CS), S). length (get_clauses_wl_heur S) \<le> sint64_max \<and> learned_clss_count S \<le> uint64_max]\<^sub>a
  unat_lit_assn\<^sup>k *\<^sub>a ahm_full_assn\<^sup>d *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>
  ahm_full_assn \<times>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding isa_deduplicate_binary_clauses_wl_def
    mop_polarity_st_heur_def[symmetric]
    mop_arena_status_st_def[symmetric]
    tri_bool_eq_def[symmetric]
    encoded_irred_index_set_def[symmetric]
    encoded_irred_index_irred_def[symmetric]
    encoded_irred_index_get_def[symmetric]
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
    skip \<leftarrow> binary_deduplicate_required S\<^sub>0;
    CS \<leftarrow> create (length (get_watched_wl_heur S\<^sub>0));
    (_, CS, S) \<leftarrow> WHILE\<^sub>T\<^bsup> \<lambda>(n,CS, S). get_vmtf_heur_array S\<^sub>0 = (get_vmtf_heur_array S)\<^esup>(\<lambda>(n, CS, S). n \<noteq> None \<and> get_conflict_wl_is_None_heur S)
      (\<lambda>(n, CS, S). do {
        ASSERT (n \<noteq> None);
        let A = the n;
        ASSERT (A < length (get_vmtf_heur_array S));
        ASSERT (A \<le> uint32_max div 2);
        added \<leftarrow> mop_is_marked_added_heur_st S A;
        if \<not>skip \<or> \<not>added then RETURN (get_next (get_vmtf_heur_array S ! A), CS, S)
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
    unfolding isa_mark_duplicated_binary_clauses_as_garbage_wl2_def bind_to_let_conv
      nres_monad3
   apply (simp add: case_prod_beta cong: if_cong)
   unfolding bind_to_let_conv Let_def prod.simps
   apply (subst Massign_split[of \<open>isa_deduplicate_binary_clauses_wl (Pos _) _ _\<close>])
   unfolding prod.simps nres_monad3
   apply (subst (2) Massign_split[of \<open>_ :: (_ \<times> isasat) nres\<close>])
   unfolding prod.simps nres_monad3
   apply (auto intro!: bind_cong[OF refl] cong: if_cong)
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
  unfolding if_False nres_monad3
  supply [[goals_limit=1]]
  by sepref

end