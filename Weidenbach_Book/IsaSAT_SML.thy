theory IsaSAT_SML
  imports  Watched_Literals.WB_Word_Assn IsaSAT Version IsaSAT_Restart_SML IsaSAT_Initialisation_SML
begin

(*TODO Move*)
lemma [code]:
  \<open>nth_aa64_i32_u64 xs x L = do {
      x \<leftarrow> nth_u_code xs x;
      arl64_get x L \<bind> return
    }\<close>
  unfolding nth_aa64_i32_u64_def nth_aa64_def
    nth_nat_of_uint32_nth' nth_u_code_def[symmetric] ..

lemma [code]: \<open>uint32_max_uint32 = 4294967295\<close>
  by (auto simp: uint32_max_uint32_def)
(*end move*)
abbreviation  model_stat_assn where
  \<open>model_stat_assn \<equiv> option_assn (arl_assn unat_lit_assn) *a stats_assn\<close>


abbreviation lits_with_max_assn where
  \<open>lits_with_max_assn \<equiv> hr_comp (arl_assn uint32_nat_assn *a uint32_nat_assn) lits_with_max_rel\<close>
lemma lits_with_max_assn_alt_def: \<open>lits_with_max_assn  = hr_comp (arl_assn uint32_assn *a uint32_assn)
          (lits_with_max_rel O \<langle>uint32_nat_rel\<rangle>IsaSAT_Initialisation.mset_rel)\<close>
proof -
  have 1: \<open>arl_assn uint32_nat_assn *a uint32_nat_assn =
     hr_comp (arl_assn uint32_assn *a uint32_assn) (\<langle>uint32_nat_rel\<rangle>list_rel \<times>\<^sub>r uint32_nat_rel)\<close>
     unfolding arl_assn_comp' hr_comp_prod_conv
     by auto

  have [simp]: \<open> Max (insert 0 (nat_of_uint32 ` set aa)) =  nat_of_uint32 (Max (insert 0 (set aa)))\<close>for aa
    apply (induction aa)
    subgoal by auto
    subgoal for a aa
      by (cases \<open>nat_of_uint32 ` set aa = {}\<close>) (auto simp: nat_of_uint32_max)
    done

  have 2: \<open>((\<langle>uint32_nat_rel\<rangle>list_rel \<times>\<^sub>f uint32_nat_rel) O lits_with_max_rel) =
     (lits_with_max_rel O \<langle>uint32_nat_rel\<rangle>IsaSAT_Initialisation.mset_rel)\<close>
    apply (rule; rule)
    apply (case_tac x)
    apply (simp only: relcomp.simps)
    apply normalize_goal+
    subgoal for yx a b xa xb xc
       apply (rule exI[of _ a])
       apply (rule exI[of _ \<open>uint32_of_nat `# mset (fst xb)\<close>])
       apply (rule exI[of _ \<open>mset (fst xb)\<close>])
       apply (cases xa)
       by (auto simp: uint32_nat_rel_def IsaSAT_Initialisation.mset_rel_def p2rel_def rel2p_def[abs_def] br_def
         rel_mset_def lits_with_max_rel_def list_rel_def list_all2_op_eq_map_right_iff')
    apply (case_tac x)
    apply (simp only: relcomp.simps)
    apply normalize_goal+
    subgoal for yx a b xa xb xc
       apply (rule exI[of _ a])
       apply (cases xa)
       by (auto simp: uint32_nat_rel_def IsaSAT_Initialisation.mset_rel_def p2rel_def rel2p_def[abs_def] br_def
         rel_mset_def lits_with_max_rel_def list_rel_def list_all2_op_eq_map_right_iff')
    done

  show ?thesis
    unfolding 1 hr_comp_assoc 2
    by auto
qed

lemma init_state_wl_D'_code_isasat: \<open>(hr_comp isasat_init_assn
   (Id \<times>\<^sub>f
    (Id \<times>\<^sub>f
     (Id \<times>\<^sub>f
      (nat_rel \<times>\<^sub>f
       (\<langle>\<langle>Id\<rangle>list_rel\<rangle>list_rel \<times>\<^sub>f
        (Id \<times>\<^sub>f (\<langle>bool_rel\<rangle>list_rel \<times>\<^sub>f (nat_rel \<times>\<^sub>f (Id \<times>\<^sub>f (Id \<times>\<^sub>f Id))))))))))) = isasat_init_assn\<close>
  by auto

lemma list_assn_list_mset_rel_clauses_l_assn:
  \<open>(hr_comp (list_assn (list_assn unat_lit_assn)) (list_mset_rel O \<langle>list_mset_rel\<rangle>IsaSAT_Initialisation.mset_rel)) xs xs'
     = clauses_l_assn xs xs'\<close>
proof -
  have ex_remove_xs:
    \<open>(\<exists>xs. mset xs = mset x \<and> {#literal_of_nat (nat_of_uint32 x). x \<in># mset xs#} = y) \<longleftrightarrow>
       ({#literal_of_nat (nat_of_uint32 x). x \<in># mset x#} = y)\<close>
    for x y
    by auto

  show ?thesis
    unfolding list_assn_pure_conv list_mset_assn_pure_conv
     list_rel_mset_rel_def
    apply (auto simp: hr_comp_def)
    apply (auto simp: ent_ex_up_swap list_mset_assn_def pure_def)
    using ex_mset[of \<open>map (\<lambda>x. literal_of_nat (nat_of_uint32 x)) `# mset xs'\<close>]
    by (auto simp add: list_mset_rel_def br_def IsaSAT_Initialisation.mset_rel_def unat_lit_rel_def
        uint32_nat_rel_def nat_lit_rel_def WB_More_Refinement.list_mset_rel_def
        p2rel_def Collect_eq_comp rel2p_def
        list_all2_op_eq_map_map_right_iff rel_mset_def rel2p_def[abs_def]
        list_all2_op_eq_map_right_iff' ex_remove_xs list_rel_def
        list_all2_op_eq_map_right_iff
        simp del: literal_of_nat.simps)
qed

definition get_trail_wl_code :: \<open>_ \<Rightarrow> uint32 array_list option \<times> stats\<close> where
  \<open>get_trail_wl_code = (\<lambda>((M, _), _, _, _, _ ,_ ,_ ,_, _, _, _, stat, _). (Some M, stat))\<close>

definition get_stats_code :: \<open>_ \<Rightarrow> uint32 array_list option \<times> stats\<close> where
  \<open>get_stats_code = (\<lambda>((M, _), _, _, _, _ ,_ ,_ ,_, _, _, _, stat, _). (None, stat))\<close>


definition  model_assn where
  \<open>model_assn = hr_comp model_stat_assn model_stat_rel\<close>

lemma extract_model_of_state_stat_hnr[sepref_fr_rules]:
  \<open>(return o get_trail_wl_code, RETURN o extract_model_of_state_stat) \<in> isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a
       model_stat_assn\<close>
proof -
  have [simp]: \<open>(\<lambda>a c. \<up> ((c, a) \<in> unat_lit_rel)) = unat_lit_assn\<close>
    by (auto simp: unat_lit_rel_def pure_def)
  have [simp]: \<open>id_assn (an, ao, bb) (bs, bt, bu) = (id_assn an bs * id_assn ao bt * id_assn bb bu)\<close>
    for an ao bb bs bt bu :: uint64
    by (auto simp: pure_def)
  show ?thesis
    by sepref_to_hoare
      (sep_auto simp: twl_st_heur_def hr_comp_def trail_pol_def isasat_unbounded_assn_def
        get_trail_wl_code_def
        extract_model_of_state_def extract_model_of_state_stat_def
        dest!: ann_lits_split_reasons_map_lit_of
        elim!: mod_starE)
qed

lemma get_stats_code[sepref_fr_rules]:
  \<open>(return o get_stats_code, RETURN o extract_state_stat) \<in> isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a
       model_stat_assn\<close>
proof -
  have [simp]: \<open>(\<lambda>a c. \<up> ((c, a) \<in> unat_lit_rel)) = unat_lit_assn\<close>
    by (auto simp: unat_lit_rel_def pure_def)
  have [simp]: \<open>id_assn (an, ao, bb) (bs, bt, bu) = (id_assn an bs * id_assn ao bt * id_assn bb bu)\<close>
    for an ao bb bs bt bu :: uint64
    by (auto simp: pure_def)
  show ?thesis
    by sepref_to_hoare
      (sep_auto simp: twl_st_heur_def hr_comp_def trail_pol_def isasat_unbounded_assn_def
        get_trail_wl_code_def get_stats_code_def
        extract_model_of_state_def extract_model_of_state_stat_def extract_state_stat_def
        dest!: ann_lits_split_reasons_map_lit_of
        elim!: mod_starE)
qed

lemma convert_state_hnr:
  \<open>(uncurry (return oo (\<lambda>_ S. S)), uncurry (RETURN oo convert_state))
   \<in> ghost_assn\<^sup>k *\<^sub>a (isasat_init_assn)\<^sup>d \<rightarrow>\<^sub>a
     isasat_init_assn\<close>
  by sepref_to_hoare (sep_auto simp: convert_state_def)

lemma  convert_state_hnr_unb:
  \<open>(uncurry (return oo (\<lambda>_ S. S)), uncurry (RETURN oo convert_state))
   \<in> ghost_assn\<^sup>k *\<^sub>a (isasat_init_unbounded_assn)\<^sup>d \<rightarrow>\<^sub>a
     isasat_init_unbounded_assn\<close>
  by sepref_to_hoare (sep_auto simp: convert_state_def)

lemma IsaSAT_use_fast_mode[sepref_fr_rules]:
  \<open>(uncurry0 (return IsaSAT_use_fast_mode), uncurry0 (RETURN IsaSAT_use_fast_mode))
   \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare sep_auto

sepref_definition  empty_conflict_code'
  is \<open>uncurry0 (empty_conflict_code)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a model_stat_assn\<close>
  unfolding empty_conflict_code_def
  apply (rewrite in \<open>let _ =  \<hole> in _\<close> IICF_Array_List.arl.fold_custom_empty)
  apply (rewrite in \<open>let _ =  \<hole> in _\<close> annotate_assn[where A=\<open>arl_assn unat_lit_assn\<close>])
  by sepref

declare empty_conflict_code'.refine[sepref_fr_rules]

sepref_definition  empty_init_code'
  is \<open>uncurry0 (RETURN empty_init_code)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a model_stat_assn\<close>
  unfolding empty_init_code_def
  by sepref

declare empty_init_code'.refine[sepref_fr_rules]

sepref_register init_dt_wl_heur_full

declare extract_model_of_state_stat_hnr[sepref_fr_rules]
sepref_register to_init_state from_init_state get_conflict_wl_is_None_init extract_stats
  init_dt_wl_heur


declare
  get_stats_code[sepref_fr_rules]


lemma isasat_fast_init_alt_def:
  \<open>RETURN o isasat_fast_init = (\<lambda>(M, N, _). RETURN (length N \<le> isasat_fast_bound))\<close>
  by (auto simp: isasat_fast_init_def uint64_max_def uint32_max_def isasat_fast_bound_def intro!: ext)

sepref_definition isasat_fast_init_code
  is \<open>RETURN o isasat_fast_init\<close>
  :: \<open>isasat_init_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  supply [[goals_limit=1]]
  unfolding isasat_fast_init_alt_def isasat_init_assn_def isasat_fast_bound_def[symmetric]
  by sepref

declare isasat_fast_init_code.refine[sepref_fr_rules]

declare convert_state_hnr[sepref_fr_rules]
  convert_state_hnr_unb[sepref_fr_rules]

sepref_register
   cdcl_twl_stgy_restart_prog_wl_heur

declare init_state_wl_D'_code.refine[FCOMP init_state_wl_D'[unfolded convert_fref],
  unfolded lits_with_max_assn_alt_def[symmetric] init_state_wl_heur_fast_def[symmetric],
  unfolded init_state_wl_D'_code_isasat, sepref_fr_rules]

lemma init_state_wl_D'_code_isasat_unb: \<open>(hr_comp isasat_init_unbounded_assn
   (Id \<times>\<^sub>f
    (Id \<times>\<^sub>f
     (Id \<times>\<^sub>f
      (nat_rel \<times>\<^sub>f
       (\<langle>\<langle>Id\<rangle>list_rel\<rangle>list_rel \<times>\<^sub>f
        (Id \<times>\<^sub>f (\<langle>bool_rel\<rangle>list_rel \<times>\<^sub>f (nat_rel \<times>\<^sub>f (Id \<times>\<^sub>f (Id \<times>\<^sub>f Id))))))))))) = isasat_init_unbounded_assn\<close>
  unfolding isasat_init_unbounded_assn_def  by auto

lemma arena_assn_alt_def: \<open>arl_assn (pure (uint32_nat_rel O arena_el_rel)) = arena_assn\<close>
  unfolding hr_comp_pure[symmetric] ..

lemma [sepref_fr_rules]: \<open>(init_state_wl_D'_code_unb, init_state_wl_heur)
\<in> [\<lambda>x. distinct_mset x \<and>
       (\<forall>L\<in>#\<L>\<^sub>a\<^sub>l\<^sub>l x.
           nat_of_lit L
           \<le> uint_max)]\<^sub>a IsaSAT_SML.lits_with_max_assn\<^sup>d \<rightarrow> isasat_init_unbounded_assn\<close>
  using init_state_wl_D'_code_unb.refine[FCOMP init_state_wl_D'[unfolded convert_fref]]
  unfolding lits_with_max_assn_alt_def[symmetric] init_state_wl_D'_code_isasat_unb arena_assn_alt_def
  unfolding isasat_init_unbounded_assn_def
  by auto

sepref_definition isasat_init_fast_slow_code
  is \<open>isasat_init_fast_slow\<close>
  :: \<open>isasat_init_assn\<^sup>d \<rightarrow>\<^sub>a isasat_init_unbounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding isasat_init_unbounded_assn_def isasat_init_assn_def isasat_init_fast_slow_def
  apply (rewrite at \<open>(_, _, _, _, _, _, _, _, _, _, \<hole>, _)\<close> arl64_to_arl_conv_def[symmetric])
  apply (rewrite at \<open>(_, \<hole>, _, _, _, _, _, _, _, _, _, _)\<close> arl64_to_arl_conv_def[symmetric])
  apply (rewrite in \<open>(_, _, _, _, _, _, _, _, _, _, \<hole>, _)\<close> arl_nat_of_uint64_conv_def[symmetric])
  by sepref

declare isasat_init_fast_slow_code.refine[sepref_fr_rules]

sepref_register init_dt_wl_heur_unb

fun (in -) is_failed_heur_init_code :: \<open>_ \<Rightarrow> bool\<close> where
  \<open>is_failed_heur_init_code (_, _, _, _, _, _, _, _, _, _, _, failed) = failed\<close>

lemma is_failed_heur_init_code[sepref_fr_rules]:
  \<open>(return o is_failed_heur_init_code, RETURN o is_failed_heur_init) \<in> isasat_init_assn\<^sup>k \<rightarrow>\<^sub>a
       bool_assn\<close>
  by (sepref_to_hoare) (sep_auto simp: isasat_init_assn_def
        elim!: mod_starE)

declare init_dt_wl_heur_code_unb.refine[sepref_fr_rules]

sepref_definition IsaSAT_code
  is \<open>uncurry IsaSAT_heur\<close>
  :: \<open>opts_assn\<^sup>d *\<^sub>a (list_assn (list_assn unat_lit_assn))\<^sup>k \<rightarrow>\<^sub>a model_stat_assn\<close>
  supply [[goals_limit=1]] isasat_fast_init_def[simp]
  unfolding IsaSAT_heur_def empty_conflict_def[symmetric]
    get_conflict_wl_is_None extract_model_of_state_def[symmetric]
    extract_stats_def[symmetric] init_dt_wl_heur_b_def[symmetric]
    length_get_clauses_wl_heur_init_def[symmetric]
   init_dt_step_wl_heur_unb_def[symmetric] init_dt_wl_heur_unb_def[symmetric]
  supply get_conflict_wl_is_None_heur_init_def[simp]
  supply id_mset_list_assn_list_mset_assn[sepref_fr_rules] get_conflict_wl_is_None_def[simp]
   option.splits[split]
   extract_stats_def[simp del]
  apply (rewrite at \<open>extract_atms_clss _ \<hole>\<close> op_extract_list_empty_def[symmetric])
  apply (rewrite at \<open>extract_atms_clss _ \<hole>\<close> op_extract_list_empty_def[symmetric])
  apply (rewrite at \<open>extract_atms_clss _ \<hole>\<close> op_extract_list_empty_def[symmetric])
  by sepref

theorem IsaSAT_full_correctness:
  \<open>(uncurry IsaSAT_code, uncurry (\<lambda>_. model_if_satisfiable))
     \<in> [\<lambda>(_, a). Multiset.Ball a distinct_mset \<and>
      (\<forall>C\<in>#a.  \<forall>L\<in>#C. nat_of_lit L  \<le> uint_max)]\<^sub>a opts_assn\<^sup>d *\<^sub>a  clauses_l_assn\<^sup>k \<rightarrow> model_assn\<close>
  using IsaSAT_code.refine[FCOMP IsaSAT_heur_model_if_sat'[unfolded convert_fref],
    unfolded list_assn_list_mset_rel_clauses_l_assn]
  unfolding model_assn_def
  apply auto
  done


sepref_definition cdcl_twl_stgy_restart_prog_bounded_wl_heur_fast_code
  is \<open>cdcl_twl_stgy_restart_prog_bounded_wl_heur\<close>
  :: \<open>[\<lambda>S. isasat_fast S]\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> bool_assn *a isasat_bounded_assn\<close>
  unfolding cdcl_twl_stgy_restart_prog_bounded_wl_heur_def
  supply [[goals_limit = 1]] isasat_fast_def[simp]
  by sepref

declare cdcl_twl_stgy_restart_prog_bounded_wl_heur_fast_code.refine[sepref_fr_rules]

definition get_trail_wl_code_b :: \<open>_ \<Rightarrow> uint32 array_list32 option \<times> stats\<close> where
  \<open>get_trail_wl_code_b = (\<lambda>((M, _), _, _, _, _ ,_ ,_ ,_, _, _, _, stat, _). (Some M, stat))\<close>

abbreviation  model_stat_fast_assn where
  \<open>model_stat_fast_assn \<equiv> option_assn (arl32_assn unat_lit_assn) *a stats_assn\<close>

lemma extract_model_of_state_stat_bounded_hnr[sepref_fr_rules]:
  \<open>(return o get_trail_wl_code_b, RETURN o extract_model_of_state_stat) \<in> isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a
       model_stat_fast_assn\<close>
proof -
  have [simp]: \<open>(\<lambda>a c. \<up> ((c, a) \<in> unat_lit_rel)) = unat_lit_assn\<close>
    by (auto simp: unat_lit_rel_def pure_def)
  have [simp]: \<open>id_assn (an, ao, bb) (bs, bt, bu) = (id_assn an bs * id_assn ao bt * id_assn bb bu)\<close>
    for an ao bb bs bt bu :: uint64
    by (auto simp: pure_def)
  show ?thesis
    by sepref_to_hoare
      (sep_auto simp: twl_st_heur_def hr_comp_def trail_pol_def isasat_bounded_assn_def
        get_trail_wl_code_b_def
        extract_model_of_state_def extract_model_of_state_stat_def
        dest!: ann_lits_split_reasons_map_lit_of
        elim!: mod_starE)
qed


sepref_definition  empty_conflict_fast_code'
  is \<open>uncurry0 (empty_conflict_code)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a model_stat_fast_assn\<close>
  unfolding empty_conflict_code_def
  apply (rewrite in \<open>let _ =  \<hole> in _\<close> arl32.fold_custom_empty)
  apply (rewrite in \<open>let _ =  \<hole> in _\<close> annotate_assn[where A=\<open>arl32_assn unat_lit_assn\<close>])
  by sepref

declare empty_conflict_fast_code'.refine[sepref_fr_rules]

sepref_definition  empty_init_fast_code'
  is \<open>uncurry0 (RETURN empty_init_code)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a model_stat_fast_assn\<close>
  unfolding empty_init_code_def
  by sepref

declare empty_init_fast_code'.refine[sepref_fr_rules]

definition get_stats_fast_code :: \<open>_ \<Rightarrow> uint32 array_list32 option \<times> stats\<close> where
  \<open>get_stats_fast_code = (\<lambda>((M, _), _, _, _, _ ,_ ,_ ,_, _, _, _, stat, _). (None, stat))\<close>

lemma get_stats_b_code[sepref_fr_rules]:
  \<open>(return o get_stats_fast_code, RETURN o extract_state_stat) \<in> isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a
       model_stat_fast_assn\<close>
proof -
  have [simp]: \<open>(\<lambda>a c. \<up> ((c, a) \<in> unat_lit_rel)) = unat_lit_assn\<close>
    by (auto simp: unat_lit_rel_def pure_def)
  have [simp]: \<open>id_assn (an, ao, bb) (bs, bt, bu) = (id_assn an bs * id_assn ao bt * id_assn bb bu)\<close>
    for an ao bb bs bt bu :: uint64
    by (auto simp: pure_def)
  show ?thesis
    by sepref_to_hoare
      (sep_auto simp: twl_st_heur_def hr_comp_def trail_pol_def isasat_bounded_assn_def
        get_trail_wl_code_def get_stats_fast_code_def
        extract_model_of_state_def extract_model_of_state_stat_def extract_state_stat_def
        dest!: ann_lits_split_reasons_map_lit_of
        elim!: mod_starE)
qed

sepref_definition IsaSAT_bounded_code
  is \<open>uncurry IsaSAT_bounded_heur\<close>
  :: \<open>opts_assn\<^sup>d *\<^sub>a (list_assn (list_assn unat_lit_assn))\<^sup>k \<rightarrow>\<^sub>a bool_assn *a model_stat_fast_assn\<close>
  supply [[goals_limit=1]] isasat_fast_init_def[simp]
  unfolding IsaSAT_bounded_heur_def empty_conflict_def[symmetric]
    get_conflict_wl_is_None extract_model_of_state_def[symmetric]
    extract_stats_def[symmetric]
    length_get_clauses_wl_heur_init_def[symmetric]
   init_dt_step_wl_heur_b_def[symmetric] init_dt_wl_heur_b_def[symmetric]
  supply get_conflict_wl_is_None_heur_init_def[simp]
  supply id_mset_list_assn_list_mset_assn[sepref_fr_rules] get_conflict_wl_is_None_def[simp]
   option.splits[split]
   extract_stats_def[simp del]
  apply (rewrite at \<open>extract_atms_clss _ \<hole>\<close> op_extract_list_empty_def[symmetric])
  apply (rewrite at \<open>extract_atms_clss _ \<hole>\<close> op_extract_list_empty_def[symmetric])
  by sepref


subsubsection \<open>Code Export\<close>

definition nth_u_code' where
  [symmetric, code]: \<open>nth_u_code' = nth_u_code\<close>

code_printing constant nth_u_code' \<rightharpoonup> (SML) "(fn/ ()/ =>/ Array.sub/ ((_),/ Word32.toInt (_)))"

definition nth_u64_code' where
  [symmetric, code]: \<open>nth_u64_code' = nth_u64_code\<close>

code_printing constant nth_u64_code' \<rightharpoonup> (SML) "(fn/ ()/ =>/ Array.sub/ ((_),/ Word64.toInt ((_))))"

definition heap_array_set'_u' where
  [symmetric, code]: \<open>heap_array_set'_u' = heap_array_set'_u\<close>

code_printing constant heap_array_set'_u' \<rightharpoonup>
   (SML) "(fn/ ()/ =>/ Array.update/ ((_),/ (Word32.toInt (_)),/ (_)))"

definition heap_array_set'_u64' where
  [symmetric, code]: \<open>heap_array_set'_u64' = heap_array_set'_u64\<close>

code_printing constant heap_array_set'_u64' \<rightharpoonup>
   (SML) "(fn/ ()/ =>/ Array.update/ ((_),/ (Word64.toInt (_)),/ (_)))"

(* code_printing constant two_uint32 \<rightharpoonup> (SML) "(Word32.fromInt 2)"
 *)
definition length_u_code' where
  [symmetric, code]: \<open>length_u_code' = length_u_code\<close>

code_printing constant length_u_code' \<rightharpoonup> (SML_imp) "(fn/ ()/ =>/ Word32.fromInt (Array.length (_)))"

definition length_aa_u_code' where
  [symmetric, code]: \<open>length_aa_u_code' = length_aa_u_code\<close>

code_printing constant length_aa_u_code' \<rightharpoonup> (SML_imp)
   "(fn/ ()/ =>/ Word32.fromInt (Array.length (Array.sub/ ((fn/ (a,b)/ =>/ a) (_),/ IntInf.toInt (integer'_of'_nat (_))))))"

definition nth_raa_i_u64' where
  [symmetric, code]: \<open>nth_raa_i_u64' = nth_raa_i_u64\<close>

code_printing constant nth_raa_i_u64' \<rightharpoonup> (SML_imp)
   "(fn/ ()/ =>/ Array.sub (Array.sub/ ((fn/ (a,b)/ =>/ a) (_),/ IntInf.toInt (integer'_of'_nat (_))), Word64.toInt (_)))"

definition length_u64_code' where
  [symmetric, code]: \<open>length_u64_code' = length_u64_code\<close>

code_printing constant length_u64_code' \<rightharpoonup> (SML_imp)
   "(fn/ ()/ =>/ Uint64.fromFixedInt (Array.length (_)))"

code_printing constant arl_get_u \<rightharpoonup> (SML) "(fn/ ()/ =>/ Array.sub/ ((fn/ (a,b)/ =>/ a) ((_)),/ Word32.toInt ((_))))"

definition uint32_of_uint64' where
  [symmetric, code]: \<open>uint32_of_uint64' = uint32_of_uint64\<close>

code_printing constant uint32_of_uint64' \<rightharpoonup> (SML_imp)
   "Word32.fromLargeWord (_)"

lemma arl_set_u64_code[code]: \<open>arl_set_u64 a i x =
   Array_upd_u64 i x (fst a) \<bind> (\<lambda>b. return (b, (snd a)))\<close>
  unfolding arl_set_u64_def arl_set_def heap_array_set'_u64_def arl_set'_u64_def
     heap_array_set_u64_def Array.upd'_def Array_upd_u64_def
  by (cases a) (auto simp: nat_of_uint64_code[symmetric])

lemma arl_set_u_code[code]: \<open>arl_set_u a i x =
   Array_upd_u i x (fst a) \<bind> (\<lambda>b. return (b, (snd a)))\<close>
  unfolding arl_set_u_def arl_set_def heap_array_set'_u64_def arl_set'_u_def
     heap_array_set_u_def Array.upd'_def Array_upd_u_def
  by (cases a) (auto simp: nat_of_uint64_code[symmetric])

definition arl_get_u64' where
  [symmetric, code]: \<open>arl_get_u64' = arl_get_u64\<close>

code_printing constant arl_get_u64' \<rightharpoonup> (SML)
"(fn/ ()/ =>/ Array.sub/ ((fn (a,b) => a) (_),/ Word64.toInt (_)))"

(*TODO this is a copy paste because of the order of the merge *)
code_printing code_module "Uint64" \<rightharpoonup> (SML) \<open>(* Test that words can handle numbers between 0 and 63 *)
val _ = if 6 <= Word.wordSize then () else raise (Fail ("wordSize less than 6"));

structure Uint64 : sig
  eqtype uint64;
  val zero : uint64;
  val one : uint64;
  val fromInt : IntInf.int -> uint64;
  val toInt : uint64 -> IntInf.int;
  val toFixedInt : uint64 -> Int.int;
  val toLarge : uint64 -> LargeWord.word;
  val fromLarge : LargeWord.word -> uint64
  val fromFixedInt : Int.int -> uint64
  val plus : uint64 -> uint64 -> uint64;
  val minus : uint64 -> uint64 -> uint64;
  val times : uint64 -> uint64 -> uint64;
  val divide : uint64 -> uint64 -> uint64;
  val modulus : uint64 -> uint64 -> uint64;
  val negate : uint64 -> uint64;
  val less_eq : uint64 -> uint64 -> bool;
  val less : uint64 -> uint64 -> bool;
  val notb : uint64 -> uint64;
  val andb : uint64 -> uint64 -> uint64;
  val orb : uint64 -> uint64 -> uint64;
  val xorb : uint64 -> uint64 -> uint64;
  val shiftl : uint64 -> IntInf.int -> uint64;
  val shiftr : uint64 -> IntInf.int -> uint64;
  val shiftr_signed : uint64 -> IntInf.int -> uint64;
  val set_bit : uint64 -> IntInf.int -> bool -> uint64;
  val test_bit : uint64 -> IntInf.int -> bool;
end = struct

type uint64 = Word64.word;

val zero = (0wx0 : uint64);

val one = (0wx1 : uint64);

fun fromInt x = Word64.fromLargeInt (IntInf.toLarge x);

fun toInt x = IntInf.fromLarge (Word64.toLargeInt x);

fun toFixedInt x = Word64.toInt x;

fun fromLarge x = Word64.fromLarge x;

fun fromFixedInt x = Word64.fromInt x;

fun toLarge x = Word64.toLarge x;

fun plus x y = Word64.+(x, y);

fun minus x y = Word64.-(x, y);

fun negate x = Word64.~(x);

fun times x y = Word64.*(x, y);

fun divide x y = Word64.div(x, y);

fun modulus x y = Word64.mod(x, y);

fun less_eq x y = Word64.<=(x, y);

fun less x y = Word64.<(x, y);

fun set_bit x n b =
  let val mask = Word64.<< (0wx1, Word.fromLargeInt (IntInf.toLarge n))
  in if b then Word64.orb (x, mask)
     else Word64.andb (x, Word64.notb mask)
  end

fun shiftl x n =
  Word64.<< (x, Word.fromLargeInt (IntInf.toLarge n))

fun shiftr x n =
  Word64.>> (x, Word.fromLargeInt (IntInf.toLarge n))

fun shiftr_signed x n =
  Word64.~>> (x, Word.fromLargeInt (IntInf.toLarge n))

fun test_bit x n =
  Word64.andb (x, Word64.<< (0wx1, Word.fromLargeInt (IntInf.toLarge n))) <> Word64.fromInt 0

val notb = Word64.notb

fun andb x y = Word64.andb(x, y);

fun orb x y = Word64.orb(x, y);

fun xorb x y = Word64.xorb(x, y);

end (*struct Uint64*)
\<close>
export_code IsaSAT_code checking SML_imp

code_printing constant \<comment> \<open>print with line break\<close>
  println_string \<rightharpoonup> (SML) "ignore/ (print/ ((_) ^ \"\\n\"))"

export_code IsaSAT_code
    int_of_integer
    integer_of_int
    integer_of_nat
    nat_of_integer
    uint32_of_nat
    Version.version
  in SML_imp module_name SAT_Solver file_prefix "IsaSAT_solver"

external_file \<open>code/Unsynchronized.sml\<close>
external_file \<open>code/IsaSAT.mlb\<close>
external_file \<open>code/IsaSAT.sml\<close>
external_file \<open>code/dimacs_parser.sml\<close>


compile_generated_files _
  external_files
    \<open>code/IsaSAT.mlb\<close>
    \<open>code/Unsynchronized.sml\<close>
    \<open>code/IsaSAT.sml\<close>
    \<open>code/dimacs_parser.sml\<close>
  where \<open>fn dir =>
    let
      val exec = Generated_Files.execute (Path.append dir (Path.basic "code"));
      val _ = exec \<open>rename file\<close> "mv IsaSAT_solver.ML IsaSAT_solver.sml"
      val _ =
        exec \<open>Copy files\<close>
          ("cp IsaSAT_solver.sml " ^
            ((File.bash_path \<^path>\<open>$ISAFOL\<close>) ^ "/Weidenbach_Book/code/IsaSAT_solver.sml"));
      val _ =
        exec \<open>Compilation\<close>
          (File.bash_path \<^path>\<open>$ISABELLE_MLTON\<close> ^
            " -const 'MLton.safe false' -verbose 1 -default-type int64 -output IsaSAT " ^
            " -codegen native -inline 700 -cc-opt -O3 IsaSAT.mlb");
      val _ =
        exec \<open>Copy binary files\<close>
          ("cp IsaSAT " ^
            File.bash_path \<^path>\<open>$ISAFOL\<close> ^ "/Weidenbach_Book/code/");
    in () end\<close>


export_code IsaSAT_bounded_code
    int_of_integer
    integer_of_int
    integer_of_nat
    nat_of_integer
    uint32_of_nat
    Version.version
  in SML_imp module_name SAT_Solver file_prefix "IsaSAT_solver_bounded"

compile_generated_files _
  external_files
    \<open>code/IsaSAT_bounded.mlb\<close>
    \<open>code/Unsynchronized.sml\<close>
    \<open>code/IsaSAT_bounded.sml\<close>
    \<open>code/dimacs_parser.sml\<close>
  where \<open>fn dir =>
    let
      val exec = Generated_Files.execute (Path.append dir (Path.basic "code"));
      val _ = exec \<open>rename file\<close> "mv IsaSAT_solver_bounded.ML IsaSAT_solver_bounded.sml"
      val _ =
        exec \<open>Copy files\<close>
          ("cp IsaSAT_solver_bounded.sml " ^
   ((File.bash_path \<^path>\<open>$ISAFOL\<close>) ^ "/Weidenbach_Book/code/IsaSAT_solver_bounded.sml"));
      val _ =
        exec \<open>Compilation\<close>
          (File.bash_path \<^path>\<open>$ISABELLE_MLTON\<close> ^
            " -const 'MLton.safe false' -verbose 1 -default-type int64 -output IsaSAT_bounded " ^
            " -codegen native -inline 700 -cc-opt -O3 IsaSAT_bounded.mlb");
      val _ =
        exec \<open>Copy binary files\<close>
          ("cp IsaSAT_bounded " ^
            File.bash_path \<^path>\<open>$ISAFOL\<close> ^ "/Weidenbach_Book/code/");
    in () end\<close>


end