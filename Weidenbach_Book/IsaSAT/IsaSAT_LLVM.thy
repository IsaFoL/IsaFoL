theory IsaSAT_LLVM
  imports
    IsaSAT_Print_LLVM
    IsaSAT_CDCL_LLVM
    IsaSAT_Initialisation_LLVM
    IsaSAT_Restart_Simp_LLVM
    Version
    IsaSAT_Defs
begin

hide_const (open)array_assn

hide_const (open)IICF_Multiset.mset_rel
hide_const (open) NEMonad.ASSERT NEMonad.RETURN

lemma convert_state_hnr:
  \<open>(uncurry (Mreturn oo (\<lambda>_ S. S)), uncurry (RETURN oo convert_state))
   \<in> ghost_assn\<^sup>k *\<^sub>a (isasat_init_assn)\<^sup>d \<rightarrow>\<^sub>a
     isasat_init_assn\<close>
  unfolding convert_state_def
  by sepref_to_hoare vcg

declare convert_state_hnr[sepref_fr_rules]

chapter \<open>Code of Full IsaSAT\<close>

abbreviation  model_stat_assn where
  \<open>model_stat_assn \<equiv> bool1_assn \<times>\<^sub>a (arl64_assn unat_lit_assn) \<times>\<^sub>a isasat_stats_assn\<close>

abbreviation model_stat_assn\<^sub>0 ::
    \<open>bool \<times>
     nat literal list \<times>
     isasat_stats
     \<Rightarrow> 1 word \<times>
       (64 word \<times> 64 word \<times> 32 word ptr) \<times>
       _
       \<Rightarrow> llvm_amemory \<Rightarrow> bool\<close>
where
  \<open>model_stat_assn\<^sub>0 \<equiv> bool1_assn \<times>\<^sub>a (al_assn unat_lit_assn) \<times>\<^sub>a isasat_stats_assn\<close>

abbreviation lits_with_max_assn :: \<open>nat multiset
     \<Rightarrow> (64 word \<times> 64 word \<times> 32 word ptr) \<times> 32 word \<Rightarrow> llvm_amemory \<Rightarrow> bool\<close> where
  \<open>lits_with_max_assn \<equiv> hr_comp (arl64_assn atom_assn \<times>\<^sub>a uint32_nat_assn) lits_with_max_rel\<close>

abbreviation lits_with_max_assn\<^sub>0 :: \<open>nat multiset
     \<Rightarrow> (64 word \<times> 64 word \<times> 32 word ptr) \<times> 32 word \<Rightarrow> llvm_amemory \<Rightarrow> bool\<close> where
  \<open>lits_with_max_assn\<^sub>0 \<equiv> hr_comp (al_assn atom_assn \<times>\<^sub>a unat32_assn) lits_with_max_rel\<close>

lemma lits_with_max_assn_alt_def: \<open>lits_with_max_assn = hr_comp (arl64_assn atom_assn \<times>\<^sub>a uint32_nat_assn)
          (lits_with_max_rel O \<langle>nat_rel\<rangle>mset_rel)\<close>
proof -
  have 1: \<open>(lits_with_max_rel O \<langle>nat_rel\<rangle>mset_rel) = lits_with_max_rel\<close>
    by (auto simp: mset_rel_def  p2rel_def rel2p_def[abs_def] br_def
         rel_mset_def lits_with_max_rel_def list_rel_def list_all2_op_eq_map_right_iff' list.rel_eq)
  show ?thesis
    unfolding 1
    by auto
qed

lemma tuple15_rel_Id: \<open>(\<langle>Id, Id, Id, nat_rel, \<langle>\<langle>Id\<rangle>list_rel\<rangle>list_rel, Id, \<langle>bool_rel\<rangle>list_rel,nat_rel,
   Id, Id, Id, Id, Id, Id, Id\<rangle>tuple15_rel) = Id\<close>
  apply (standard; standard)
  apply (case_tac x)
  apply (auto simp: hr_comp_def[abs_def]  tuple15_rel_def split: tuple15.splits)
  done

lemma init_state_wl_D'_code_isasat: \<open>hr_comp isasat_init_assn
  (\<langle>Id, Id, Id, nat_rel, \<langle>\<langle>Id\<rangle>list_rel\<rangle>list_rel, Id, \<langle>bool_rel\<rangle>list_rel,nat_rel,
  Id, Id, Id, Id, Id, Id, Id\<rangle>tuple15_rel) = isasat_init_assn\<close>
  unfolding tuple15_rel_Id
  by (auto simp:  split: tuple15.splits)

definition split_trail where \<open>split_trail x =x\<close>

sepref_def split_trail_impl
  is \<open>RETURN o split_trail\<close>
  :: \<open>trail_pol_fast_assn\<^sup>d \<rightarrow>\<^sub>a arl64_assn unat_lit_assn \<times>\<^sub>a larray64_assn (tri_bool_assn) \<times>\<^sub>a
    larray64_assn uint32_nat_assn \<times>\<^sub>a
    larray64_assn sint64_nat_assn \<times>\<^sub>a uint32_nat_assn \<times>\<^sub>a
  arl64_assn uint32_nat_assn\<close>
  unfolding trail_pol_fast_assn_def split_trail_def
  by sepref

lemma extract_model_of_state_stat_alt_def:
  \<open>RETURN o extract_model_of_state_stat = (\<lambda>S. case S of Tuple17 MM' N' D' j W' vm clvls cach lbd
    outl stats
    heur vdom lcount opts old_arena occs \<Rightarrow>
    do {_ \<leftarrow> print_trail2 (MM');
        (M,M') \<leftarrow> RETURN (split_trail MM');
        mop_free M'; mop_free N'; mop_free D'; mop_free j; mop_free W'; mop_free vm;
         mop_free clvls;
         mop_free cach; mop_free lbd; mop_free outl; mop_free heur;
         mop_free vdom; mop_free opts;
         mop_free old_arena; mop_free lcount; mop_free occs;
        RETURN (False, M, stats)
     })\<close>
  by (auto simp: extract_model_of_state_stat_def mop_free_def print_trail2_def split_trail_def
    intro!: ext split: isasat_int_splits)

schematic_goal mk_free_lbd_assn[sepref_frame_free_rules]: \<open>MK_FREE aivdom_assn ?fr\<close>
  unfolding aivdom_assn_def code_hider_assn_def by synthesize_free+

sepref_def extract_model_of_state_stat
  is \<open>RETURN o extract_model_of_state_stat\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a model_stat_assn\<close>
  supply [[goals_limit=1]]
  unfolding extract_model_of_state_stat_alt_def
    trail_pol_fast_assn_def
  by sepref

lemma extract_state_stat_alt_def:
  \<open>RETURN o extract_state_stat = (\<lambda>S. case S of Tuple17 M N' D' j W' vm clvls cach lbd outl stats
       heur vdom lcount opts old_arena occs \<Rightarrow>
     do {
        mop_free M; mop_free N'; mop_free D'; mop_free j; mop_free W'; mop_free vm;
         mop_free clvls;
         mop_free cach; mop_free lbd; mop_free outl; mop_free heur;
         mop_free vdom; mop_free opts;
         mop_free old_arena; mop_free lcount;  mop_free occs;
        RETURN (True, [], stats)})\<close>
  by (auto simp: extract_state_stat_def mop_free_def split: isasat_int_splits intro!: ext)

sepref_def extract_state_stat
  is \<open>RETURN o extract_state_stat\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a model_stat_assn\<close>
  supply [[goals_limit=1]]
  unfolding extract_state_stat_alt_def isasat_bounded_assn_def
    al_fold_custom_empty[where 'l=64]
  by sepref

sepref_def empty_conflict_code'
  is \<open>uncurry0 (empty_conflict_code)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a model_stat_assn\<close>
  unfolding empty_conflict_code_def
  apply (rewrite in \<open>let _ =  \<hole> in _\<close> al_fold_custom_empty[where 'l=64])
  apply (rewrite in \<open>let _ =  \<hole> in _\<close> annotate_assn[where A=\<open>arl64_assn unat_lit_assn\<close>])
  by sepref

declare empty_conflict_code'.refine[sepref_fr_rules]

sepref_def  empty_init_code'
  is \<open>uncurry0 (RETURN empty_init_code)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a model_stat_assn\<close>
  unfolding empty_init_code_def al_fold_custom_empty[where 'l=64]
  apply (rewrite in \<open>RETURN (_, \<hole>,_)\<close> annotate_assn[where A=\<open>arl64_assn unat_lit_assn\<close>])
  by sepref

sepref_register init_dt_wl_heur_full

sepref_register to_init_state from_init_state get_conflict_wl_is_None_init
  init_dt_wl_heur

sepref_def isasat_fast_bound_impl
  is \<open>uncurry0 (RETURN isasat_fast_bound)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a sint64_nat_assn\<close>
  unfolding isasat_fast_bound_alt_def
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

lemma isasat_fast_init_alt_def:
  \<open>RETURN o isasat_fast_init = (\<lambda>S. do{
     let n = length (get_clauses_wl_heur_init S);
     let lcountUE = clss_size_lcountUE (get_learned_count_init S);
     let lcount = clss_size_lcount (get_learned_count_init S);
     let lcountUEk = clss_size_lcountUEk (get_learned_count_init S);
     let lcountUS = clss_size_lcountUS (get_learned_count_init S);
     let lcountU0 = clss_size_lcountU0 (get_learned_count_init S);
     ASSERT(18446744073709551615 \<in> unats LENGTH(64));
     c \<leftarrow> RETURN 18446744073709551615;
     if \<not>(n \<le> isasat_fast_bound \<and> lcount < c - lcountUE) then RETURN False
     else do {
        ASSERT(lcount + lcountUE \<in> unats LENGTH(64));
        a  \<leftarrow> RETURN (lcount + lcountUE);
        if \<not>a < c - lcountUS then RETURN False
        else do {
          ASSERT(a +  lcountUS \<in> unats LENGTH(64));
          a \<leftarrow> RETURN (a + lcountUS);
          if \<not>a < c - lcountU0 then RETURN False
          else do {
            ASSERT(a +  lcountU0 \<in> unats LENGTH(64));
            a \<leftarrow> RETURN (a + lcountU0);
            if \<not>a < c - lcountUEk then RETURN False
            else do {
            ASSERT(a +  lcountUEk \<in> unats LENGTH(64));
            a \<leftarrow> RETURN (a + lcountUEk);
              RETURN(a < c)
            }
         }

      }
   }})\<close>
  by (auto simp: isasat_fast_init_def uint64_max_def uint32_max_def isasat_fast_bound_def max_uint_def
    clss_size_lcountUS_def clss_size_lcountUE_def clss_size_lcount_def learned_clss_count_init_def unats_def
    clss_size_lcountU0_def clss_size_lcountUEk_def Let_def bind_ASSERT_eq_if split: if_splits intro!: ASSERT_leI
  intro!: ext)

lemma isasat_fast_init_codeI: \<open>(aa :: 64 word, b) \<in> unat_rel64 \<Longrightarrow>  b \<le> 18446744073709551615\<close>
  using unat_lt_max_unat[of aa]
  by (auto simp: unat_rel_def unat.rel_def br_def max_unat_def)

sepref_def isasat_fast_init_code
  is \<open>RETURN o isasat_fast_init\<close>
  :: \<open>isasat_init_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  supply [[goals_limit=1]]
  supply [sepref_bounds_simps del] = max_snat_def max_unat_def max_sint_def min_sint_def
  supply [intro] = isasat_fast_init_codeI
  unfolding isasat_fast_init_alt_def  if_not_swap isasat_fast_init_def
    clss_size_lcountUS_st_init_def[symmetric]
    clss_size_lcountUEk_st_init_def[symmetric]
    clss_size_lcountUE_st_init_def[symmetric] full_arena_length_st_init_def[symmetric]
    clss_size_lcount_st_init_def[symmetric]
    clss_size_lcountU0_st_init_def[symmetric]
  apply (rewrite at \<open>RETURN \<hole>\<close> unat_const_fold[where 'a=64])
  by sepref

sepref_register
   cdcl_twl_stgy_restart_prog_wl_heur

declare init_state_wl_D'_code.refine[FCOMP init_state_wl_D'[unfolded convert_fref],
  unfolded lits_with_max_assn_alt_def[symmetric] init_state_wl_heur_fast_def[symmetric],
  unfolded init_state_wl_D'_code_isasat, sepref_fr_rules]

lemma [sepref_fr_rules]: \<open>(init_state_wl_D'_code, init_state_wl_heur_fast)
\<in> [\<lambda>x. distinct_mset x \<and>
       (\<forall>L\<in>#\<L>\<^sub>a\<^sub>l\<^sub>l x. nat_of_lit L \<le> uint32_max)]\<^sub>a lits_with_max_assn\<^sup>k \<rightarrow> isasat_init_assn\<close>
  using init_state_wl_D'_code.refine[FCOMP init_state_wl_D'[unfolded convert_fref]]
  unfolding lits_with_max_assn_alt_def[symmetric] init_state_wl_D'_code_isasat
    init_state_wl_heur_fast_def
  by auto


definition ghost_assn where \<open>ghost_assn = hr_comp unit_assn virtual_copy_rel\<close>

lemma [sepref_fr_rules]: \<open>(Mreturn o (\<lambda>_. ()), RETURN o virtual_copy) \<in> lits_with_max_assn\<^sup>k \<rightarrow>\<^sub>a ghost_assn\<close>
proof -
  have [simp]: \<open>(\<lambda>s. (\<exists>xa. (\<up>(xa = x)) s)) = (\<up>True)\<close> for s :: \<open>'b::sep_algebra\<close> and x :: 'a
    by (auto simp: pred_lift_extract_simps)
  show ?thesis
    unfolding virtual_copy_def ghost_assn_def virtual_copy_rel_def
    apply sepref_to_hoare
    apply vcg'
    apply (auto simp: ENTAILS_def hr_comp_def snat_rel_def pure_true_conv)
    apply (rule Defer_Slot.remove_slot)
    done
qed

sepref_register virtual_copy empty_conflict_code empty_init_code
  isasat_fast_init is_failed_heur_init
  extract_model_of_state_stat extract_state_stat
  isasat_information_banner
  finalise_init_code
  IsaSAT_Initialisation.rewatch_heur_st_fast
  get_conflict_wl_is_None_heur
  cdcl_twl_stgy_prog_bounded_wl_heur
  get_conflict_wl_is_None_heur_init
  convert_state

lemma isasat_information_banner_alt_def:
  \<open>isasat_information_banner S =
    RETURN (())\<close>
  by (auto simp: isasat_information_banner_def)

schematic_goal mk_free_ghost_assn[sepref_frame_free_rules]: \<open>MK_FREE ghost_assn ?fr\<close>
  unfolding ghost_assn_def
  by synthesize_free

sepref_def IsaSAT_code
  is \<open>uncurry IsaSAT_bounded_heur\<close>
  :: \<open>opts_assn\<^sup>d *\<^sub>a (clauses_ll_assn)\<^sup>k \<rightarrow>\<^sub>a bool1_assn \<times>\<^sub>a model_stat_assn\<close>
  supply [[goals_limit=1]] isasat_fast_init_def[simp]
  unfolding IsaSAT_bounded_heur_def empty_conflict_def[symmetric]
    get_conflict_wl_is_None (*extract_model_of_state_def[symmetric]*)
    (*extract_stats_def[symmetric]*) init_dt_wl_heur_b_def[symmetric]
    (*length_get_clauses_wl_heur_init_def[symmetric]*)
    init_dt_step_wl_heur_unb_def[symmetric] init_dt_wl_heur_unb_def[symmetric]
    length_0_conv[symmetric]  op_list_list_len_def[symmetric]
    isasat_information_banner_alt_def
  supply get_conflict_wl_is_None_heur_init_def[simp]
  supply  get_conflict_wl_is_None_def[simp]
   option.splits[split]
(*   extract_stats_def[simp del]*)
  apply (rewrite at \<open>extract_atms_clss _ \<hole>\<close> op_extract_list_empty_def[symmetric])
  apply (rewrite at \<open>extract_atms_clss _ \<hole>\<close> op_extract_list_empty_def[symmetric])
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref


sepref_register print_forward_rounds print_forward_subsumed print_forward_strengthened

abbreviation (input) C_bool_to_bool :: \<open>8 word \<Rightarrow> bool\<close> where
  \<open>C_bool_to_bool g \<equiv> g \<noteq> 0\<close>

definition IsaSAT_bounded_heur_wrapper :: \<open>8 word \<Rightarrow> 8 word \<Rightarrow> 8 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> nat \<Rightarrow>
  8 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 8 word \<Rightarrow> _ \<Rightarrow> (nat) nres\<close>where
  \<open>IsaSAT_bounded_heur_wrapper red res unbdd mini res1 res2 target_option fema sema units subsume C = do {
      let opts = IsaOptions (C_bool_to_bool red) (C_bool_to_bool res)
         (C_bool_to_bool unbdd) mini res1 res2
         (if target_option = 2 then TARGET_ALWAYS else if target_option = 0 then TARGET_NEVER else TARGET_STABLE_ONLY)
         fema sema units (C_bool_to_bool subsume);
      (b, (b', _, stats)) \<leftarrow> IsaSAT_bounded_heur (opts) C;
      let (_ :: unit) = print_propa (stats_propagations stats);
      let (_ :: unit) = print_confl (stats_conflicts stats);
      let (_ :: unit) = print_dec (stats_decisions stats);
      let (_ :: unit) = print_res (stats_restarts stats) (stats_conflicts stats);
      let (_ :: unit) = print_lres (stats_reductions stats) (stats_conflicts stats);
      let (_ :: unit) = print_uset (stats_fixed stats);
      let (_ :: unit) = print_gcs (stats_gcs stats) (stats_conflicts stats);
      let (_ :: unit) = print_irred_clss (stats_irred stats);
      let (_ :: unit) = print_binary_unit (stats_binary_units stats);
      let (_ :: unit) = print_binary_red_removed (stats_binary_removed stats);
      let (_ :: unit) = print_purelit_elim (stats_pure_lits_removed stats);
      let (_ :: unit) = print_purelit_rounds (stats_pure_lits_rounds stats) (stats_conflicts stats);
      let (_ :: unit) = print_forward_rounds (stats_forward_rounds stats) (stats_conflicts stats);
      let (_ :: unit) = print_forward_tried (stats_forward_tried stats) (stats_forward_rounds stats);
      let (_ :: unit) = print_forward_subsumed (stats_forward_subsumed stats) (stats_forward_tried stats);
      let (_ :: unit) = print_forward_strengthened (stats_forward_strengthened stats) (stats_forward_tried stats);
      RETURN ((if b then 2 else 0) + (if b' then 1 else 0))
  }\<close>

text \<open>
  The calling convention of LLVM and clang is not the same, so returning the model is
  currently unsupported. We return only the flags (as ints, not as bools) and the
  statistics.
\<close>
sepref_register IsaSAT_bounded_heur default_opts

abbreviation bool_C_assn where
   \<open>bool_C_assn \<equiv> (word_assn' (TYPE(8)))\<close>

sepref_def IsaSAT_wrapped
  is \<open>uncurry11 IsaSAT_bounded_heur_wrapper\<close>
  :: \<open>bool_C_assn\<^sup>k *\<^sub>a bool_C_assn\<^sup>k *\<^sub>a bool_C_assn\<^sup>k *\<^sub>a word64_assn\<^sup>k *\<^sub>a word64_assn\<^sup>k *\<^sub>a
      (snat_assn' (TYPE(64)))\<^sup>k *\<^sub>a bool_C_assn\<^sup>k *\<^sub>a word64_assn\<^sup>k *\<^sub>a word64_assn\<^sup>k *\<^sub>a
      word64_assn\<^sup>k *\<^sub>a bool_C_assn\<^sup>k *\<^sub>a (clauses_ll_assn)\<^sup>k \<rightarrow>\<^sub>a sint64_nat_assn\<close>
  supply [[goals_limit=1]] if_splits[split]
  unfolding IsaSAT_bounded_heur_wrapper_def
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

text \<open>The setup to transmit the version is a bit complicated, because
  Isabelle does not support direct export of string
  literals. Therefore, we actually convert the version to an array
  chars (more precisely, of machine words -- ended with 0) that can be read
  and printed by the C layer. Note the conversion must be automatic, because
  the version depends on the underlying git repository, hence the call to auto.
\<close>
function array_of_version where
  \<open>array_of_version i str arr =
    (if i \<ge> length str then arr
    else array_of_version (i+1) str (arr[i := str ! i]))\<close>
  by pat_completeness auto
termination
  apply (relation \<open>measure (\<lambda>(i,str, arr). length str - i)\<close>)
  apply auto
  done

text \<open>Using this as version number makes our work on the cluster easier and makes the version checking
  slightly easier (because the git hash is never up-to-date).\<close>
definition internal_version :: \<open>string\<close> where \<open>internal_version = ''1f''\<close>

sepref_definition llvm_version
  is \<open>uncurry0 (RETURN (
        let str = map (nat_of_integer o (of_char :: _ \<Rightarrow> integer)) (internal_version @ ''-'' @ String.explode Version.version) @ [0] in
        array_of_version 0 str (replicate (length str) 0)))\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a IICF_Array.array_assn sint32_nat_assn\<close>
  supply[[goals_limit=1]]
  unfolding Version.version_def String.explode_code internal_version_def
    String.asciis_of_Literal
  apply (auto simp: String.asciis_of_Literal of_char_of char_of_char nat_of_integer_def
    simp del: list_update.simps replicate.simps)
  apply (annot_snat_const \<open>TYPE(32)\<close>)
  unfolding array_fold_custom_replicate
  unfolding hf_pres.simps[symmetric]
  by sepref

experiment
begin
  lemmas [llvm_code] = llvm_version_def

  lemmas [llvm_inline] =
    unit_propagation_inner_loop_body_wl_fast_heur_code_def
    FOCUSED_MODE_def DEFAULT_INIT_PHASE_def STABLE_MODE_def
    find_unwatched_wl_st_heur_fast_code_def
    update_clause_wl_fast_code_def

lemmas [unfolded inline_direct_return_node_case, llvm_code] = units_since_last_GC_st_code_def[unfolded read_all_st_code_def]
lemmas [llvm_code del] = units_since_last_GC_st_code_def

export_llvm
    llvm_version is \<open>STRING_VERSION llvm_version()\<close>
    IsaSAT_code
    IsaSAT_wrapped (*is \<open>int64_t IsaSAT_wrapped(CBOOL, CBOOL, CBOOL,
        int64_t, int64_t, int64_t, CBOOL, int64_t, int64_t, int64_t, CLAUSES)\<close>*)
    IsaSAT_Profile_PROPAGATE is \<open>PROFILE_CST IsaSAT_Profile_PROPAGATE()\<close>
    IsaSAT_Profile_REDUCE is \<open>PROFILE_CST IsaSAT_Profile_REDUCE()\<close>
    IsaSAT_Profile_GC is \<open>PROFILE_CST IsaSAT_Profile_GC()\<close>
    IsaSAT_Profile_ANALYZE is \<open>PROFILE_CST IsaSAT_Profile_ANALYZE()\<close>
    IsaSAT_Profile_MINIMIZATION is \<open>PROFILE_CST IsaSAT_Profile_MINIMIZATION()\<close>
    IsaSAT_Profile_INITIALISATION is \<open>PROFILE_CST IsaSAT_Profile_INITIALISATION()\<close>
    IsaSAT_Profile_SUBSUMPTION is \<open>PROFILE_CST IsaSAT_Profile_SUBSUMPTION()\<close>
    IsaSAT_Profile_PURE_LITERAL is \<open>PROFILE_CST IsaSAT_Profile_PURE_LITERAL()\<close>
    IsaSAT_Profile_BINARY_SIMP is \<open>PROFILE_CST IsaSAT_Profile_BINARY_SIMP()\<close>
  defines \<open>
     typedef int8_t CBOOL;
     typedef int8_t PROFILE_CST;
     typedef struct {int64_t size; struct {int64_t used; uint32_t *clause;};} CLAUSE;
     typedef struct {int64_t num_clauses; CLAUSE *clauses;} CLAUSES;
     typedef int32_t* STRING_VERSION;
  \<close>
  file \<open>code/src/isasat_restart.ll\<close>

end

end
