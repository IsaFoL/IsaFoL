theory IsaSAT_LLVM
  imports
    IsaSAT_CDCL_LLVM
    IsaSAT_Initialisation_LLVM
    IsaSAT_Restart_Simp_LLVM
    Version
    IsaSAT
begin
hide_const (open)array_assn

hide_const (open)IICF_Multiset.mset_rel

chapter \<open>Code of Full IsaSAT\<close>

abbreviation  model_stat_assn where
  \<open>model_stat_assn \<equiv> bool1_assn \<times>\<^sub>a (arl64_assn unat_lit_assn) \<times>\<^sub>a stats_int_assn\<close>

abbreviation model_stat_assn\<^sub>0 ::
    \<open>bool \<times>
     nat literal list \<times>
     64 word \<times>
     64 word \<times> 64 word \<times> 64 word \<times> 64 word \<times> 64 word \<times> 64 word \<times> 64 word\<times> 64 word \<times>  64 word\<times> 64 word\<times>  64 word\<times> 64 word \<times> ema
     \<Rightarrow> 1 word \<times>
       (64 word \<times> 64 word \<times> 32 word ptr) \<times>
       64 word \<times>
       64 word \<times> 64 word \<times> 64 word \<times> 64 word \<times> 64 word \<times> 64 word \<times> 64 word\<times> 64 word \<times> 64 word\<times> 64 word\<times>  64 word\<times> 64 word\<times> ema
       \<Rightarrow> llvm_amemory \<Rightarrow> bool\<close>
where
  \<open>model_stat_assn\<^sub>0 \<equiv> bool1_assn \<times>\<^sub>a (al_assn unat_lit_assn) \<times>\<^sub>a stats_int_assn\<close>

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

definition model_assn where
  \<open>model_assn = hr_comp model_stat_assn model_stat_rel\<close>

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
  \<open>RETURN o extract_model_of_state_stat = (\<lambda>S. case S of IsaSAT_int MM' N' D' j W' vm clvls cach lbd
    outl stats
    heur vdom lcount opts old_arena \<Rightarrow>
    do {_ \<leftarrow> print_trail2 (MM');
        (M,M') \<leftarrow> RETURN (split_trail MM');
        mop_free M'; mop_free N'; mop_free D'; mop_free j; mop_free W'; mop_free vm;
         mop_free clvls;
         mop_free cach; mop_free lbd; mop_free outl; mop_free heur;
         mop_free vdom; mop_free opts;
         mop_free old_arena; mop_free lcount;
        RETURN (False, M, get_content stats)
     })\<close>
  by (auto simp: extract_model_of_state_stat_def mop_free_def print_trail2_def split_trail_def
    intro!: ext split: isasat_int.splits)

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
  \<open>RETURN o extract_state_stat = (\<lambda>S. case S of IsaSAT_int M N' D' j W' vm clvls cach lbd outl stats
       heur vdom lcount opts old_arena \<Rightarrow>
     do {
        mop_free M; mop_free N'; mop_free D'; mop_free j; mop_free W'; mop_free vm;
         mop_free clvls;
         mop_free cach; mop_free lbd; mop_free outl; mop_free heur;
         mop_free vdom; mop_free opts;
         mop_free old_arena; mop_free lcount;
        RETURN (True, [], get_content stats)})\<close>
  by (auto simp: extract_state_stat_def mop_free_def split: isasat_int.splits intro!: ext)

sepref_def extract_state_stat
  is \<open>RETURN o extract_state_stat\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a model_stat_assn\<close>
  supply [[goals_limit=1]]
  unfolding extract_state_stat_alt_def isasat_bounded_assn_def
    al_fold_custom_empty[where 'l=64]
  by sepref

sepref_def IsaSAT_use_fast_mode_impl
  is \<open>uncurry0 (RETURN IsaSAT_use_fast_mode)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding IsaSAT_use_fast_mode_def
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

sepref_register to_init_state from_init_state get_conflict_wl_is_None_init extract_stats
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

lemma convert_state_hnr:
  \<open>(uncurry (Mreturn oo (\<lambda>_ S. S)), uncurry (RETURN oo convert_state))
   \<in> ghost_assn\<^sup>k *\<^sub>a (isasat_init_assn)\<^sup>d \<rightarrow>\<^sub>a
     isasat_init_assn\<close>
  unfolding convert_state_def
  by sepref_to_hoare vcg
declare convert_state_hnr[sepref_fr_rules]

schematic_goal mk_free_isasat_init_assn[sepref_frame_free_rules]: \<open>MK_FREE isasat_init_assn ?fr\<close>
  unfolding isasat_init_assn_def
  apply (rule tuple15_free)
  by synthesize_free+


sepref_def IsaSAT_code
  is \<open>uncurry IsaSAT_bounded_heur\<close>
  :: \<open>opts_assn\<^sup>d *\<^sub>a (clauses_ll_assn)\<^sup>k \<rightarrow>\<^sub>a bool1_assn \<times>\<^sub>a model_stat_assn\<close>
  supply [[goals_limit=1]] isasat_fast_init_def[simp]
  unfolding IsaSAT_bounded_heur_def empty_conflict_def[symmetric]
    get_conflict_wl_is_None extract_model_of_state_def[symmetric]
    extract_stats_def[symmetric] init_dt_wl_heur_b_def[symmetric]
    length_get_clauses_wl_heur_init_def[symmetric]
    init_dt_step_wl_heur_unb_def[symmetric] init_dt_wl_heur_unb_def[symmetric]
    length_0_conv[symmetric]  op_list_list_len_def[symmetric]
    isasat_information_banner_alt_def
  supply get_conflict_wl_is_None_heur_init_def[simp]
  supply  get_conflict_wl_is_None_def[simp]
   option.splits[split]
   extract_stats_def[simp del]
  apply (rewrite at \<open>extract_atms_clss _ \<hole>\<close> op_extract_list_empty_def[symmetric])
  apply (rewrite at \<open>extract_atms_clss _ \<hole>\<close> op_extract_list_empty_def[symmetric])
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

definition print_propa :: \<open>64 word \<Rightarrow> unit\<close> where
  \<open>print_propa _ = ()\<close>

definition print_confl :: \<open>64 word \<Rightarrow> unit\<close> where
  \<open>print_confl _ = ()\<close>

definition print_dec :: \<open>64 word \<Rightarrow> unit\<close> where
  \<open>print_dec _ = ()\<close>

definition print_res :: \<open>64 word \<Rightarrow> unit\<close> where
  \<open>print_res _ = ()\<close>

definition print_lres :: \<open>64 word \<Rightarrow> unit\<close> where
  \<open>print_lres _ = ()\<close>

definition print_uset :: \<open>64 word \<Rightarrow> unit\<close> where
  \<open>print_uset _ = ()\<close>

definition print_gcs :: \<open>64 word \<Rightarrow> unit\<close> where
  \<open>print_gcs _ = ()\<close>

definition print_binary_unit :: \<open>64 word \<Rightarrow> unit\<close> where
  \<open>print_binary_unit _ = ()\<close>

definition print_binary_red_removed :: \<open>64 word \<Rightarrow> unit\<close> where
  \<open>print_binary_red_removed _ = ()\<close>

definition print_purelit_elim :: \<open>64 word \<Rightarrow> unit\<close> where
  \<open>print_purelit_elim _ = ()\<close>

definition print_purelit_rounds :: \<open>64 word \<Rightarrow> unit\<close> where
  \<open>print_purelit_rounds _ = ()\<close>

definition print_lbds :: \<open>64 word \<Rightarrow> unit\<close> where
  \<open>print_lbds _ = ()\<close>

sepref_def print_propa_impl
  is \<open>RETURN o print_propa\<close>
  :: \<open>word_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding print_propa_def
  by sepref

sepref_def print_confl_impl
  is \<open>RETURN o print_confl\<close>
  :: \<open>word_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding print_confl_def
  by sepref

sepref_def print_dec_impl
  is \<open>RETURN o print_dec\<close>
  :: \<open>word_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding print_dec_def
  by sepref

sepref_def print_res_impl
  is \<open>RETURN o print_res\<close>
  :: \<open>word_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding print_res_def
  by sepref

sepref_def print_lres_impl
  is \<open>RETURN o print_lres\<close>
  :: \<open>word_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding print_lres_def
  by sepref

sepref_def print_uset_impl
  is \<open>RETURN o print_uset\<close>
  :: \<open>word_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding print_uset_def
  by sepref

definition print_irred_clss :: \<open>64 word \<Rightarrow> unit\<close> where
  \<open>print_irred_clss _ = ()\<close>

sepref_def print_gc_impl
  is \<open>RETURN o print_gcs\<close>
  :: \<open>word_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding print_gcs_def
  by sepref

sepref_def print_irred_clss_impl
  is \<open>RETURN o print_irred_clss\<close>
  :: \<open>word_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding print_irred_clss_def
  by sepref

sepref_def print_binary_unit_impl
  is \<open>RETURN o print_binary_unit\<close>
  :: \<open>word_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding print_binary_unit_def
  by sepref

sepref_def print_purelit_rounds_impl
  is \<open>RETURN o print_purelit_rounds\<close>
  :: \<open>word_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding print_purelit_rounds_def
  by sepref

sepref_def print_purelit_elim_impl
  is \<open>RETURN o print_purelit_elim\<close>
  :: \<open>word_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding print_purelit_elim_def
  by sepref

sepref_def print_binary_red_removed_impl
  is \<open>RETURN o print_binary_red_removed\<close>
  :: \<open>word_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn\<close>
  unfolding print_binary_red_removed_def
  by sepref

abbreviation (input) C_bool_to_bool :: \<open>8 word \<Rightarrow> bool\<close> where
  \<open>C_bool_to_bool g \<equiv> g \<noteq> 0\<close>

definition IsaSAT_bounded_heur_wrapper :: \<open>8 word \<Rightarrow> 8 word \<Rightarrow> 8 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> nat \<Rightarrow>
  8 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> _ \<Rightarrow> (nat) nres\<close>where
  \<open>IsaSAT_bounded_heur_wrapper red res unbdd mini res1 res2 target_option fema sema units C = do {
      let opts = IsaOptions (C_bool_to_bool red) (C_bool_to_bool res)
         (C_bool_to_bool unbdd) mini res1 res2
         (if target_option = 2 then 2 else if target_option = 0 then 0 else 1)
         fema sema units;
      (b, (b', (_, propa, confl, dec, res, lres, uset, gcs, _, irred_clss, binary_unit, binary_red_removed, purelit_elim, purelit_rounds, d))) \<leftarrow> IsaSAT_bounded_heur (opts) C;
      let _ = print_propa propa;
      let _ = print_confl confl;
      let _ = print_dec dec;
      let _ = print_res res;
      let _ = print_lres lres;
      let _ = print_uset uset;
      let _ = print_gcs gcs;
      let _ = print_irred_clss irred_clss;
      let _ = print_binary_unit binary_unit;
      let _ = print_binary_red_removed binary_red_removed;
      let _ = print_purelit_elim purelit_elim;
      let _ = print_purelit_rounds purelit_rounds;
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
  is \<open>uncurry10 IsaSAT_bounded_heur_wrapper\<close>
  :: \<open>bool_C_assn\<^sup>k *\<^sub>a bool_C_assn\<^sup>k *\<^sub>a bool_C_assn\<^sup>k *\<^sub>a word64_assn\<^sup>k *\<^sub>a word64_assn\<^sup>k *\<^sub>a
      (snat_assn' (TYPE(64)))\<^sup>k *\<^sub>a bool_C_assn\<^sup>k *\<^sub>a word64_assn\<^sup>k *\<^sub>a word64_assn\<^sup>k *\<^sub>a
      word64_assn\<^sup>k *\<^sub>a (clauses_ll_assn)\<^sup>k \<rightarrow>\<^sub>a sint64_nat_assn\<close>
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

sepref_definition llvm_version
  is \<open>uncurry0 (RETURN (
        let str = map (nat_of_integer o (of_char :: _ \<Rightarrow> integer)) (String.explode Version.version) @ [0] in
        array_of_version 0 str (replicate (length str) 0)))\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a array_assn sint32_nat_assn\<close>
  supply[[goals_limit=1]]
  unfolding Version.version_def String.explode_code
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
    NORMAL_PHASE_def DEFAULT_INIT_PHASE_def QUIET_PHASE_def
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
  defines \<open>
     typedef int8_t CBOOL;
     typedef int8_t PROFILE_CST;
     typedef struct {int64_t size; struct {int64_t used; uint32_t *clause;};} CLAUSE;
     typedef struct {int64_t num_clauses; CLAUSE *clauses;} CLAUSES;
   For those who don’t understand the reference this is satire coming from the comment on the Dropbox Launch post on HN in 2007 [0]  typedef int32_t* STRING_VERSION;
  \<close>
  file \<open>code/src/isasat_restart.ll\<close>

end

definition model_bounded_assn where
  \<open>model_bounded_assn =
   hr_comp (bool1_assn \<times>\<^sub>a model_stat_assn\<^sub>0)
   {((b, m), (b', m')). b=b' \<and> (\<not>b \<longrightarrow> (m,m') \<in> model_stat_rel)}\<close>

definition clauses_l_assn where
  \<open>clauses_l_assn = hr_comp (IICF_Array_of_Array_List.aal_assn unat_lit_assn)
    (list_mset_rel O \<langle>list_mset_rel\<rangle>mset_rel)\<close>

theorem IsaSAT_full_correctness:
  \<open>(uncurry IsaSAT_code, uncurry (\<lambda>_. model_if_satisfiable_bounded))
     \<in> [\<lambda>(_, a). (\<forall>C\<in>#a. \<forall>L\<in>#C. nat_of_lit L \<le> uint32_max)]\<^sub>a opts_assn\<^sup>d *\<^sub>a clauses_l_assn\<^sup>k \<rightarrow>
      model_bounded_assn\<close>
  using IsaSAT_code.refine[FCOMP IsaSAT_bounded_heur_model_if_sat'[unfolded convert_fref]]
  unfolding model_bounded_assn_def clauses_l_assn_def
  by auto

end