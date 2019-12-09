theory IsaSAT_LLVM
  imports  Version IsaSAT_CDCL_LLVM
    IsaSAT_Initialisation_LLVM Version IsaSAT
    IsaSAT_Restart_LLVM
begin

chapter \<open>Code of Full IsaSAT\<close>

abbreviation  model_stat_assn where
  \<open>model_stat_assn \<equiv> bool1_assn \<times>\<^sub>a (arl64_assn unat_lit_assn) \<times>\<^sub>a stats_assn\<close>

abbreviation  model_stat_assn\<^sub>0 ::
    "bool \<times>
     nat literal list \<times>
     64 word \<times>
     64 word \<times> 64 word \<times> 64 word \<times> 64 word \<times> 64 word \<times> 64 word \<times> 64 word
     \<Rightarrow> 1 word \<times>
       (64 word \<times> 64 word \<times> 32 word ptr) \<times>
       64 word \<times>
       64 word \<times> 64 word \<times> 64 word \<times> 64 word \<times> 64 word \<times> 64 word \<times> 64 word
       \<Rightarrow> llvm_amemory \<Rightarrow> bool"
where
  \<open>model_stat_assn\<^sub>0 \<equiv> bool1_assn \<times>\<^sub>a (al_assn unat_lit_assn) \<times>\<^sub>a stats_assn\<close>

abbreviation lits_with_max_assn :: \<open>nat multiset
     \<Rightarrow> (64 word \<times> 64 word \<times> 32 word ptr) \<times> 32 word \<Rightarrow> llvm_amemory \<Rightarrow> bool\<close> where
  \<open>lits_with_max_assn \<equiv> hr_comp (arl64_assn atom_assn \<times>\<^sub>a uint32_nat_assn) lits_with_max_rel\<close>

abbreviation lits_with_max_assn\<^sub>0 :: \<open>nat multiset
     \<Rightarrow> (64 word \<times> 64 word \<times> 32 word ptr) \<times> 32 word \<Rightarrow> llvm_amemory \<Rightarrow> bool\<close> where
  \<open>lits_with_max_assn\<^sub>0 \<equiv> hr_comp (al_assn atom_assn \<times>\<^sub>a unat32_assn) lits_with_max_rel\<close>

lemma lits_with_max_assn_alt_def: \<open>lits_with_max_assn = hr_comp (arl64_assn atom_assn \<times>\<^sub>a uint32_nat_assn)
          (lits_with_max_rel O \<langle>nat_rel\<rangle>IsaSAT_Initialisation.mset_rel)\<close>
proof -

  have 1: \<open>(lits_with_max_rel O \<langle>nat_rel\<rangle>IsaSAT_Initialisation.mset_rel) = lits_with_max_rel\<close>
    by (auto simp: mset_rel_def  p2rel_def rel2p_def[abs_def] br_def
         rel_mset_def lits_with_max_rel_def list_rel_def list_all2_op_eq_map_right_iff' list.rel_eq)
  show ?thesis
    unfolding 1
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

(*
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
*)

definition model_assn where
  \<open>model_assn = hr_comp model_stat_assn model_stat_rel\<close>

lemma extract_model_of_state_stat_alt_def:
  \<open>RETURN o extract_model_of_state_stat = (\<lambda>((M, M'), N', D', j, W', vm, clvls, cach, lbd,
    outl, stats,
    heur, vdom, avdom, lcount, opts, old_arena).
     do {mop_free M'; mop_free N'; mop_free D'; mop_free j; mop_free W'; mop_free vm;
         mop_free clvls;
         mop_free cach; mop_free lbd; mop_free outl; mop_free heur;
         mop_free vdom; mop_free avdom; mop_free opts;
         mop_free old_arena;
        RETURN (False, M, stats)
     })\<close>
  by (auto simp: extract_model_of_state_stat_def mop_free_def intro!: ext)

schematic_goal mk_free_lookup_clause_rel_assn[sepref_frame_free_rules]: "MK_FREE lookup_clause_rel_assn ?fr"
  unfolding conflict_option_rel_assn_def lookup_clause_rel_assn_def
  by (rule free_thms sepref_frame_free_rules)+ (* TODO: Write a method for that! *)

schematic_goal mk_free_trail_pol_fast_assn[sepref_frame_free_rules]: "MK_FREE conflict_option_rel_assn ?fr"  
  unfolding conflict_option_rel_assn_def
  by (rule free_thms sepref_frame_free_rules)+ (* TODO: Write a method for that! *)


schematic_goal mk_free_vmtf_remove_assn[sepref_frame_free_rules]: "MK_FREE vmtf_remove_assn ?fr"  
  unfolding vmtf_remove_assn_def
  by (rule free_thms sepref_frame_free_rules)+ (* TODO: Write a method for that! *)
(*cach_refinement_l_assn*)

schematic_goal mk_free_cach_refinement_l_assn[sepref_frame_free_rules]: "MK_FREE cach_refinement_l_assn ?fr"  
  unfolding cach_refinement_l_assn_def
  by (rule free_thms sepref_frame_free_rules)+ (* TODO: Write a method for that! *)

schematic_goal mk_free_lbd_assn[sepref_frame_free_rules]: "MK_FREE lbd_assn ?fr"  
  unfolding lbd_assn_def
  by (rule free_thms sepref_frame_free_rules)+ (* TODO: Write a method for that! *)

schematic_goal mk_free_opts_assn[sepref_frame_free_rules]: "MK_FREE opts_assn ?fr"  
  unfolding opts_assn_def
  by (rule free_thms sepref_frame_free_rules)+ (* TODO: Write a method for that! *)

schematic_goal mk_free_heuristic_assn[sepref_frame_free_rules]: "MK_FREE heuristic_assn ?fr"
  unfolding heuristic_assn_def
  by (rule free_thms sepref_frame_free_rules)+ (* TODO: Write a method for that! *)

thm array_mk_free
  context 
    fixes l_dummy :: "'l::len2 itself"
    fixes ll_dummy :: "'ll::len2 itself"
    fixes L LL AA
    defines [simp]: "L \<equiv> (LENGTH ('l))"
    defines [simp]: "LL \<equiv> (LENGTH ('ll))"
    defines [simp]: "AA \<equiv> raw_aal_assn TYPE('l::len2) TYPE('ll::len2)"
  begin  
    private lemma n_unf: "hr_comp AA (\<langle>\<langle>the_pure A\<rangle>list_rel\<rangle>list_rel) = aal_assn A" unfolding aal_assn_def AA_def ..

    context 
      notes [fcomp_norm_unfold] = n_unf
    begin
    
lemma aal_assn_free[sepref_frame_free_rules]: "MK_FREE AA aal_free"
  apply rule by vcg
  sepref_decl_op list_list_free: "\<lambda>_::_ list list. ()" :: "\<langle>\<langle>A\<rangle>list_rel\<rangle>list_rel \<rightarrow> unit_rel" .

lemma hn_aal_free_raw: "(aal_free,RETURN o op_list_list_free) \<in> AA\<^sup>d \<rightarrow>\<^sub>a unit_assn"
    by sepref_to_hoare vcg
  
  sepref_decl_impl aal_free: hn_aal_free_raw
     .

  lemmas array_mk_free[sepref_frame_free_rules] = hn_MK_FREEI[OF aal_free_hnr]
end
end

schematic_goal mk_free_isasat_init_assn[sepref_frame_free_rules]: "MK_FREE isasat_init_assn ?fr"  
  unfolding isasat_init_assn_def
  by (rule free_thms sepref_frame_free_rules)+ (* TODO: Write a method for that! *)

sepref_def extract_model_of_state_stat
  is \<open>RETURN o extract_model_of_state_stat\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a model_stat_assn\<close>
  supply [[goals_limit=1]]
  unfolding extract_model_of_state_stat_alt_def isasat_bounded_assn_def
   trail_pol_fast_assn_def
  by sepref

lemmas [sepref_fr_rules] = extract_model_of_state_stat.refine

lemma extract_state_stat_alt_def:
  \<open>RETURN o extract_state_stat = (\<lambda>(M, N', D', j, W', vm, clvls, cach, lbd, outl, stats,
       heur,
       vdom, avdom, lcount, opts, old_arena).
     do {mop_free M; mop_free N'; mop_free D'; mop_free j; mop_free W'; mop_free vm;
         mop_free clvls;
         mop_free cach; mop_free lbd; mop_free outl; mop_free heur;
         mop_free vdom; mop_free avdom; mop_free opts;
         mop_free old_arena;
        RETURN (True, [], stats)})\<close>
  by (auto simp: extract_state_stat_def mop_free_def intro!: ext)

sepref_def extract_state_stat
  is \<open>RETURN o extract_state_stat\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a model_stat_assn\<close>
  supply [[goals_limit=1]]
  unfolding extract_state_stat_alt_def isasat_bounded_assn_def
    al_fold_custom_empty[where 'l=64]
  by sepref

lemma convert_state_hnr:
  \<open>(uncurry (return oo (\<lambda>_ S. S)), uncurry (RETURN oo convert_state))
   \<in> ghost_assn\<^sup>k *\<^sub>a (isasat_init_assn)\<^sup>d \<rightarrow>\<^sub>a
     isasat_init_assn\<close>
  unfolding convert_state_def
  by sepref_to_hoare vcg

sepref_def IsaSAT_use_fast_mode_impl
  is \<open>uncurry0 (RETURN IsaSAT_use_fast_mode)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding IsaSAT_use_fast_mode_def
  by sepref

lemmas [sepref_fr_rules] = IsaSAT_use_fast_mode_impl.refine extract_state_stat.refine


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

declare empty_init_code'.refine[sepref_fr_rules]

sepref_register init_dt_wl_heur_full

sepref_register to_init_state from_init_state get_conflict_wl_is_None_init extract_stats
  init_dt_wl_heur

definition isasat_fast_bound :: \<open>nat\<close> where
\<open>isasat_fast_bound = sint64_max - (uint32_max div 2 + 6)\<close>

lemma isasat_fast_bound_alt_def: \<open>isasat_fast_bound = 9223372034707292154\<close>
  unfolding isasat_fast_bound_def sint64_max_def uint32_max_def
  by simp

sepref_def isasat_fast_bound_impl
  is \<open>uncurry0 (RETURN isasat_fast_bound)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a sint64_nat_assn\<close>
  unfolding isasat_fast_bound_alt_def
  apply (annot_snat_const "TYPE(64)")
  by sepref

lemmas [sepref_fr_rules] = isasat_fast_bound_impl.refine

lemma isasat_fast_init_alt_def:
  \<open>RETURN o isasat_fast_init = (\<lambda>(M, N, _). RETURN (length N \<le> isasat_fast_bound))\<close>
  by (auto simp: isasat_fast_init_def uint64_max_def uint32_max_def isasat_fast_bound_def intro!: ext)

sepref_def isasat_fast_init_code
  is \<open>RETURN o isasat_fast_init\<close>
  :: \<open>isasat_init_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  supply [[goals_limit=1]]
  unfolding isasat_fast_init_alt_def isasat_init_assn_def isasat_fast_bound_def[symmetric]
  by sepref

declare isasat_fast_init_code.refine[sepref_fr_rules]

declare convert_state_hnr[sepref_fr_rules]

sepref_register
   cdcl_twl_stgy_restart_prog_wl_heur

declare init_state_wl_D'_code.refine[FCOMP init_state_wl_D'[unfolded convert_fref],
  unfolded lits_with_max_assn_alt_def[symmetric] init_state_wl_heur_fast_def[symmetric],
  unfolded init_state_wl_D'_code_isasat, sepref_fr_rules]

thm init_state_wl_D'_code.refine[FCOMP init_state_wl_D'[unfolded convert_fref],
  unfolded lits_with_max_assn_alt_def[symmetric] ]

lemma [sepref_fr_rules]: \<open>(init_state_wl_D'_code, init_state_wl_heur_fast)
\<in> [\<lambda>x. distinct_mset x \<and>
       (\<forall>L\<in>#\<L>\<^sub>a\<^sub>l\<^sub>l x.
           nat_of_lit L
           \<le> uint32_max)]\<^sub>a lits_with_max_assn\<^sup>k \<rightarrow> isasat_init_assn\<close>
  using init_state_wl_D'_code.refine[FCOMP init_state_wl_D'[unfolded convert_fref]]
  unfolding lits_with_max_assn_alt_def[symmetric] init_state_wl_D'_code_isasat
    init_state_wl_heur_fast_def
  by auto


lemma is_failed_heur_init_alt_def:
  \<open>is_failed_heur_init = (\<lambda>(_, _, _, _, _, _, _, _, _, _, _, failed). failed)\<close>
  by (auto)

sepref_def is_failed_heur_init_impl
  is \<open>RETURN o is_failed_heur_init\<close>
  :: \<open>isasat_init_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding isasat_init_assn_def is_failed_heur_init_alt_def
  by sepref

lemmas [sepref_fr_rules] = is_failed_heur_init_impl.refine

definition ghost_assn where \<open>ghost_assn = hr_comp unit_assn virtual_copy_rel\<close>

lemma [sepref_fr_rules]: \<open>(return o (\<lambda>_. ()), RETURN o virtual_copy) \<in> lits_with_max_assn\<^sup>k \<rightarrow>\<^sub>a ghost_assn\<close>
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

schematic_goal mk_free_ghost_assn[sepref_frame_free_rules]: "MK_FREE ghost_assn ?fr"  
  unfolding ghost_assn_def
  by (rule free_thms sepref_frame_free_rules)+ (* TODO: Write a method for that! *)

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
  apply (annot_snat_const "TYPE(64)")
  by sepref

definition default_opts where
  \<open>default_opts = (True, True, True)\<close>

sepref_def default_opts_impl
  is \<open>uncurry0 (RETURN default_opts)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a opts_assn\<close>
  unfolding opts_assn_def default_opts_def
  by sepref

definition IsaSAT_bounded_heur_wrapper :: \<open>_ \<Rightarrow> (nat) nres\<close>where
  \<open>IsaSAT_bounded_heur_wrapper C = do {
      (b, (b', _)) \<leftarrow> IsaSAT_bounded_heur default_opts C;
      RETURN ((if b then 2 else 0) + (if b' then 1 else 0))
  }\<close>

text \<open>
  The calling convention of LLVM and clang is not the same, so returning the model is
  currently unsupported. We return only the flags (as ints, not as bools) and the
  statistics.
\<close>
sepref_register IsaSAT_bounded_heur default_opts
sepref_def IsaSAT_code_wrapped
  is \<open>IsaSAT_bounded_heur_wrapper\<close>
  :: \<open>(clauses_ll_assn)\<^sup>k \<rightarrow>\<^sub>a sint64_nat_assn\<close>
  supply [[goals_limit=1]] if_splits[split]
  unfolding IsaSAT_bounded_heur_wrapper_def
  apply (annot_snat_const "TYPE(64)")
  by sepref


text \<open>The setup to transmit the version is a bit complicated, because
  it LLVM does not support direct export of string
  literals. Therefore, we actually convert the version to an array
  chars (more precisely, of machine words -- ended with 0) that can be read
  and printed in isasat.
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
  apply (annot_snat_const "TYPE(32)")
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

  export_llvm
    IsaSAT_code_wrapped is \<open>int64_t IsaSAT_code_wrapped(CLAUSES)\<close>
    llvm_version is \<open>STRING_VERSION llvm_version\<close>
    default_opts_impl
    IsaSAT_code
    opts_restart_impl
    count_decided_pol_impl is \<open>uint32_t count_decided_st_heur_pol_fast(TRAIL)\<close>
    arena_lit_impl is \<open>uint32_t arena_lit_impl(ARENA, int64_t)\<close>
  defines \<open>
     typedef struct {int64_t size; struct {int64_t used; uint32_t *clause;};} CLAUSE;
     typedef struct {int64_t num_clauses; CLAUSE *clauses;} CLAUSES;

     typedef struct {int64_t size; struct {int64_t capacity; int32_t *data;};} ARENA;
     typedef int32_t* STRING_VERSION;

     typedef struct {int64_t size; struct {int64_t capacity; uint32_t *data;};} RAW_TRAIL;
     typedef struct {int64_t size; int8_t *polarity;} POLARITY;
     typedef struct {int64_t size; int32_t *level;} LEVEL;
     typedef struct {int64_t size; int64_t *reasons;} REASONS;
     typedef struct {int64_t size; struct {int64_t capacity; int32_t *data;};} CONTROL_STACK;
     typedef struct {RAW_TRAIL raw_trail;
         struct {POLARITY pol;
           struct {LEVEL lev;
             struct {REASONS resasons;
               struct {int32_t dec_lev;
                CONTROL_STACK cs;};};};};} TRAIL;
  \<close>
  file "code/isasat_restart.ll"

end

definition model_bounded_assn where
  \<open>model_bounded_assn =
   hr_comp (bool1_assn \<times>\<^sub>a model_stat_assn\<^sub>0)
   {((b, m), (b', m')). b=b' \<and> (b \<longrightarrow> (m,m') \<in> model_stat_rel)}\<close>

definition clauses_l_assn where
  \<open>clauses_l_assn = hr_comp (IICF_Array_of_Array_List.aal_assn
                                    unat_lit_assn)
                                  (list_mset_rel O
                                   \<langle>list_mset_rel\<rangle>IsaSAT_Initialisation.mset_rel)\<close>

theorem IsaSAT_full_correctness:
  \<open>(uncurry IsaSAT_code, uncurry (\<lambda>_. model_if_satisfiable_bounded))
     \<in> [\<lambda>(_, a). Multiset.Ball a distinct_mset \<and>
      (\<forall>C\<in>#a.  \<forall>L\<in>#C. nat_of_lit L  \<le> uint32_max)]\<^sub>a opts_assn\<^sup>d *\<^sub>a clauses_l_assn\<^sup>k \<rightarrow> model_bounded_assn\<close>
  using IsaSAT_code.refine[FCOMP IsaSAT_bounded_heur_model_if_sat'[unfolded convert_fref]]
  unfolding model_bounded_assn_def clauses_l_assn_def
  apply auto
  done

end
