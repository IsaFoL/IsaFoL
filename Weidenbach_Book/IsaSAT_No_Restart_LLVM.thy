theory IsaSAT_No_Restart_LLVM
  imports  Version IsaSAT_CDCL_LLVM
    IsaSAT_Initialisation_LLVM Version IsaSAT
begin

abbreviation  model_stat_assn where
  \<open>model_stat_assn \<equiv> bool1_assn *a (arl64_assn unat_lit_assn) *a stats_assn\<close>

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
  \<open>model_stat_assn\<^sub>0 \<equiv> bool1_assn *a (al_assn unat_lit_assn) *a stats_assn\<close>

abbreviation lits_with_max_assn :: \<open>nat multiset
     \<Rightarrow> (64 word \<times> 64 word \<times> 32 word ptr) \<times> 32 word \<Rightarrow> llvm_amemory \<Rightarrow> bool\<close> where
  \<open>lits_with_max_assn \<equiv> hr_comp (arl64_assn atom_assn *a uint32_nat_assn) lits_with_max_rel\<close>

abbreviation lits_with_max_assn\<^sub>0 :: \<open>nat multiset
     \<Rightarrow> (64 word \<times> 64 word \<times> 32 word ptr) \<times> 32 word \<Rightarrow> llvm_amemory \<Rightarrow> bool\<close> where
  \<open>lits_with_max_assn\<^sub>0 \<equiv> hr_comp (al_assn atom_assn *a unat32_assn) lits_with_max_rel\<close>

lemma lits_with_max_assn_alt_def: \<open>lits_with_max_assn = hr_comp (arl64_assn atom_assn *a uint32_nat_assn)
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
  \<open>RETURN o extract_model_of_state_stat = (\<lambda>((M, M'), N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema, ccount,
       vdom, avdom, lcount, opts, old_arena).
     do {mop_free M'; mop_free N'; mop_free D'; mop_free j; mop_free W'; mop_free vm; mop_free \<phi>; mop_free clvls;
         mop_free cach; mop_free lbd; mop_free outl; mop_free fast_ema; mop_free slow_ema; mop_free ccount;
         mop_free vdom; mop_free avdom; mop_free opts;
         mop_free old_arena;
        RETURN (False, M, stats)})\<close>
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
  \<open>RETURN o extract_state_stat = (\<lambda>(M, N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema, ccount,
       vdom, avdom, lcount, opts, old_arena).
     do {mop_free M; mop_free N'; mop_free D'; mop_free j; mop_free W'; mop_free vm; mop_free \<phi>; mop_free clvls;
         mop_free cach; mop_free lbd; mop_free outl; mop_free fast_ema; mop_free slow_ema; mop_free ccount;
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

sepref_def  empty_conflict_code'
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
  :: \<open>opts_assn\<^sup>d *\<^sub>a (clauses_ll_assn)\<^sup>k \<rightarrow>\<^sub>a bool1_assn *a model_stat_assn\<close>
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

sepref_register IsaSAT_bounded_heur default_opts
sepref_def IsaSAT_code_wrapped
  is \<open>IsaSAT_bounded_heur_wrapper\<close>
  :: \<open>(clauses_ll_assn)\<^sup>k \<rightarrow>\<^sub>a sint64_nat_assn\<close>
  supply [[goals_limit=1]] if_splits[split]
  unfolding IsaSAT_bounded_heur_wrapper_def
  apply (annot_snat_const "TYPE(64)")
  by sepref

experiment
begin

  export_llvm IsaSAT_code_wrapped default_opts_impl IsaSAT_code file "code/isasat_no_restart.ll"

end


theorem IsaSAT_full_correctness:
  \<open>(uncurry IsaSAT_code, uncurry (\<lambda>_. model_if_satisfiable))
     \<in> [\<lambda>(_, a). Multiset.Ball a distinct_mset \<and>
      (\<forall>C\<in>#a.  \<forall>L\<in>#C. nat_of_lit L  \<le> uint32_max)]\<^sub>a opts_assn\<^sup>d *\<^sub>a  clauses_l_assn\<^sup>k \<rightarrow> model_assn\<close>
  using IsaSAT_code.refine[FCOMP IsaSAT_heur_model_if_sat'[unfolded convert_fref],
    unfolded list_assn_list_mset_rel_clauses_l_assn]
  unfolding model_assn_def
  apply auto
  done


sepref_def cdcl_twl_stgy_restart_prog_bounded_wl_heur_fast_code
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


sepref_def  empty_conflict_fast_code'
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

sepref_def IsaSAT_bounded_code
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