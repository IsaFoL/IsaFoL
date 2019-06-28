theory IsaSAT_Setup_LLVM
  imports IsaSAT_Setup IsaSAT_Watch_List_LLVM IsaSAT_Lookup_Conflict_LLVM
    Watched_Literals.WB_More_Refinement IsaSAT_Clauses_LLVM LBD_LLVM
begin

find_in_thms of_nat in sepref_fr_rules  

no_notation WB_More_Refinement.fref ("[_]\<^sub>f _ \<rightarrow> _" [0,60,60] 60)
no_notation WB_More_Refinement.freft ("_ \<rightarrow>\<^sub>f _" [60,60] 60)


(*TODO Move*)
abbreviation "word32_rel \<equiv> word_rel :: (32 word \<times> _) set"
abbreviation "word64_rel \<equiv> word_rel :: (64 word \<times> _) set"
abbreviation "word32_assn \<equiv> word_assn :: 32 word \<Rightarrow> _"
abbreviation "word64_assn \<equiv> word_assn :: 64 word \<Rightarrow> _"

abbreviation stats_rel :: \<open>(stats \<times> stats) set\<close> where
  \<open>stats_rel \<equiv> word64_rel \<times>\<^sub>r word64_rel \<times>\<^sub>r word64_rel \<times>\<^sub>r word64_rel \<times>\<^sub>r word64_rel
     \<times>\<^sub>r word64_rel \<times>\<^sub>r word64_rel \<times>\<^sub>r word64_rel\<close>

abbreviation ema_rel :: \<open>(ema\<times>ema) set\<close> where
  \<open>ema_rel \<equiv> word64_rel \<times>\<^sub>r word64_rel \<times>\<^sub>r word64_rel \<times>\<^sub>r word64_rel \<times>\<^sub>r word64_rel\<close>
     
abbreviation ema_assn :: \<open>ema \<Rightarrow> ema \<Rightarrow> assn\<close> where
  \<open>ema_assn \<equiv> word64_assn *a word64_assn *a word64_assn *a word64_assn *a word64_assn\<close>

abbreviation stats_assn :: \<open>stats \<Rightarrow> stats \<Rightarrow> assn\<close> where
  \<open>stats_assn \<equiv> word64_assn *a word64_assn *a word64_assn *a ema_assn\<close>
  
  
lemma [sepref_import_param]: 
  "(ema_get_value, ema_get_value) \<in> ema_rel \<rightarrow> word64_rel" 
  "(ema_bitshifting,ema_bitshifting) \<in> word64_rel"
  "(ema_reinit,ema_reinit) \<in> ema_rel \<rightarrow> ema_rel"
  "(ema_init,ema_init) \<in> word_rel \<rightarrow> ema_rel"
  by auto



sepref_definition ema_update_impl is "uncurry (RETURN oo ema_update)"  
  :: "uint32_nat_assn\<^sup>k *\<^sub>a ema_assn\<^sup>k \<rightarrow>\<^sub>a ema_assn"
  unfolding ema_update_def
  apply (rewrite at \<open>let _ = of_nat \<hole> * _ in _\<close> annot_unat_unat_upcast[where 'l = 64])
  apply (rewrite at \<open>let _=_ + _; _=\<hole> in _\<close> fold_COPY)
  (* TODO: The let x=y seems to be inlined, making necessary this COPY! Is this behaviour correct? *)
  apply (annot_unat_const "TYPE(64)")
  supply [[goals_limit = 1]]
  supply [simp] = max_unat_def
  by sepref
lemmas [sepref_fr_rules] = ema_update_impl.refine
  
    
  
lemma [sepref_import_param]:
  "(incr_propagation,incr_propagation) \<in> stats_rel \<rightarrow> stats_rel" 
  "(incr_conflict,incr_conflict) \<in> stats_rel \<rightarrow> stats_rel" 
  "(incr_decision,incr_decision) \<in> stats_rel \<rightarrow> stats_rel" 
  "(incr_restart,incr_restart) \<in> stats_rel \<rightarrow> stats_rel" 
  "(incr_lrestart,incr_lrestart) \<in> stats_rel \<rightarrow> stats_rel" 
  "(incr_uset,incr_uset) \<in> stats_rel \<rightarrow> stats_rel" 
  "(incr_GC,incr_GC) \<in> stats_rel \<rightarrow> stats_rel" 
  "(add_lbd,add_lbd) \<in> word64_rel \<rightarrow> stats_rel \<rightarrow> stats_rel"
  by auto


  
abbreviation (input) "restart_info_rel \<equiv> word64_rel \<times>\<^sub>r word64_rel"

abbreviation (input) restart_info_assn where
  \<open>restart_info_assn \<equiv> word64_assn *a word64_assn\<close>

lemma restart_info_params[sepref_import_param]:  
  "(incr_conflict_count_since_last_restart,incr_conflict_count_since_last_restart) \<in> restart_info_rel \<rightarrow> restart_info_rel"
  "(restart_info_update_lvl_avg,restart_info_update_lvl_avg) \<in> word32_rel \<rightarrow> restart_info_rel \<rightarrow> restart_info_rel"
  "(restart_info_init,restart_info_init) \<in> restart_info_rel"
  "(restart_info_restart_done,restart_info_restart_done) \<in> restart_info_rel \<rightarrow> restart_info_rel"
  by auto

  
type_synonym vmtf_node_assn = "(64 word \<times> 32 word \<times> 32 word)"    

definition "vmtf_node1_rel \<equiv> { ((a,b,c),(VMTF_Node a b c)) | a b c. True}"
definition "vmtf_node2_assn \<equiv> uint64_nat_assn *a snat_option_assn' TYPE(32) *a snat_option_assn' TYPE(32)"

definition "vmtf_node_assn \<equiv> hr_comp vmtf_node2_assn vmtf_node1_rel"
lemmas [fcomp_norm_unfold] = vmtf_node_assn_def[symmetric]

lemma 
    vmtf_Node_refine1: "(\<lambda>a b c. (a,b,c), VMTF_Node) \<in> Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> vmtf_node1_rel"
and vmtf_stamp_refine1: "(\<lambda>(a,b,c). a, stamp) \<in> vmtf_node1_rel \<rightarrow> Id"  
and vmtf_get_prev_refine1: "(\<lambda>(a,b,c). b, get_prev) \<in> vmtf_node1_rel \<rightarrow> \<langle>Id\<rangle>option_rel"  
and vmtf_get_next_refine1: "(\<lambda>(a,b,c). c, get_next) \<in> vmtf_node1_rel \<rightarrow> \<langle>Id\<rangle>option_rel"  
  by (auto simp: vmtf_node1_rel_def)

sepref_definition VMTF_Node_impl is "uncurry2 (RETURN ooo (\<lambda>a b c. (a,b,c)))" :: "uint64_nat_assn\<^sup>k *\<^sub>a (snat_option_assn' TYPE(32))\<^sup>k *\<^sub>a (snat_option_assn' TYPE(32))\<^sup>k \<rightarrow>\<^sub>a vmtf_node2_assn"
  unfolding vmtf_node2_assn_def by sepref

sepref_definition VMTF_stamp_impl is "RETURN o (\<lambda>(a,b,c). a)" :: "vmtf_node2_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn"
  unfolding vmtf_node2_assn_def 
  by sepref

sepref_definition VMTF_get_prev_impl is "RETURN o (\<lambda>(a,b,c). b)" :: "vmtf_node2_assn\<^sup>k \<rightarrow>\<^sub>a snat_option_assn' TYPE(32)"
  unfolding vmtf_node2_assn_def 
  by sepref

sepref_definition VMTF_get_next_impl is "RETURN o (\<lambda>(a,b,c). c)" :: "vmtf_node2_assn\<^sup>k \<rightarrow>\<^sub>a snat_option_assn' TYPE(32)"
  unfolding vmtf_node2_assn_def 
  by sepref

(* TODO: This should be done automatically! For all structured ID-relations on hr_comp! *)
lemma workaround_hrcomp_id_norm[fcomp_norm_unfold]: "hr_comp R (\<langle>nat_rel\<rangle>option_rel) = R" by simp

lemmas [sepref_fr_rules] = 
  VMTF_Node_impl.refine[FCOMP vmtf_Node_refine1]  
  VMTF_stamp_impl.refine[FCOMP vmtf_stamp_refine1]
  VMTF_get_prev_impl.refine[FCOMP vmtf_get_prev_refine1]
  VMTF_get_next_impl.refine[FCOMP vmtf_get_next_refine1]
  

  
    
type_synonym vmtf_assn = \<open>vmtf_node_assn ptr \<times> 64 word \<times> 32 word \<times> 32 word \<times> 32 word\<close>  
  
type_synonym vmtf_remove_assn = \<open>vmtf_assn \<times> (32 word array_list64 \<times> 1 word ptr)\<close>


abbreviation vmtf_assn :: "_ \<Rightarrow> vmtf_assn \<Rightarrow> assn" where
  \<open>vmtf_assn \<equiv> (array_assn vmtf_node_assn *a uint64_nat_assn *a uint32_nat_assn *a uint32_nat_assn
    *a snat_option_assn' TYPE(32))\<close>

abbreviation atoms_hash_assn :: \<open>bool list \<Rightarrow> 1 word ptr \<Rightarrow> assn\<close> where
  \<open>atoms_hash_assn \<equiv> array_assn bool1_assn\<close>

abbreviation distinct_atoms_assn where
  \<open>distinct_atoms_assn \<equiv> arl64_assn uint32_nat_assn *a atoms_hash_assn\<close>

definition vmtf_remove_assn
  :: \<open>isa_vmtf_remove_int \<Rightarrow> vmtf_remove_assn \<Rightarrow> assn\<close>
where
  \<open>vmtf_remove_assn \<equiv> vmtf_assn *a distinct_atoms_assn\<close>


paragraph \<open>Options\<close>

type_synonym opts_assn = "1 word \<times> 1 word \<times> 1 word"

definition opts_assn
  :: \<open>opts \<Rightarrow> opts_assn \<Rightarrow> assn\<close>
where
  \<open>opts_assn \<equiv> bool1_assn *a bool1_assn *a bool1_assn\<close>

lemma workaround_opt_assn: "RETURN o (\<lambda>(a,b,c). f a b c) = (\<lambda>(a,b,c). RETURN (f a b c))" by auto

sepref_register opts_restart opts_reduce opts_unbounded_mode
  
sepref_definition opts_restart_impl is "RETURN o opts_restart" :: "opts_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"  
  unfolding opts_restart_def workaround_opt_assn opts_assn_def
  by sepref

sepref_definition opts_reduce_impl is "RETURN o opts_reduce" :: "opts_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"  
  unfolding opts_reduce_def workaround_opt_assn opts_assn_def
  by sepref

sepref_definition opts_unbounded_mode_impl is "RETURN o opts_unbounded_mode" :: "opts_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"  
  unfolding opts_unbounded_mode_def workaround_opt_assn opts_assn_def
  by sepref
  
lemmas [sepref_fr_rules] = 
  opts_restart_impl.refine
  opts_reduce_impl.refine
  opts_unbounded_mode_impl.refine
  
  
abbreviation "watchlist_fast_assn \<equiv> aal_assn' TYPE(64) TYPE(64) watcher_fast_assn"


type_synonym vdom_fast_assn = \<open>64 word array_list64\<close>
abbreviation vdom_fast_assn :: \<open>vdom \<Rightarrow> vdom_fast_assn \<Rightarrow> assn\<close> where
  \<open>vdom_fast_assn \<equiv> arl64_assn sint64_nat_assn\<close>

type_synonym phase_saver_assn = "1 word larray32"
abbreviation phase_saver_assn where
  \<open>phase_saver_assn \<equiv> larray32_assn bool1_assn\<close>

(* TODO: Move *)
type_synonym arena_assn = "(32 word, 64) array_list"
  
typ "(32 word, 64) array_list"
  
type_synonym twl_st_wll_trail_fast =
  \<open>trail_pol_fast_assn \<times> arena_assn \<times> option_lookup_clause_assn \<times>
    32 word \<times> watched_wl_uint32 \<times> vmtf_remove_assn \<times> phase_saver_assn \<times>
    32 word \<times> cach_refinement_l_assn \<times> lbd_assn \<times> out_learned_assn \<times> stats \<times> ema \<times> ema \<times> restart_info \<times>
    vdom_fast_assn \<times> vdom_fast_assn \<times> 64 word \<times> opts_assn \<times> arena_assn\<close>


definition isasat_bounded_assn :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wll_trail_fast \<Rightarrow> assn\<close> where
\<open>isasat_bounded_assn =
  trail_pol_fast_assn *a arena_fast_assn *a
  conflict_option_rel_assn *a
  uint32_nat_assn *a
  watchlist_fast_assn *a
  vmtf_remove_assn *a phase_saver_assn *a
  uint32_nat_assn *a
  cach_refinement_l_assn *a
  lbd_assn *a
  out_learned_assn *a
  stats_assn *a
  ema_assn *a
  ema_assn *a
  restart_info_assn *a
  vdom_fast_assn *a
  vdom_fast_assn *a
  uint64_nat_assn *a
  opts_assn *a arena_fast_assn\<close>


subsubsection \<open>Lift Operations to State\<close>

(*TODO proper setup to test if the conflict is none*)
sepref_definition get_conflict_wl_is_None_fast_code
  is \<open>RETURN o get_conflict_wl_is_None_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding get_conflict_wl_is_None_heur_alt_def isasat_bounded_assn_def length_ll_def[symmetric]
    conflict_option_rel_assn_def
  supply [[goals_limit=1]]
  by sepref

declare get_conflict_wl_is_None_fast_code.refine[sepref_fr_rules]

sepref_definition isa_count_decided_st_fast_code
  is \<open>RETURN o isa_count_decided_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  supply [[goals_limit=2]]
  unfolding isa_count_decided_st_def isasat_bounded_assn_def
  by sepref

declare isa_count_decided_st_fast_code.refine[sepref_fr_rules]


sepref_definition polarity_st_heur_pol_fast
  is \<open>uncurry (RETURN oo polarity_st_heur)\<close>
  :: \<open>[polarity_st_heur_pre]\<^sub>a isasat_bounded_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> tri_bool_assn\<close>
  unfolding polarity_st_heur_alt_def isasat_bounded_assn_def polarity_st_pre_def
    polarity_st_heur_pre_def
  supply [[goals_limit = 1]]
  by sepref

declare polarity_st_heur_pol_fast.refine[sepref_fr_rules]


subsection \<open>More theorems\<close>

(*TODO dup of count_decided_pol*)
lemma count_decided_st_heur_alt_def:
   \<open>count_decided_st_heur = (\<lambda>(M, _). count_decided_pol M)\<close>
  by (auto simp: count_decided_st_heur_def count_decided_pol_def)

sepref_definition count_decided_st_heur_pol_fast
  is \<open>RETURN o count_decided_st_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  unfolding isasat_bounded_assn_def count_decided_st_heur_alt_def
  supply [[goals_limit = 1]]
  by sepref

sepref_definition access_lit_in_clauses_heur_fast_code
  is \<open>uncurry2 (RETURN ooo access_lit_in_clauses_heur)\<close>
  :: \<open>[\<lambda>((S, i), j). access_lit_in_clauses_heur_pre ((S, i), j) \<and>
           length (get_clauses_wl_heur S) \<le> sint64_max]\<^sub>a
      isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k  *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  supply [[goals_limit=1]] arena_lit_pre_le[dest]
  supply [simp] = max_snat_def max_sint_def sint64_max_def
  unfolding isasat_bounded_assn_def access_lit_in_clauses_heur_alt_def
    access_lit_in_clauses_heur_pre_def
  by sepref

declare access_lit_in_clauses_heur_fast_code.refine[sepref_fr_rules]

sepref_register \<open>(=) :: clause_status \<Rightarrow> clause_status \<Rightarrow> _\<close>


lemma [def_pat_rules]: "append_ll \<equiv> op_list_list_push_back" 
  by (rule eq_reflection) (auto simp: append_ll_def fun_eq_iff)

sepref_register rewatch_heur
term op_neq
sepref_definition rewatch_heur_fast_code
  is \<open>uncurry2 (rewatch_heur)\<close>
  :: \<open>[\<lambda>((vdom, arena), W). (\<forall>x \<in> set vdom. x \<le> sint64_max) \<and> length arena \<le> sint64_max \<and> length vdom \<le> sint64_max]\<^sub>a
        vdom_fast_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a watchlist_fast_assn\<^sup>d \<rightarrow> watchlist_fast_assn\<close>
  supply [[goals_limit=1]]
     arena_lit_pre_le_sint64_max[dest] arena_is_valid_clause_idx_le_uint64_max[dest]
  supply [simp] = max_snat_def max_sint_def sint64_max_def append_ll_def[simp]
  supply [dest] = in_snat_rel_imp_less_max' arena_lit_implI(1)
  unfolding rewatch_heur_alt_def Let_def PR_CONST_def
  unfolding while_eq_nfoldli[symmetric]
  apply (subst while_upt_while_direct, simp)
  unfolding if_not_swap
    FOREACH_cond_def FOREACH_body_def 
  apply (annot_snat_const "TYPE(64)")
  by sepref

declare rewatch_heur_fast_code.refine[sepref_fr_rules]


sepref_definition rewatch_heur_st_fast_code
  is \<open>(rewatch_heur_st_fast)\<close>
  :: \<open>[rewatch_heur_st_fast_pre]\<^sub>a
       isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding rewatch_heur_st_def PR_CONST_def rewatch_heur_st_fast_pre_def
    isasat_bounded_assn_def rewatch_heur_st_fast_def
  by sepref

declare rewatch_heur_st_fast_code.refine[sepref_fr_rules]

end