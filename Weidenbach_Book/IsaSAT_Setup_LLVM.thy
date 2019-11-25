theory IsaSAT_Setup_LLVM
  imports IsaSAT_Setup IsaSAT_Watch_List_LLVM IsaSAT_Lookup_Conflict_LLVM
    Watched_Literals.WB_More_Refinement IsaSAT_Clauses_LLVM LBD_LLVM
begin


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


lemma ema_bitshifting_inline[llvm_inline]:
  "ema_bitshifting = (0x100000000::_::len word)" by (auto simp: ema_bitshifting_def)
lemma ema_reinit_inline[llvm_inline]:
  "ema_reinit = (\<lambda>(value, \<alpha>, \<beta>, wait, period).
    (value, \<alpha>, 0x100000000::_::len word, 0::_ word, 0:: _ word))"
  by auto

lemmas [llvm_inline] = ema_init_def

sepref_def ema_update_impl is "uncurry (RETURN oo ema_update)"
  :: "uint32_nat_assn\<^sup>k *\<^sub>a ema_assn\<^sup>k \<rightarrow>\<^sub>a ema_assn"
  unfolding ema_update_def
  apply (rewrite at \<open>let _ = of_nat \<hole> * _ in _\<close> annot_unat_unat_upcast[where 'l = 64])
  apply (rewrite at \<open>let _=_ + _; _=\<hole> in _\<close> fold_COPY)
  (* TODO: The let x=y seems to be inlined, making necessary this COPY! Is this behaviour correct? *)
  apply (annot_unat_const "TYPE(64)")
  supply [[goals_limit = 1]]
  by sepref

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

lemmas [llvm_inline] =
  incr_propagation_def
  incr_conflict_def
  incr_decision_def
  incr_restart_def
  incr_lrestart_def
  incr_uset_def
  incr_GC_def


abbreviation (input) "restart_info_rel \<equiv> word64_rel \<times>\<^sub>r word64_rel \<times>\<^sub>r word64_rel \<times>\<^sub>r word64_rel"

abbreviation (input) restart_info_assn where
  \<open>restart_info_assn \<equiv> word64_assn *a word64_assn *a word64_assn *a word64_assn\<close>

lemma restart_info_params[sepref_import_param]:
  "(incr_conflict_count_since_last_restart,incr_conflict_count_since_last_restart) \<in>
    restart_info_rel \<rightarrow> restart_info_rel"
  "(restart_info_update_lvl_avg,restart_info_update_lvl_avg) \<in>
    word32_rel \<rightarrow> restart_info_rel \<rightarrow> restart_info_rel"
  "(restart_info_init,restart_info_init) \<in> restart_info_rel"
  "(restart_info_restart_done,restart_info_restart_done) \<in> restart_info_rel \<rightarrow> restart_info_rel"
  by auto

lemmas [llvm_inline] =
  incr_conflict_count_since_last_restart_def
  restart_info_update_lvl_avg_def
  restart_info_init_def
  restart_info_restart_done_def


(* TODO: Define vmtf_node_rel, such that sepref sees syntactically an assertion of form "pure ..."*)
type_synonym vmtf_node_assn = "(64 word \<times> 32 word \<times> 32 word)"

definition "vmtf_node1_rel \<equiv> { ((a,b,c),(VMTF_Node a b c)) | a b c. True}"
definition "vmtf_node2_assn \<equiv> uint64_nat_assn *a atom.option_assn *a atom.option_assn"

definition "vmtf_node_assn \<equiv> hr_comp vmtf_node2_assn vmtf_node1_rel"
lemmas [fcomp_norm_unfold] = vmtf_node_assn_def[symmetric]


lemma vmtf_node_assn_pure[safe_constraint_rules]: \<open>CONSTRAINT is_pure vmtf_node_assn\<close>
  unfolding vmtf_node_assn_def vmtf_node2_assn_def
  by solve_constraint


(*

  TODO: Test whether this setup is safe in general?
    E.g., synthesize destructors when side-tac can prove is_pure.

lemmas [sepref_frame_free_rules] = mk_free_is_pure
lemmas [simp] = vmtf_node_assn_pure[unfolded CONSTRAINT_def]
*)

lemmas [sepref_frame_free_rules] = mk_free_is_pure[OF vmtf_node_assn_pure[unfolded CONSTRAINT_def]]


lemma
    vmtf_Node_refine1: "(\<lambda>a b c. (a,b,c), VMTF_Node) \<in> Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> vmtf_node1_rel"
and vmtf_stamp_refine1: "(\<lambda>(a,b,c). a, stamp) \<in> vmtf_node1_rel \<rightarrow> Id"
and vmtf_get_prev_refine1: "(\<lambda>(a,b,c). b, get_prev) \<in> vmtf_node1_rel \<rightarrow> \<langle>Id\<rangle>option_rel"
and vmtf_get_next_refine1: "(\<lambda>(a,b,c). c, get_next) \<in> vmtf_node1_rel \<rightarrow> \<langle>Id\<rangle>option_rel"
  by (auto simp: vmtf_node1_rel_def)

sepref_def VMTF_Node_impl is []
  "uncurry2 (RETURN ooo (\<lambda>a b c. (a,b,c)))"
  :: "uint64_nat_assn\<^sup>k *\<^sub>a (atom.option_assn)\<^sup>k *\<^sub>a (atom.option_assn)\<^sup>k \<rightarrow>\<^sub>a vmtf_node2_assn"
  unfolding vmtf_node2_assn_def by sepref

sepref_def VMTF_stamp_impl
  is [] "RETURN o (\<lambda>(a,b,c). a)"
  :: "vmtf_node2_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn"
  unfolding vmtf_node2_assn_def
  by sepref

sepref_def VMTF_get_prev_impl
  is [] "RETURN o (\<lambda>(a,b,c). b)"
  :: "vmtf_node2_assn\<^sup>k \<rightarrow>\<^sub>a atom.option_assn"
  unfolding vmtf_node2_assn_def
  by sepref

sepref_def VMTF_get_next_impl
  is [] "RETURN o (\<lambda>(a,b,c). c)"
  :: "vmtf_node2_assn\<^sup>k \<rightarrow>\<^sub>a atom.option_assn"
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
  \<open>vmtf_assn \<equiv> (array_assn vmtf_node_assn *a uint64_nat_assn *a atom_assn *a atom_assn
    *a atom.option_assn)\<close>

abbreviation atoms_hash_assn :: \<open>bool list \<Rightarrow> 1 word ptr \<Rightarrow> assn\<close> where
  \<open>atoms_hash_assn \<equiv> array_assn bool1_assn\<close>

abbreviation distinct_atoms_assn where
  \<open>distinct_atoms_assn \<equiv> arl64_assn atom_assn *a atoms_hash_assn\<close>

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

sepref_def opts_restart_impl is "RETURN o opts_restart" :: "opts_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding opts_restart_def workaround_opt_assn opts_assn_def
  by sepref

sepref_def opts_reduce_impl is "RETURN o opts_reduce" :: "opts_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding opts_reduce_def workaround_opt_assn opts_assn_def
  by sepref

sepref_def opts_unbounded_mode_impl is "RETURN o opts_unbounded_mode" :: "opts_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding opts_unbounded_mode_def workaround_opt_assn opts_assn_def
  by sepref

abbreviation "watchlist_fast_assn \<equiv> aal_assn' TYPE(64) TYPE(64) watcher_fast_assn"


type_synonym vdom_fast_assn = \<open>64 word array_list64\<close>
abbreviation vdom_fast_assn :: \<open>vdom \<Rightarrow> vdom_fast_assn \<Rightarrow> assn\<close> where
  \<open>vdom_fast_assn \<equiv> arl64_assn sint64_nat_assn\<close>

type_synonym phase_saver_assn = "1 word larray64"
abbreviation phase_saver_assn :: \<open>phase_saver \<Rightarrow> phase_saver_assn \<Rightarrow> assn\<close> where
  \<open>phase_saver_assn \<equiv> larray64_assn bool1_assn\<close>

(* TODO: Move *)
type_synonym arena_assn = "(32 word, 64) array_list"
type_synonym heur_assn = \<open>(ema \<times> ema \<times> restart_info \<times> 64 word \<times>
   phase_saver_assn \<times> 32 word \<times> phase_saver_assn \<times> 32 word \<times> phase_saver_assn \<times> 64 word \<times> 64 word)\<close>

type_synonym twl_st_wll_trail_fast =
  \<open>trail_pol_fast_assn \<times> arena_assn \<times> option_lookup_clause_assn \<times>
    64 word \<times> watched_wl_uint32 \<times> vmtf_remove_assn \<times>
    32 word \<times> cach_refinement_l_assn \<times> lbd_assn \<times> out_learned_assn \<times> stats \<times>
    heur_assn \<times>
    vdom_fast_assn \<times> vdom_fast_assn \<times> 64 word \<times> opts_assn \<times> arena_assn\<close>


abbreviation phase_heur_assn where
  \<open>phase_heur_assn \<equiv> phase_saver_assn *a uint32_nat_assn *a phase_saver_assn *a uint32_nat_assn *a
     phase_saver_assn *a word64_assn *a word64_assn\<close>
     
definition heuristic_assn :: \<open>restart_heuristics \<Rightarrow> heur_assn \<Rightarrow> assn\<close> where
  \<open>heuristic_assn = ema_assn *a
  ema_assn *a
  restart_info_assn *a
  word64_assn *a phase_heur_assn\<close>

definition isasat_bounded_assn :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wll_trail_fast \<Rightarrow> assn\<close> where
\<open>isasat_bounded_assn =
  trail_pol_fast_assn *a arena_fast_assn *a
  conflict_option_rel_assn *a
  sint64_nat_assn *a
  watchlist_fast_assn *a
  vmtf_remove_assn *a
  uint32_nat_assn *a
  cach_refinement_l_assn *a
  lbd_assn *a
  out_learned_assn *a
  stats_assn *a
  heuristic_assn *a
  vdom_fast_assn *a
  vdom_fast_assn *a
  uint64_nat_assn *a
  opts_assn *a arena_fast_assn\<close>


sepref_register NORMAL_PHASE QUIET_PHASE DEFAULT_INIT_PHASE

sepref_def NORMAL_PHASE_impl
  is \<open>uncurry0 (RETURN NORMAL_PHASE)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding NORMAL_PHASE_def
  by sepref

sepref_def QUIET_PHASE_impl
  is \<open>uncurry0 (RETURN QUIET_PHASE)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding QUIET_PHASE_def
  by sepref



subsubsection \<open>Lift Operations to State\<close>

(*TODO proper setup to test if the conflict is none*)
sepref_def get_conflict_wl_is_None_fast_code
  is \<open>RETURN o get_conflict_wl_is_None_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding get_conflict_wl_is_None_heur_alt_def isasat_bounded_assn_def length_ll_def[symmetric]
    conflict_option_rel_assn_def
  supply [[goals_limit=1]]
  by sepref


sepref_def isa_count_decided_st_fast_code
  is \<open>RETURN o isa_count_decided_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  supply [[goals_limit=2]]
  unfolding isa_count_decided_st_def isasat_bounded_assn_def
  by sepref

sepref_def polarity_pol_fast
  is \<open>uncurry (mop_polarity_pol)\<close>
  :: \<open>trail_pol_fast_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a tri_bool_assn\<close>
  unfolding mop_polarity_pol_def trail_pol_fast_assn_def
    polarity_pol_def polarity_pol_pre_def
  by sepref

sepref_def polarity_st_heur_pol_fast
  is \<open>uncurry (mop_polarity_st_heur)\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a tri_bool_assn\<close>
  unfolding mop_polarity_st_heur_alt_def isasat_bounded_assn_def polarity_st_pre_def
    mop_polarity_st_heur_alt_def
  supply [[goals_limit = 1]]
  by sepref


subsection \<open>More theorems\<close>

(*TODO dup of count_decided_pol*)
lemma count_decided_st_heur_alt_def:
   \<open>count_decided_st_heur = (\<lambda>(M, _). count_decided_pol M)\<close>
  by (auto simp: count_decided_st_heur_def count_decided_pol_def)

sepref_def count_decided_st_heur_pol_fast
  is \<open>RETURN o count_decided_st_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  unfolding isasat_bounded_assn_def count_decided_st_heur_alt_def
  supply [[goals_limit = 1]]
  by sepref

sepref_def access_lit_in_clauses_heur_fast_code
  is \<open>uncurry2 (RETURN ooo access_lit_in_clauses_heur)\<close>
  :: \<open>[\<lambda>((S, i), j). access_lit_in_clauses_heur_pre ((S, i), j) \<and>
           length (get_clauses_wl_heur S) \<le> sint64_max]\<^sub>a
      isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k  *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  supply [[goals_limit=1]] arena_lit_pre_le[dest]
  unfolding isasat_bounded_assn_def access_lit_in_clauses_heur_alt_def
    access_lit_in_clauses_heur_pre_def
  unfolding fold_tuple_optimizations
  by sepref (* slow *)


sepref_register \<open>(=) :: clause_status \<Rightarrow> clause_status \<Rightarrow> _\<close>


lemma [def_pat_rules]: "append_ll \<equiv> op_list_list_push_back"
  by (rule eq_reflection) (auto simp: append_ll_def fun_eq_iff)

sepref_register rewatch_heur mop_append_ll mop_arena_length

sepref_def mop_append_ll_impl
  is \<open>uncurry2 mop_append_ll\<close>
  :: \<open>[\<lambda>((W, i), _). length (W ! (nat_of_lit i)) < sint64_max]\<^sub>a
    watchlist_fast_assn\<^sup>d *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a watcher_fast_assn\<^sup>k \<rightarrow> watchlist_fast_assn\<close>
  unfolding mop_append_ll_def
  by sepref


sepref_def rewatch_heur_fast_code
  is \<open>uncurry2 (rewatch_heur)\<close>
  :: \<open>[\<lambda>((vdom, arena), W). (\<forall>x \<in> set vdom. x \<le> sint64_max) \<and> length arena \<le> sint64_max \<and>
        length vdom \<le> sint64_max]\<^sub>a
        vdom_fast_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a watchlist_fast_assn\<^sup>d \<rightarrow> watchlist_fast_assn\<close>
  supply [[goals_limit=1]]
     arena_lit_pre_le_sint64_max[dest] arena_is_valid_clause_idx_le_uint64_max[dest]
  supply [simp] = append_ll_def
  supply [dest] = arena_lit_implI(1)
  unfolding rewatch_heur_alt_def Let_def PR_CONST_def
  unfolding while_eq_nfoldli[symmetric]
  apply (subst while_upt_while_direct, simp)
  unfolding if_not_swap
    FOREACH_cond_def FOREACH_body_def
  apply (annot_snat_const "TYPE(64)")
  by sepref


sepref_def rewatch_heur_st_fast_code
  is \<open>(rewatch_heur_st_fast)\<close>
  :: \<open>[rewatch_heur_st_fast_pre]\<^sub>a
       isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding rewatch_heur_st_def PR_CONST_def rewatch_heur_st_fast_pre_def
    isasat_bounded_assn_def rewatch_heur_st_fast_def
  unfolding fold_tuple_optimizations
  by sepref


sepref_register length_avdom

sepref_def length_avdom_fast_code
  is \<open>RETURN o length_avdom\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a sint64_nat_assn\<close>
  unfolding length_avdom_alt_def isasat_bounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

sepref_register get_the_propagation_reason_heur

sepref_def get_the_propagation_reason_heur_fast_code
  is \<open>uncurry get_the_propagation_reason_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a snat_option_assn' TYPE(64)\<close>
  unfolding get_the_propagation_reason_heur_alt_def
     isasat_bounded_assn_def
  supply [[goals_limit = 1]]
  by sepref


sepref_def clause_is_learned_heur_code2
  is \<open>uncurry (RETURN oo clause_is_learned_heur)\<close>
  :: \<open>[\<lambda>(S, C). arena_is_valid_clause_vdom (get_clauses_wl_heur S) C]\<^sub>a
      isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> bool1_assn\<close>
  supply [[goals_limit = 1]]
  unfolding clause_is_learned_heur_alt_def isasat_bounded_assn_def
  by sepref

sepref_register clause_lbd_heur


lemma clause_lbd_heur_alt_def:
  \<open>clause_lbd_heur = (\<lambda>(M', N', D', j, W', vm, clvls, cach, lbd, outl, stats, heur, vdom,
     lcount) C.
     arena_lbd N' C)\<close>
  by (intro ext) (auto simp: clause_lbd_heur_def)

sepref_def clause_lbd_heur_code2
  is \<open>uncurry (RETURN oo clause_lbd_heur)\<close>
  :: \<open>[\<lambda>(S, C). get_clause_LBD_pre (get_clauses_wl_heur S) C]\<^sub>a
       isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  unfolding isasat_bounded_assn_def clause_lbd_heur_alt_def
  supply [[goals_limit = 1]]
  by sepref



sepref_register mark_garbage_heur


sepref_def mark_garbage_heur_code2
  is \<open>uncurry2 (RETURN ooo mark_garbage_heur)\<close>
  :: \<open>[\<lambda>((C, i), S). mark_garbage_pre (get_clauses_wl_heur S, C) \<and> i < length_avdom S \<and>
         get_learned_count S \<ge> 1]\<^sub>a
       sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit = 1]]
  unfolding mark_garbage_heur_def isasat_bounded_assn_def delete_index_and_swap_alt_def
    length_avdom_def fold_tuple_optimizations
  apply (annot_unat_const "TYPE(64)")
  by sepref

sepref_register delete_index_vdom_heur


sepref_def delete_index_vdom_heur_fast_code2
  is \<open>uncurry (RETURN oo delete_index_vdom_heur)\<close>
  :: \<open>[\<lambda>(i, S). i < length_avdom S]\<^sub>a
        sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit = 1]]
  unfolding delete_index_vdom_heur_def isasat_bounded_assn_def delete_index_and_swap_alt_def
    length_avdom_def fold_tuple_optimizations
  by sepref

sepref_register access_length_heur

sepref_def access_length_heur_fast_code2
  is \<open>uncurry (RETURN oo access_length_heur)\<close>
  :: \<open>[\<lambda>(S, C). arena_is_valid_clause_idx (get_clauses_wl_heur S) C]\<^sub>a
       isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> sint64_nat_assn\<close>
  supply [[goals_limit = 1]]
  unfolding access_length_heur_alt_def isasat_bounded_assn_def fold_tuple_optimizations
  by sepref

sepref_register marked_as_used_st

sepref_def marked_as_used_st_fast_code
  is \<open>uncurry (RETURN oo marked_as_used_st)\<close>
  :: \<open>[\<lambda>(S, C). marked_as_used_pre (get_clauses_wl_heur S) C]\<^sub>a
       isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> bool1_assn\<close>
  supply [[goals_limit = 1]]
  unfolding marked_as_used_st_alt_def isasat_bounded_assn_def fold_tuple_optimizations
  by sepref


sepref_register mark_unused_st_heur
sepref_def mark_unused_st_fast_code
  is \<open>uncurry (RETURN oo mark_unused_st_heur)\<close>
  :: \<open>[\<lambda>(C, S). arena_act_pre (get_clauses_wl_heur S) C]\<^sub>a
        sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  unfolding mark_unused_st_heur_def isasat_bounded_assn_def
    arena_act_pre_mark_used[intro!]
  supply [[goals_limit = 1]]
  by sepref


sepref_def get_slow_ema_heur_fast_code
  is \<open>RETURN o get_slow_ema_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a ema_assn\<close>
  unfolding get_slow_ema_heur_alt_def isasat_bounded_assn_def heuristic_assn_def
  by sepref

sepref_def get_fast_ema_heur_fast_code
  is \<open>RETURN o get_fast_ema_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a ema_assn\<close>
  unfolding get_fast_ema_heur_alt_def isasat_bounded_assn_def heuristic_assn_def
  by sepref

sepref_def get_conflict_count_since_last_restart_heur_fast_code
  is \<open>RETURN o get_conflict_count_since_last_restart_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
  unfolding get_counflict_count_heur_alt_def isasat_bounded_assn_def heuristic_assn_def
  by sepref

sepref_def get_learned_count_fast_code
  is \<open>RETURN o get_learned_count\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  unfolding get_learned_count_alt_def isasat_bounded_assn_def
  by sepref

sepref_register incr_restart_stat

sepref_def incr_restart_stat_fast_code
  is \<open>incr_restart_stat\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding incr_restart_stat_def isasat_bounded_assn_def PR_CONST_def
    heuristic_assn_def fold_tuple_optimizations
  by sepref

sepref_register incr_lrestart_stat

sepref_def incr_lrestart_stat_fast_code
  is \<open>incr_lrestart_stat\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding incr_lrestart_stat_def isasat_bounded_assn_def PR_CONST_def
    heuristic_assn_def fold_tuple_optimizations
  by sepref


sepref_def opts_restart_st_fast_code
  is \<open>RETURN o opts_restart_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding opts_restart_st_def isasat_bounded_assn_def
  by sepref


sepref_def opts_reduction_st_fast_code
  is \<open>RETURN o opts_reduction_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding opts_reduction_st_def isasat_bounded_assn_def
  by sepref

sepref_register opts_reduction_st opts_restart_st


lemma emag_get_value_alt_def:
  \<open>ema_get_value = (\<lambda>(a, b, c, d). a)\<close>
  by auto
sepref_def ema_get_value_impl
  is \<open>RETURN o ema_get_value\<close>
  :: \<open>ema_assn\<^sup>k \<rightarrow>\<^sub>a word_assn\<close>
  unfolding emag_get_value_alt_def
  by sepref


sepref_register isasat_length_trail_st

sepref_def isasat_length_trail_st_code
  is \<open>RETURN o isasat_length_trail_st\<close>
  :: \<open>[isa_length_trail_pre o get_trail_wl_heur]\<^sub>a isasat_bounded_assn\<^sup>k  \<rightarrow> sint64_nat_assn\<close>
  supply [[goals_limit=1]]
  unfolding isasat_length_trail_st_alt_def isasat_bounded_assn_def
  by sepref

sepref_register get_pos_of_level_in_trail_imp_st

sepref_def get_pos_of_level_in_trail_imp_st_code
  is \<open>uncurry get_pos_of_level_in_trail_imp_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k  \<rightarrow>\<^sub>a sint64_nat_assn\<close>
  supply [[goals_limit=1]]
  unfolding get_pos_of_level_in_trail_imp_alt_def isasat_bounded_assn_def
  apply (rewrite in "_" eta_expand[where f = RETURN])
  apply (rewrite in "RETURN \<hole>" annot_unat_snat_upcast[where 'l=64])
  by sepref



sepref_register neq : "(op_neq :: clause_status \<Rightarrow> _ \<Rightarrow> _)"
lemma status_neq_refine1: "((\<noteq>),op_neq) \<in> status_rel \<rightarrow> status_rel \<rightarrow> bool_rel"
  by (auto simp: status_rel_def)

sepref_def status_neq_impl is [] "uncurry (RETURN oo (\<noteq>))"
  :: "(unat_assn' TYPE(32))\<^sup>k *\<^sub>a (unat_assn' TYPE(32))\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  by sepref

lemmas [sepref_fr_rules] = status_neq_impl.refine[FCOMP status_neq_refine1]

lemma clause_not_marked_to_delete_heur_alt_def:
  \<open>RETURN oo clause_not_marked_to_delete_heur = (\<lambda>(M, arena, D, oth) C.
      RETURN (arena_status arena C \<noteq> DELETED))\<close>
  unfolding clause_not_marked_to_delete_heur_def by (auto intro!: ext)

sepref_def clause_not_marked_to_delete_heur_fast_code
  is \<open>uncurry (RETURN oo clause_not_marked_to_delete_heur)\<close>
  :: \<open>[clause_not_marked_to_delete_heur_pre]\<^sub>a isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> bool1_assn\<close>
  supply [[goals_limit=1]]
  unfolding clause_not_marked_to_delete_heur_alt_def isasat_bounded_assn_def
     clause_not_marked_to_delete_heur_pre_def
  by sepref

lemma mop_clause_not_marked_to_delete_heur_alt_def:
  \<open>mop_clause_not_marked_to_delete_heur = (\<lambda>(M, arena, D, oth) C. do {
    ASSERT(clause_not_marked_to_delete_heur_pre ((M, arena, D, oth), C));
     RETURN (arena_status arena C \<noteq> DELETED)
   })\<close>
  unfolding clause_not_marked_to_delete_heur_def mop_clause_not_marked_to_delete_heur_def
  by (auto intro!: ext)

sepref_def mop_clause_not_marked_to_delete_heur_impl
  is \<open>uncurry mop_clause_not_marked_to_delete_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding mop_clause_not_marked_to_delete_heur_alt_def
    clause_not_marked_to_delete_heur_pre_def  prod.case isasat_bounded_assn_def
  by sepref

sepref_def delete_index_and_swap_code2
  is \<open>uncurry (RETURN oo delete_index_and_swap)\<close>
  :: \<open>[\<lambda>(xs, i). i < length xs]\<^sub>a
      vdom_fast_assn\<^sup>d *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> vdom_fast_assn\<close>
  unfolding delete_index_and_swap.simps
  by sepref

sepref_def mop_mark_garbage_heur_impj
  is \<open>uncurry2 mop_mark_garbage_heur\<close>
  :: \<open>[\<lambda>((C, i), S). length (get_clauses_wl_heur S) \<le> sint64_max]\<^sub>a
      sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding mop_mark_garbage_heur_alt_def
    clause_not_marked_to_delete_heur_pre_def prod.case isasat_bounded_assn_def
  apply (annot_unat_const "TYPE(64)")
  by sepref

sepref_def mop_mark_unused_st_heur_impl
  is \<open>uncurry mop_mark_unused_st_heur\<close>
  :: \<open> sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  unfolding mop_mark_unused_st_heur_def
  by sepref


sepref_def mop_arena_lbd_st_impl
  is \<open>uncurry mop_arena_lbd_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  supply [[goals_limit=1]]
  unfolding mop_arena_lbd_st_alt_def isasat_bounded_assn_def
  by sepref

sepref_def mop_arena_status_st_impl
  is \<open>uncurry mop_arena_status_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a status_impl_assn\<close>
  supply [[goals_limit=1]]
  unfolding mop_arena_status_st_alt_def isasat_bounded_assn_def
  by sepref

sepref_def mop_marked_as_used_st_impl
  is \<open>uncurry mop_marked_as_used_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  supply [[goals_limit=1]]
  unfolding mop_marked_as_used_st_alt_def isasat_bounded_assn_def
  by sepref

sepref_def mop_arena_length_st_impl
  is \<open>uncurry mop_arena_length_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a sint64_nat_assn\<close>
  supply [[goals_limit=1]]
  unfolding mop_arena_length_st_alt_def isasat_bounded_assn_def
  by sepref

sepref_register incr_wasted_st full_arena_length_st wasted_bytes_st
sepref_def incr_wasted_st_impl
  is \<open>uncurry (RETURN oo incr_wasted_st)\<close>
  :: \<open>word64_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply[[goals_limit=1]]
  unfolding incr_wasted_st_def incr_wasted.simps
    isasat_bounded_assn_def heuristic_assn_def
  by sepref

sepref_def full_arena_length_st_impl
  is \<open>RETURN o full_arena_length_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a sint64_nat_assn\<close>
  unfolding full_arena_length_st_def isasat_bounded_assn_def
  by sepref


sepref_def wasted_bytes_st_impl
  is \<open>RETURN o wasted_bytes_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
  supply [[goals_limit=1]]
  unfolding isasat_bounded_assn_def
    heuristic_assn_def wasted_bytes_st_def
  by sepref

lemma set_zero_wasted_def:
  \<open>set_zero_wasted = (\<lambda>(fast_ema, slow_ema, res_info, wasted, \<phi>, target, best).
    (fast_ema, slow_ema, res_info, 0, \<phi>, target, best))\<close>
  by (auto intro!: ext)

sepref_def set_zero_wasted_impl
  is \<open>RETURN o set_zero_wasted\<close>
  :: \<open>heuristic_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_assn\<close>
  unfolding heuristic_assn_def set_zero_wasted_def
  by sepref

lemma mop_save_phase_heur_alt_def:
  \<open>mop_save_phase_heur = (\<lambda> L b (fast_ema, slow_ema, res_info, wasted, \<phi>, target, best). do {
    ASSERT(L < length \<phi>);
    RETURN (fast_ema, slow_ema, res_info, wasted, \<phi>[L := b], target,
                 best)})\<close>
  unfolding mop_save_phase_heur_def save_phase_heur_def save_phase_heur_pre_def
    heuristic_assn_def
  by (auto intro!: ext)

sepref_def mop_save_phase_heur_impl
  is \<open>uncurry2 (mop_save_phase_heur)\<close>
  :: \<open>atom_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a heuristic_assn\<^sup>d \<rightarrow>\<^sub>a heuristic_assn\<close>
  supply [[goals_limit=1]]
  unfolding mop_save_phase_heur_alt_def save_phase_heur_def save_phase_heur_pre_def
    heuristic_assn_def
  apply annot_all_atm_idxs
  by sepref

sepref_register set_zero_wasted mop_save_phase_heur

experiment begin

export_llvm
  ema_update_impl
  VMTF_Node_impl
  VMTF_stamp_impl
  VMTF_get_prev_impl
  VMTF_get_next_impl
  opts_restart_impl
  opts_reduce_impl
  opts_unbounded_mode_impl
  get_conflict_wl_is_None_fast_code
  isa_count_decided_st_fast_code
  polarity_st_heur_pol_fast
  count_decided_st_heur_pol_fast
  access_lit_in_clauses_heur_fast_code
  rewatch_heur_fast_code
  rewatch_heur_st_fast_code
  set_zero_wasted_impl

end

end

