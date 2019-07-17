theory IsaSAT_Decide_LLVM
  imports IsaSAT_Decide IsaSAT_VMTF_LLVM IsaSAT_Setup_LLVM
begin



(* Cannot find usage of this
sepref_definition lit_of_found_atm_D_code
  is \<open>uncurry lit_of_found_atm_D\<close>
  :: \<open>[lit_of_found_atm_D_pre]\<^sub>a
      (array_assn bool_assn)\<^sup>k *\<^sub>a (option_assn uint32_nat_assn)\<^sup>d \<rightarrow>
          option_assn unat_lit_assn\<close>
  supply [[goals_limit=1]]
  supply not_is_None_not_None[simp] Pos_unat_lit_assn'[sepref_fr_rules]
    Neg_unat_lit_assn'[sepref_fr_rules]
  unfolding lit_of_found_atm_D_def PR_CONST_def lit_of_found_atm_D_pre_def
  by sepref

declare lit_of_found_atm_D_code.refine[sepref_fr_rules]
*)
(* Cannot find usage of this
lemma lit_of_found_atm_hnr[sepref_fr_rules]:
  \<open>(uncurry lit_of_found_atm_D_code, uncurry lit_of_found_atm)
   \<in> [lit_of_found_atm_D_pre]\<^sub>a
     phase_saver_assn\<^sup>k *\<^sub>a (option_assn uint32_nat_assn)\<^sup>d \<rightarrow>
     option_assn unat_lit_assn\<close>
  using lit_of_found_atm_D_code.refine[FCOMP lit_of_found_atm_D_lit_of_found_atm[unfolded convert_fref]] by simp
*)
(*sepref_register find_undefined_atm*)

(*
sepref_definition find_unassigned_lit_wl_D_code
  is \<open>find_unassigned_lit_wl_D_heur\<close>
  :: \<open>isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a (isasat_unbounded_assn *a option_assn unat_lit_assn)\<close>
  supply [[goals_limit=1]]
  unfolding find_unassigned_lit_wl_D_heur_def isasat_unbounded_assn_def PR_CONST_def
  by sepref
*)  

(* will inline
sepref_definition find_unassigned_lit_wl_D_fast_code
  is \<open>find_unassigned_lit_wl_D_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a (isasat_bounded_assn *a option_assn unat_lit_assn)\<close>
  supply [[goals_limit=1]]
  unfolding find_unassigned_lit_wl_D_heur_def isasat_bounded_assn_def PR_CONST_def
  by sepref

declare find_unassigned_lit_wl_D_code.refine[sepref_fr_rules]
  find_unassigned_lit_wl_D_fast_code.refine[sepref_fr_rules]
*)

(*
sepref_definition decide_lit_wl_code
  is \<open>uncurry decide_lit_wl_heur\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding decide_lit_wl_heur_def isasat_unbounded_assn_def PR_CONST_def
    cons_trail_Decided_def[symmetric]
  by sepref
*)


sepref_def decide_lit_wl_fast_code
  is \<open>uncurry decide_lit_wl_heur\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding decide_lit_wl_heur_def isasat_bounded_assn_def
  (*supply hn_case_prod'[sepref_comb_rules del]*)
  unfolding fold_tuple_optimizations
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_constraints
  done
  

  
sepref_register decide_wl_or_skip_D find_unassigned_lit_wl_D_heur decide_lit_wl_heur

find_theorems lit_of_found_atm

find_theorems "\<langle>Id\<rangle>nres_rel = Id"

lemma lit_of_found_atm_D_refine: "
  \<lbrakk>lit_of_found_atm_D_pre (\<phi>, a); (\<phi>,\<phi>')\<in>Id; (a,a')\<in>Id\<rbrakk> \<Longrightarrow> lit_of_found_atm_D \<phi> a \<le>\<Down>Id (lit_of_found_atm \<phi>' a')"
  using lit_of_found_atm_D_lit_of_found_atm unfolding convert_fref
  by (auto dest!: frefD nres_relD)
  
thm decide_wl_or_skip_D_heur_def[unfolded find_unassigned_lit_wl_D_heur_def, no_vars]  
  
definition "decide_wl_or_skip_D_heur1 S \<equiv> doN {
  (S, L) \<leftarrow> case S of (M, N, D, WS, Q, vm, \<phi>, clvls) \<Rightarrow> do {
                          ((M, vm), L) \<leftarrow> isa_vmtf_find_next_undef_upd M vm;
                          L \<leftarrow> lit_of_found_atm_D \<phi> L;
                          RETURN ((M, N, D, WS, Q, vm, \<phi>, clvls), L)
                        };
  case L of None \<Rightarrow> RETURN (True, S) | Some L \<Rightarrow> do {
                                           T \<leftarrow> decide_lit_wl_heur L S;
                                           RETURN (False, T)
                                         }
  }"

lemma decide_wl_or_skip_D_heur1_refine: "decide_wl_or_skip_D_heur1 S \<le> 
  (decide_wl_or_skip_D_heur S)"
  unfolding decide_wl_or_skip_D_heur1_def decide_wl_or_skip_D_heur_def find_unassigned_lit_wl_D_heur_def
  (*using lit_of_found_atm_D_refine*)
  apply (rule refine_IdD)
  apply (refine_vcg lit_of_found_atm_D_refine)
  apply (refine_dref_type)
  by simp_all
  
  
lemma bind_refine_same:
  assumes "\<And>x. f x \<le> \<Down>R (g x)"
  shows "doN { x \<leftarrow> m; f x} \<le>\<Down>R (doN { x \<leftarrow> m; g x})"  
  using assms 
  by (simp add: pw_le_iff refine_pw_simps; blast) 
  
term lit_of_found_atm_D  

definition "lit_of_atm_D \<phi> L \<equiv> doN {
  ASSERT (L<length \<phi>);
  if \<phi>!L then RETURN (Pos L) else RETURN (Neg L)
}"

  
lemma decide_wl_or_skip_D_heur2_refine: "doN {
    let (M, N, D, WS, Q, vm, \<phi>, clvls) = S;
    ((M, vm), L) \<leftarrow> isa_vmtf_find_next_undef_upd M vm;
    if is_None L then let S = (M, N, D, WS, Q, vm, \<phi>, clvls) in RETURN (True, S)
    else doN {
      L \<leftarrow> lit_of_atm_D \<phi> (the L);
      let S = (M, N, D, WS, Q, vm, \<phi>, clvls);
      S \<leftarrow> decide_lit_wl_heur L S;
      RETURN (False, S)
    }
  }
  \<le>
  decide_wl_or_skip_D_heur1 S"
proof -
  obtain M N D WS Q vm \<phi> clvls where SEQ: "S = (M, N, D, WS, Q, vm, \<phi>, clvls)" by (cases S)

  show ?thesis
    unfolding decide_wl_or_skip_D_heur1_def lit_of_atm_D_def lit_of_found_atm_D_def
    apply (simp add: SEQ cong: if_cong)
    apply (rule refine_IdD)
    apply (rule bind_refine_same)
    apply (simp split!: prod.splits; intro allI impI conjI; clarsimp)
    done
qed  
  
(* TODO: Move *)
sepref_register isa_vmtf_find_next_undef  

sepref_def isa_vmtf_find_next_undef_code is 
  "uncurry isa_vmtf_find_next_undef" :: "vmtf_remove_assn\<^sup>k *\<^sub>a trail_pol_fast_assn\<^sup>k \<rightarrow>\<^sub>a atom.option_assn"
  unfolding isa_vmtf_find_next_undef_def vmtf_remove_assn_def
  unfolding atom.fold_option
  apply (rewrite in "WHILEIT _ \<hole>" short_circuit_conv)
  supply [[goals_limit = 1]]
  apply annot_all_atm_idxs
  by sepref

sepref_register update_next_search
sepref_def update_next_search_code is 
  "uncurry (RETURN oo update_next_search)" :: "atom.option_assn\<^sup>k *\<^sub>a vmtf_remove_assn\<^sup>d \<rightarrow>\<^sub>a vmtf_remove_assn"
  unfolding update_next_search_def vmtf_remove_assn_def
  by sepref
  
sepref_register isa_vmtf_find_next_undef_upd  
sepref_def isa_vmtf_find_next_undef_upd_code is 
  "uncurry isa_vmtf_find_next_undef_upd" 
    :: "trail_pol_fast_assn\<^sup>d *\<^sub>a vmtf_remove_assn\<^sup>d \<rightarrow>\<^sub>a (trail_pol_fast_assn *a vmtf_remove_assn) *a atom.option_assn"
  unfolding isa_vmtf_find_next_undef_upd_def
  by sepref
  
find_consts name: lit name: assn

find_theorems unat_lit_assn Neg

sepref_register lit_of_atm_D
sepref_def lit_of_atm_D_code is "uncurry lit_of_atm_D" :: "(phase_saver_assn)\<^sup>k *\<^sub>a atom_assn\<^sup>k \<rightarrow>\<^sub>a unat_lit_assn"
  unfolding lit_of_atm_D_def
  apply annot_all_atm_idxs
  by sepref_dbg_keep

definition "make_isasat_bounded M N D WS Q vm \<phi> clvls = RETURN (M, N, D, WS, Q, vm, \<phi>, clvls)"

lemma fold_make_isasat_bounded: "Let (M, N, D, WS, Q, vm, \<phi>, clvls) m = make_isasat_bounded M N D WS Q vm \<phi> clvls \<bind> m"
  unfolding make_isasat_bounded_def by auto

sepref_register make_isasat_bounded
sepref_def make_isasat_bounded_impl is "uncurry7 (make_isasat_bounded)"
  :: "
  trail_pol_fast_assn\<^sup>d *\<^sub>a arena_fast_assn\<^sup>d *\<^sub>a
  conflict_option_rel_assn\<^sup>d *\<^sub>a
  sint64_nat_assn\<^sup>d *\<^sub>a
  watchlist_fast_assn\<^sup>d *\<^sub>a
  vmtf_remove_assn\<^sup>d *\<^sub>a phase_saver_assn\<^sup>d *\<^sub>a (
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
  opts_assn *a arena_fast_assn)\<^sup>d  
  \<rightarrow>\<^sub>a isasat_bounded_assn"
  unfolding make_isasat_bounded_def isasat_bounded_assn_def
  by sepref

  

sepref_def decide_wl_or_skip_D_fast_code
  is \<open>decide_wl_or_skip_D_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a bool1_assn *a isasat_bounded_assn\<close>
  supply [[goals_limit = 1]]
  apply (rule hfref_refine_with_pre[OF decide_wl_or_skip_D_heur1_refine])
  apply (rule hfref_refine_with_pre[OF decide_wl_or_skip_D_heur2_refine])
  unfolding fold_make_isasat_bounded
  unfolding atom.fold_option
  apply (rewrite in "\<hole> \<rightarrow>\<^sub>a _" isasat_bounded_assn_def)
  unfolding fold_tuple_optimizations
  apply sepref
  done
  

  
experiment begin

export_llvm
  decide_lit_wl_fast_code
  isa_vmtf_find_next_undef_code 
  update_next_search_code 
  isa_vmtf_find_next_undef_upd_code 
  lit_of_atm_D_code
  make_isasat_bounded_impl
  decide_wl_or_skip_D_fast_code
  
end  
  
  
end
