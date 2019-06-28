theory IsaSAT_Conflict_Analysis_LLVM
imports IsaSAT_Conflict_Analysis (*IsaSAT_VMTF_LLVM*) IsaSAT_Setup_LLVM
begin

(*
lemma mark_of_refine[sepref_fr_rules]:
  \<open>(return o (\<lambda>C. the (snd C)), RETURN o mark_of) \<in>
    [\<lambda>C. is_proped C]\<^sub>a pair_nat_ann_lit_assn\<^sup>k \<rightarrow> nat_assn\<close>
  apply sepref_to_hoare
  apply (case_tac x; case_tac xi; case_tac \<open>snd xi\<close>)
  by (sep_auto simp: nat_ann_lit_rel_def)+


lemma mark_of_fast_refine[sepref_fr_rules]:
  \<open>(return o (\<lambda>C. the (snd C)), RETURN o mark_of) \<in>
    [\<lambda>C. is_proped C]\<^sub>a pair_nat_ann_lit_fast_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
proof -
  have 1: \<open>option_assn (\<lambda>a c. \<up> ((c, a) \<in> uint64_nat_rel)) = pure (\<langle>uint64_nat_rel\<rangle>option_rel)\<close>
    unfolding option_assn_pure_conv[symmetric]
    by (auto simp: pure_def)
  show ?thesis
    apply sepref_to_hoare
    unfolding 1
    apply (case_tac x; case_tac xi; case_tac \<open>snd xi\<close>)
       apply (sep_auto simp: br_def)
      apply (sep_auto simp: nat_ann_lit_rel_def uint64_nat_rel_def br_def
        ann_lit_of_pair_if cong: )+
     apply (sep_auto simp: hr_comp_def)
    apply (sep_auto simp: hr_comp_def uint64_nat_rel_def br_def)
     apply (auto simp: nat_ann_lit_rel_def elim: option_relE)[]
    apply (auto simp: ent_refl_true)
    done
qed
*)

lemma get_count_max_lvls_heur_def:
   \<open>get_count_max_lvls_heur = (\<lambda>(_, _, _, _, _, _, _, clvls, _). clvls)\<close>
  by (auto intro!: ext)

sepref_definition get_count_max_lvls_heur_impl
  is \<open>RETURN o get_count_max_lvls_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  unfolding get_count_max_lvls_heur_def isasat_bounded_assn_def
  by sepref

lemmas [sepref_fr_rules] = get_count_max_lvls_heur_impl.refine

sepref_definition maximum_level_removed_eq_count_dec_fast_code
  is \<open>uncurry (RETURN oo maximum_level_removed_eq_count_dec_heur)\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding maximum_level_removed_eq_count_dec_heur_def
  apply (annot_unat_const "TYPE(32)")
  by sepref

declare
  maximum_level_removed_eq_count_dec_fast_code.refine[sepref_fr_rules]

lemma is_decided_hd_trail_wl_heur_alt_def:
  \<open>is_decided_hd_trail_wl_heur = (\<lambda>((M, xs, lvls, reasons, k), _).
      let r = reasons ! (atm_of (last M)) in
      r = DECISION_REASON)\<close>
  unfolding is_decided_hd_trail_wl_heur_def last_trail_pol_def
  by (auto simp: is_decided_hd_trail_wl_heur_pre_def last_trail_pol_def
     Let_def intro!: ext split: if_splits)

sepref_definition is_decided_hd_trail_wl_fast_code
  is \<open>RETURN o is_decided_hd_trail_wl_heur\<close>
  :: \<open>[is_decided_hd_trail_wl_heur_pre]\<^sub>a isasat_bounded_assn\<^sup>k \<rightarrow> bool1_assn\<close>
  supply [[goals_limit=1]]
  unfolding is_decided_hd_trail_wl_heur_alt_def isasat_bounded_assn_def
    is_decided_hd_trail_wl_heur_pre_def last_trail_pol_def trail_pol_fast_assn_def
    last_trail_pol_pre_def
  apply (rewrite in "_ ! \<hole>" annot_unat_snat_upcast[where 'l="64"])
  by sepref

declare
  is_decided_hd_trail_wl_fast_code.refine[sepref_fr_rules]

sepref_definition lit_and_ann_of_propagated_st_heur_fast_code
  is \<open>RETURN o lit_and_ann_of_propagated_st_heur\<close>
  :: \<open>[lit_and_ann_of_propagated_st_heur_pre]\<^sub>a
       isasat_bounded_assn\<^sup>k \<rightarrow> (unat_lit_assn *a sint64_nat_assn)\<close>
  supply [[goals_limit=1]]
  supply get_trail_wl_heur_def[simp]
  unfolding lit_and_ann_of_propagated_st_heur_def isasat_bounded_assn_def
    lit_and_ann_of_propagated_st_heur_pre_def trail_pol_fast_assn_def
  apply (rewrite in "_ ! \<hole>" annot_unat_snat_upcast[where 'l="64"])
  by sepref

declare
  lit_and_ann_of_propagated_st_heur_fast_code.refine[sepref_fr_rules]

(*TODO Move or kill*)
definition is_UNSET where [simp]: \<open>is_UNSET x \<longleftrightarrow> x = UNSET\<close>
lemma tri_bool_is_UNSET_refine_aux:
  \<open>(\<lambda>x. x = 0, is_UNSET) \<in> tri_bool_rel_aux \<rightarrow> bool_rel \<close>
  by (auto simp: tri_bool_rel_aux_def)

sepref_definition is_UNSET_impl
  is \<open>RETURN o (\<lambda>x. x= 0)\<close>
  :: \<open>(unat_assn' TYPE(8))\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  apply (annot_unat_const "TYPE(8)")
  supply [simp] = max_unat_def
  by sepref

(*lemmas [sepref_fr_rules] = is_UNSET_impl.refine[FCOMP tri_bool_is_UNSET_refine_aux]*)
(*END Move*)

(*TODO Move*)

sepref_definition is_in_option_lookup_conflict_code
  is \<open>uncurry (RETURN oo is_in_option_lookup_conflict)\<close>
  :: \<open>[\<lambda>(L, (c, n, xs)). atm_of L < length xs]\<^sub>a
        unat_lit_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>k \<rightarrow> bool1_assn\<close>
  unfolding is_in_option_lookup_conflict_alt_def is_in_lookup_conflict_def PROTECT_def
     is_NOTIN_alt_def[symmetric] conflict_option_rel_assn_def lookup_clause_rel_assn_def
  apply (rewrite in "_ ! \<hole>" annot_unat_snat_upcast[where 'l="64"])
  by sepref

sepref_definition atm_is_in_conflict_st_heur_fast_code
  is \<open>uncurry (RETURN oo atm_is_in_conflict_st_heur)\<close>
  :: \<open>[atm_is_in_conflict_st_heur_pre]\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>k \<rightarrow> bool1_assn\<close>
  supply [[goals_limit=1]]
  unfolding atm_is_in_conflict_st_heur_def atm_is_in_conflict_st_heur_pre_def isasat_bounded_assn_def
    atm_in_conflict_lookup_def trail_pol_fast_assn_def NOTIN_def[symmetric]
   is_NOTIN_def[symmetric] conflict_option_rel_assn_def lookup_clause_rel_assn_def
  apply (rewrite in "_ ! \<hole>" annot_unat_snat_upcast[where 'l="64"])
  by sepref

declare atm_is_in_conflict_st_heur_fast_code.refine[sepref_fr_rules]
(*END Move*)


(* TODO require VMTF 
sepref_definition tl_state_wl_heur_fast_code
  is \<open>RETURN o tl_state_wl_heur\<close>
  :: \<open>[tl_state_wl_heur_pre]\<^sub>a
      isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]] if_splits[split] lit_of_last_trail_pol_def[simp]
  unfolding tl_state_wl_heur_alt_def[abs_def] isasat_bounded_assn_def get_trail_wl_heur_def[simp]
    vmtf_unset_def bind_ref_tag_def[simp] short_circuit_conv lit_of_last_trail_pol_def
  unfolding tl_state_wl_heur_pre_def trail_pol_fast_assn_def
  by sepref

declare
  tl_state_wl_heur_code.refine[sepref_fr_rules]
  tl_state_wl_heur_fast_code.refine[sepref_fr_rules]*)
sepref_register isasat_lookup_merge_eq2 update_confl_tl_wl_heur

sepref_definition update_confl_tl_wl_fast_code
  is \<open>uncurry2 update_confl_tl_wl_heur\<close>
  :: \<open>[\<lambda>((i, L), S). update_confl_tl_wl_heur_pre ((i, L), S) \<and> isasat_fast S]\<^sub>a
  uint64_nat_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> bool1_assn *a isasat_bounded_assn\<close>
  supply [[goals_limit=1]] isasat_fast_length_leD[dest]
  unfolding update_confl_tl_wl_heur_def isasat_bounded_assn_def
    update_confl_tl_wl_heur_pre_def PR_CONST_def

  by sepref (* slow 200s*)

declare update_confl_tl_wl_code.refine[sepref_fr_rules]
  update_confl_tl_wl_fast_code.refine[sepref_fr_rules]

sepref_register skip_and_resolve_loop_wl_D is_in_conflict_st
sepref_definition skip_and_resolve_loop_wl_D
  is \<open>skip_and_resolve_loop_wl_D_heur\<close>
  :: \<open>isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
  supply [[goals_limit=1]]
    skip_and_resolve_loop_wl_DI[intro]
  unfolding skip_and_resolve_loop_wl_D_heur_def
  apply (rewrite at \<open>\<not>_ \<and> \<not> _\<close> short_circuit_conv)
  by sepref

sepref_definition skip_and_resolve_loop_wl_D_fast
  is \<open>skip_and_resolve_loop_wl_D_heur\<close>
  :: \<open>[\<lambda>S. isasat_fast S]\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
    skip_and_resolve_loop_wl_DI[intro]
    isasat_fast_after_skip_and_resolve_loop_wl_D_heur_inv[intro]
  unfolding skip_and_resolve_loop_wl_D_heur_def
  apply (rewrite at \<open>\<not>_ \<and> \<not> _\<close> short_circuit_conv)
  by sepref (* slow *)

declare skip_and_resolve_loop_wl_D_fast.refine[sepref_fr_rules]
  skip_and_resolve_loop_wl_D.refine[sepref_fr_rules]

end