theory IsaSAT_Conflict_Analysis_LLVM
imports IsaSAT_Conflict_Analysis IsaSAT_VMTF_LLVM IsaSAT_Setup_LLVM
begin
thm fold_tuple_optimizations
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

sepref_def get_count_max_lvls_heur_impl
  is \<open>RETURN o get_count_max_lvls_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  unfolding get_count_max_lvls_heur_def isasat_bounded_assn_def
  by sepref

lemmas [sepref_fr_rules] = get_count_max_lvls_heur_impl.refine

sepref_def maximum_level_removed_eq_count_dec_fast_code
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

sepref_def is_decided_hd_trail_wl_fast_code
  is \<open>RETURN o is_decided_hd_trail_wl_heur\<close>
  :: \<open>[is_decided_hd_trail_wl_heur_pre]\<^sub>a isasat_bounded_assn\<^sup>k \<rightarrow> bool1_assn\<close>
  supply [[goals_limit=1]]
  unfolding is_decided_hd_trail_wl_heur_alt_def isasat_bounded_assn_def
    is_decided_hd_trail_wl_heur_pre_def last_trail_pol_def trail_pol_fast_assn_def
    last_trail_pol_pre_def
  by sepref

declare
  is_decided_hd_trail_wl_fast_code.refine[sepref_fr_rules]

sepref_def lit_and_ann_of_propagated_st_heur_fast_code
  is \<open>RETURN o lit_and_ann_of_propagated_st_heur\<close>
  :: \<open>[lit_and_ann_of_propagated_st_heur_pre]\<^sub>a
       isasat_bounded_assn\<^sup>k \<rightarrow> (unat_lit_assn *a sint64_nat_assn)\<close>
  supply [[goals_limit=1]]
  supply get_trail_wl_heur_def[simp]
  unfolding lit_and_ann_of_propagated_st_heur_def isasat_bounded_assn_def
    lit_and_ann_of_propagated_st_heur_pre_def trail_pol_fast_assn_def
  unfolding fold_tuple_optimizations
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
  by sepref

(*lemmas [sepref_fr_rules] = is_UNSET_impl.refine[FCOMP tri_bool_is_UNSET_refine_aux]*)
(*END Move*)

(*TODO Move*)

sepref_def is_in_option_lookup_conflict_code
  is \<open>uncurry (RETURN oo is_in_option_lookup_conflict)\<close>
  :: \<open>[\<lambda>(L, (c, n, xs)). atm_of L < length xs]\<^sub>a
        unat_lit_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>k \<rightarrow> bool1_assn\<close>
  unfolding is_in_option_lookup_conflict_alt_def is_in_lookup_conflict_def PROTECT_def
     is_NOTIN_alt_def[symmetric] conflict_option_rel_assn_def lookup_clause_rel_assn_def
  by sepref

sepref_def atm_is_in_conflict_st_heur_fast_code
  is \<open>uncurry (RETURN oo atm_is_in_conflict_st_heur)\<close>
  :: \<open>[atm_is_in_conflict_st_heur_pre]\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>k \<rightarrow> bool1_assn\<close>
  supply [[goals_limit=1]]
  unfolding atm_is_in_conflict_st_heur_def atm_is_in_conflict_st_heur_pre_def isasat_bounded_assn_def
    atm_in_conflict_lookup_def trail_pol_fast_assn_def NOTIN_def[symmetric]
   is_NOTIN_def[symmetric] conflict_option_rel_assn_def lookup_clause_rel_assn_def
  unfolding fold_tuple_optimizations
  by sepref

declare atm_is_in_conflict_st_heur_fast_code.refine[sepref_fr_rules]
(*END Move*)
thm tl_trailt_tr_pre_def
find_theorems lit_of_last_trail_pol
thm lit_of_last_trail_fast_code.refine
sepref_def (in -) lit_of_last_trail_fast_code
  is \<open>RETURN o lit_of_last_trail_pol\<close>
  :: \<open>[\<lambda>(M). fst M \<noteq> []]\<^sub>a trail_pol_fast_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  unfolding lit_of_last_trail_pol_def trail_pol_fast_assn_def
  by sepref

declare lit_of_last_trail_fast_code.refine[sepref_fr_rules]

lemma tl_state_wl_heurI: \<open>tl_state_wl_heur_pre (a, b, c) \<Longrightarrow> fst a \<noteq> []\<close>
  \<open>tl_state_wl_heur_pre (a, b, c) \<Longrightarrow> tl_trailt_tr_pre a\<close>
  \<open>tl_state_wl_heur_pre (a1', a1'a, a1'b, a1'c, a1'd, a1'e, a1'f, a2'f) \<Longrightarrow>
       vmtf_unset_pre (atm_of (lit_of_last_trail_pol a1')) a1'e\<close>
  by (auto simp: tl_state_wl_heur_pre_def tl_trailt_tr_pre_def
    vmtf_unset_pre_def lit_of_last_trail_pol_def)

thm tl_state_wl_heur_alt_def
lemma tl_state_wl_heur_alt_def:
  \<open>tl_state_wl_heur = (\<lambda>(M, N, D, Q, WS, vm, \<phi>, clvls, cach, lbd, outl, stats, s1, s2, s3, vdom, avdom,
      lcount, opts, old_arena).
     let L = lit_of_last_trail_pol M
      in
       (tl_trailt_tr M, N, D, Q, WS, isa_vmtf_unset (atm_of L) vm, \<phi>, clvls,
          cach, lbd, outl, stats, s1, s2, s3, vdom, avdom,
      lcount, opts, old_arena))\<close>
  by (auto simp: tl_state_wl_heur_def)

sepref_def tl_state_wl_heur_fast_code
  is \<open>RETURN o tl_state_wl_heur\<close>
  :: \<open>[tl_state_wl_heur_pre]\<^sub>a
      isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]] if_splits[split] tl_state_wl_heurI[simp]
  unfolding tl_state_wl_heur_alt_def[abs_def] isasat_bounded_assn_def get_trail_wl_heur_def
    vmtf_unset_def bind_ref_tag_def short_circuit_conv
  unfolding fold_tuple_optimizations
  by sepref

declare
  tl_state_wl_heur_fast_code.refine[sepref_fr_rules]

definition None_lookup_conflict :: \<open>_ \<Rightarrow> _ \<Rightarrow> conflict_option_rel\<close> where
\<open>None_lookup_conflict b xs = (b, xs)\<close>


sepref_def None_lookup_conflict_impl
  is \<open>uncurry (RETURN oo None_lookup_conflict)\<close>
  :: \<open>bool1_assn\<^sup>k *\<^sub>a lookup_clause_rel_assn\<^sup>d \<rightarrow>\<^sub>a conflict_option_rel_assn\<close>
  unfolding None_lookup_conflict_def conflict_option_rel_assn_def
    lookup_clause_rel_assn_def
  by sepref

sepref_register None_lookup_conflict
declare None_lookup_conflict_impl.refine[sepref_fr_rules]


definition extract_valuse_of_lookup_conflict :: \<open>conflict_option_rel \<Rightarrow> bool\<close> where
\<open>extract_valuse_of_lookup_conflict = (\<lambda>(b, (_, xs)). b)\<close>


sepref_def extract_valuse_of_lookup_conflict_impl
  is \<open>RETURN o extract_valuse_of_lookup_conflict\<close>
  :: \<open>conflict_option_rel_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding extract_valuse_of_lookup_conflict_def conflict_option_rel_assn_def
    lookup_clause_rel_assn_def
  by sepref

sepref_register extract_valuse_of_lookup_conflict
declare extract_valuse_of_lookup_conflict_impl.refine[sepref_fr_rules]

sepref_register isasat_lookup_merge_eq2 update_confl_tl_wl_heur
lemma update_confl_tl_wl_heur_alt_def:
  \<open>update_confl_tl_wl_heur = (\<lambda>C L (M, N, bnxs, Q, W, vm, \<phi>, clvls, cach, lbd, outl, stats, s1, s2, s3, vdom, avdom, lcount, opts,
       old_arena). do {
      ASSERT (clvls \<ge> 1);
      let L' = atm_of L;
      ASSERT(arena_length N C \<noteq> 2 \<longrightarrow>
        curry6 isa_set_lookup_conflict_aa_pre M N C bnxs clvls lbd outl);
      ASSERT(arena_is_valid_clause_idx N C);
      (bnxs, clvls, lbd, outl) \<leftarrow>
        if arena_length N C = 2 then isasat_lookup_merge_eq2 L M N C bnxs clvls lbd outl
        else isa_resolve_merge_conflict_gt2 M N C bnxs clvls lbd outl;
      let b = extract_valuse_of_lookup_conflict bnxs;
      let nxs =  the_lookup_conflict bnxs;
      ASSERT(curry lookup_conflict_remove1_pre L nxs \<and> clvls \<ge> 1);
      let nxs = lookup_conflict_remove1 L nxs;
      ASSERT(arena_act_pre N C);
      let N = mark_used N C;
      ASSERT(arena_act_pre N C);
      let N = arena_incr_act N C;
      ASSERT(vmtf_unset_pre L' vm);
      ASSERT(tl_trailt_tr_pre M);
      RETURN (False, (tl_trailt_tr M, N, (None_lookup_conflict b nxs), Q, W, isa_vmtf_unset L' vm,
          \<phi>, clvls - 1, cach, lbd, outl, stats,s1, s2, s3, vdom, avdom, lcount, opts,
       old_arena))
   })\<close>
  unfolding update_confl_tl_wl_heur_def
  by (auto intro!: ext bind_cong simp: None_lookup_conflict_def the_lookup_conflict_def
    extract_valuse_of_lookup_conflict_def Let_def)

sepref_def update_confl_tl_wl_fast_code
  is \<open>uncurry2 update_confl_tl_wl_heur\<close>
  :: \<open>[\<lambda>((i, L), S). update_confl_tl_wl_heur_pre ((i, L), S) \<and> isasat_fast S]\<^sub>a
  sint64_nat_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> bool1_assn *a isasat_bounded_assn\<close>
  supply [[goals_limit=1]] isasat_fast_length_leD[intro]
  unfolding update_confl_tl_wl_heur_alt_def isasat_bounded_assn_def
    PR_CONST_def
  apply (rewrite at \<open>If (_ = \<hole>)\<close> snat_const_fold[where 'a=64])
  apply (annot_unat_const "TYPE (32)")
  unfolding fold_tuple_optimizations
  by sepref

declare update_confl_tl_wl_fast_code.refine[sepref_fr_rules]

sepref_register skip_and_resolve_loop_wl_D is_in_conflict_st
sepref_def skip_and_resolve_loop_wl_D_fast
  is \<open>skip_and_resolve_loop_wl_D_heur\<close>
  :: \<open>[\<lambda>S. isasat_fast S]\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
    skip_and_resolve_loop_wl_DI[intro]
    isasat_fast_after_skip_and_resolve_loop_wl_D_heur_inv[intro]
  unfolding skip_and_resolve_loop_wl_D_heur_def
  unfolding fold_tuple_optimizations
  apply (rewrite at \<open>\<not>_ \<and> \<not> _\<close> short_circuit_conv)
  by sepref (* slow *)

declare skip_and_resolve_loop_wl_D_fast.refine[sepref_fr_rules]

experiment
begin
  export_llvm
    get_count_max_lvls_heur_impl
    maximum_level_removed_eq_count_dec_fast_code
    is_decided_hd_trail_wl_fast_code
    lit_and_ann_of_propagated_st_heur_fast_code
    is_in_option_lookup_conflict_code
    atm_is_in_conflict_st_heur_fast_code
    lit_of_last_trail_fast_code
    tl_state_wl_heur_fast_code
    None_lookup_conflict_impl
    extract_valuse_of_lookup_conflict_impl
    update_confl_tl_wl_fast_code
    skip_and_resolve_loop_wl_D_fast

end



end