theory IsaSAT_Conflict_Analysis_Defs
  imports IsaSAT_Setup IsaSAT_VMTF IsaSAT_LBD
begin

definition lit_and_ann_of_propagated_st :: \<open>nat twl_st_wl \<Rightarrow> nat literal \<times> nat\<close> where
  \<open>lit_and_ann_of_propagated_st S = lit_and_ann_of_propagated (hd (get_trail_wl S))\<close>

definition lit_and_ann_of_propagated_st_heur
   :: \<open>isasat \<Rightarrow> (nat literal \<times> nat) nres\<close>
where
  \<open>lit_and_ann_of_propagated_st_heur = (\<lambda>S. do {
     let (M, _, _, reasons, _) = get_trail_wl_heur S;
     ASSERT(M \<noteq> [] \<and> atm_of (last M) < length reasons);
     RETURN (last M, reasons ! (atm_of (last M)))})\<close>

definition tl_state_wl_heur_pre :: \<open>isasat \<Rightarrow> bool\<close> where
  \<open>tl_state_wl_heur_pre =
      (\<lambda>S.
         let M = get_trail_wl_heur S in let((A, m, fst_As, lst_As, next_search), to_remove) = get_vmtf_heur S in fst M \<noteq> [] \<and>
         tl_trailt_tr_pre M \<and>
	 vmtf_unset_pre (atm_of (last (fst M))) ((A, m, fst_As, lst_As, next_search), to_remove) \<and>
         atm_of (last (fst M)) < length A \<and>
         (next_search \<noteq> None \<longrightarrow>  the next_search < length A))\<close>

definition tl_state_wl_heur :: \<open>isasat \<Rightarrow> (bool \<times> isasat) nres\<close> where
  \<open>tl_state_wl_heur = (\<lambda>S. do {
       ASSERT(tl_state_wl_heur_pre S);
       let M = get_trail_wl_heur S; let vm = get_vmtf_heur S;
       let S = set_trail_wl_heur (tl_trailt_tr M) S; let S = set_vmtf_wl_heur (isa_vmtf_unset (atm_of (lit_of_last_trail_pol M)) vm) S;
       RETURN (False, S)
  })\<close>

definition update_confl_tl_wl_heur
  :: \<open>nat literal \<Rightarrow> nat \<Rightarrow> isasat \<Rightarrow> (bool \<times> isasat) nres\<close>
where
  \<open>update_confl_tl_wl_heur = (\<lambda>L C S. do {
      let M = get_trail_wl_heur S;
      let N = get_clauses_wl_heur S;
      let lbd = get_lbd S;
      let outl = get_outlearned_heur S;
      let clvls = get_count_max_lvls_heur S;
      let vm = get_vmtf_heur S;
      let (b, (n, xs)) = get_conflict_wl_heur S;
      (N, lbd) \<leftarrow> calculate_LBD_heur_st M N lbd C;
      ASSERT (clvls \<ge> 1);
      let L' = atm_of L;
      ASSERT(arena_is_valid_clause_idx N C);
      ((b, (n, xs)), clvls, outl) \<leftarrow>
        if arena_length N C = 2 then isasat_lookup_merge_eq2 L M N C (b, (n, xs)) clvls outl
        else isa_resolve_merge_conflict_gt2 M N C (b, (n, xs)) clvls outl;
      ASSERT(curry lookup_conflict_remove1_pre L (n, xs) \<and> clvls \<ge> 1);
      let (n, xs) = lookup_conflict_remove1 L (n, xs);
      ASSERT(arena_act_pre N C);
      vm \<leftarrow> isa_vmtf_mark_to_rescore_also_reasons_cl M N C (-L) vm;
      ASSERT(vmtf_unset_pre L' vm);
      ASSERT(tl_trailt_tr_pre M);
      let S = set_trail_wl_heur (tl_trailt_tr M) S;
      let S = set_conflict_wl_heur (b, (n, xs)) S;
      let S = set_vmtf_wl_heur (isa_vmtf_unset L' vm) S;
      let S = set_count_max_wl_heur (clvls - 1) S;
      let S = set_outl_wl_heur outl S;
      let S = set_clauses_wl_heur N S;
      let S = set_lbd_wl_heur lbd S;
      RETURN (False, S)
   })\<close>

definition is_decided_hd_trail_wl_heur :: \<open>isasat \<Rightarrow> bool\<close> where
  \<open>is_decided_hd_trail_wl_heur = (\<lambda>S. is_None (snd (last_trail_pol (get_trail_wl_heur S))))\<close>

definition skip_and_resolve_loop_wl_D_heur_inv where
 \<open>skip_and_resolve_loop_wl_D_heur_inv S\<^sub>0' =
    (\<lambda>(brk, S'). \<exists>S S\<^sub>0. (S', S) \<in> twl_st_heur_conflict_ana \<and> (S\<^sub>0', S\<^sub>0) \<in> twl_st_heur_conflict_ana \<and>
      skip_and_resolve_loop_wl_inv S\<^sub>0 brk S \<and>
      length (get_clauses_wl_heur S') = length (get_clauses_wl_heur S\<^sub>0') \<and>
       get_learned_count S' = get_learned_count S\<^sub>0')\<close>

definition update_confl_tl_wl_heur_pre
   :: \<open>(nat \<times> nat literal) \<times> isasat \<Rightarrow> bool\<close>
where
\<open>update_confl_tl_wl_heur_pre =
  (\<lambda>((i, L), S).
      let M = get_trail_wl_heur S; ((A, m, fst_As, lst_As, next_search), _) = get_vmtf_heur S in
      i > 0 \<and>
      (fst M) \<noteq> [] \<and>
      atm_of ((last (fst M))) < length A \<and> (next_search \<noteq> None \<longrightarrow>  the next_search < length A) \<and>
      L = (last (fst M))
      )\<close>

definition lit_and_ann_of_propagated_st_heur_pre where
  \<open>lit_and_ann_of_propagated_st_heur_pre = (\<lambda>((M, _, _, reasons, _), _). atm_of (last M) < length reasons \<and> M \<noteq> [])\<close>

definition atm_is_in_conflict_st_heur_pre
   :: \<open>nat literal \<times> isasat \<Rightarrow> bool\<close>
where
  \<open>atm_is_in_conflict_st_heur_pre  = (\<lambda>(L, S). atm_of L < length (snd (snd (get_conflict_wl_heur S))))\<close>

definition maximum_level_removed_eq_count_dec_heur where
  \<open>maximum_level_removed_eq_count_dec_heur L S =
      RETURN (get_count_max_lvls_heur S > 1)\<close>

definition is_decided_hd_trail_wl_heur_pre where
  \<open>is_decided_hd_trail_wl_heur_pre =
    (\<lambda>S. fst (get_trail_wl_heur S) \<noteq> [] \<and> last_trail_pol_pre (get_trail_wl_heur S))\<close>


definition skip_and_resolve_loop_wl_D_heur
  :: \<open>isasat \<Rightarrow> isasat nres\<close>
where
  \<open>skip_and_resolve_loop_wl_D_heur S\<^sub>0 =
    do {
      _ \<leftarrow> RETURN (IsaSAT_Profile.start_analyze);
      (_, S) \<leftarrow>
        WHILE\<^sub>T\<^bsup>skip_and_resolve_loop_wl_D_heur_inv S\<^sub>0\<^esup>
        (\<lambda>(brk, S). \<not>brk \<and> \<not>is_decided_hd_trail_wl_heur S)
        (\<lambda>(brk, S).
          do {
            ASSERT(\<not>brk \<and> \<not>is_decided_hd_trail_wl_heur S);
            (L, C) \<leftarrow> lit_and_ann_of_propagated_st_heur S;
            b \<leftarrow> atm_is_in_conflict_st_heur (-L) S;
            if b then
	      tl_state_wl_heur S
            else do {
              b \<leftarrow> maximum_level_removed_eq_count_dec_heur L S;
              if b
              then do {
                update_confl_tl_wl_heur L C S
              }
              else
                RETURN (True, S)
            }
          }
        )
        (False, S\<^sub>0);
      _ \<leftarrow> RETURN (IsaSAT_Profile.stop_analyze);
      RETURN S
    }
  \<close>
lemma twl_st_heur_conflict_ana_trail_empty: \<open>(T, x) \<in> twl_st_heur_conflict_ana \<Longrightarrow>
  fst (get_trail_wl_heur T) = [] \<longleftrightarrow> get_trail_wl x = []\<close>
  by 
   (clarsimp simp: twl_st_heur_def state_wl_l_def twl_st_l_def twl_st_heur_conflict_ana_def
    trail_pol_alt_def last_trail_pol_pre_def last_rev hd_map literals_are_in_\<L>\<^sub>i\<^sub>n_trail_def simp flip: rev_map
    dest: multi_member_split)
lemma twl_st_heur_conflict_ana_last_trail_pol_pre:
  \<open>(T, x) \<in> twl_st_heur_conflict_ana \<Longrightarrow> fst (get_trail_wl_heur T) \<noteq> [] \<Longrightarrow> last_trail_pol_pre (get_trail_wl_heur T)\<close>
  apply (cases \<open>get_trail_wl x\<close>)
  by (clarsimp_all simp: twl_st_heur_def state_wl_l_def twl_st_l_def twl_st_heur_conflict_ana_def
    trail_pol_alt_def last_trail_pol_pre_def last_rev hd_map literals_are_in_\<L>\<^sub>i\<^sub>n_trail_def simp flip: rev_map
    dest: multi_member_split)
    (clarsimp_all dest!: multi_member_split simp: ann_lits_split_reasons_def)


lemma skip_and_resolve_loop_wl_DI:
  assumes
    \<open>skip_and_resolve_loop_wl_D_heur_inv S (b, T)\<close>
  shows \<open>is_decided_hd_trail_wl_heur_pre T\<close>
  using assms apply -
  unfolding skip_and_resolve_loop_wl_inv_def skip_and_resolve_loop_inv_l_def skip_and_resolve_loop_inv_def
     skip_and_resolve_loop_wl_D_heur_inv_def is_decided_hd_trail_wl_heur_pre_def
  apply (subst (asm) case_prod_beta)+
  unfolding prod.case
  apply normalize_goal+
  by (simp add: twl_st_heur_conflict_ana_trail_empty twl_st_heur_conflict_ana_last_trail_pol_pre)

lemma isasat_fast_after_skip_and_resolve_loop_wl_D_heur_inv:
  \<open>isasat_fast x \<Longrightarrow> skip_and_resolve_loop_wl_D_heur_inv x (False, a2') \<Longrightarrow> isasat_fast a2'\<close>
  unfolding skip_and_resolve_loop_wl_D_heur_inv_def isasat_fast_def
  by (auto dest: get_learned_count_learned_clss_countD2)

end