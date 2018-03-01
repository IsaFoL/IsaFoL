theory IsaSAT_CDCL
  imports IsaSAT_Propagate_Conflict IsaSAT_Conflict_Analysis IsaSAT_Backtrack
begin

paragraph \<open>Decide\<close>

context isasat_input_bounded_nempty
begin

lemma (in -)not_is_None_not_None: \<open>\<not>is_None s \<Longrightarrow> s \<noteq> None\<close>
  by (auto split: option.splits)

sepref_register vmtf_find_next_undef
sepref_thm vmtf_find_next_undef_code
  is \<open>uncurry (PR_CONST vmtf_find_next_undef)\<close>
  :: \<open>vmtf_remove_conc\<^sup>k *\<^sub>a (hr_comp trail_pol_assn trail_pol)\<^sup>k \<rightarrow>\<^sub>a option_assn uint32_nat_assn\<close>
  supply [[goals_limit=1]]
  supply not_is_None_not_None[simp]
  unfolding vmtf_find_next_undef_def PR_CONST_def
  apply (rewrite at \<open>WHILE\<^sub>T\<^bsup>_\<^esup> (\<lambda> _ . \<hole>) _ _\<close> short_circuit_conv)
  apply (rewrite in \<open>If _ \<hole> _\<close> defined_atm_def[symmetric])
  by sepref

concrete_definition (in -) vmtf_find_next_undef_code
  uses isasat_input_bounded_nempty.vmtf_find_next_undef_code.refine_raw
  is \<open>(uncurry ?f, _) \<in> _\<close>

prepare_code_thms (in -) vmtf_find_next_undef_code_def

lemmas vmtf_find_next_undef_code_ref[sepref_fr_rules] =
   vmtf_find_next_undef_code.refine[OF isasat_input_bounded_nempty_axioms]

definition (in isasat_input_ops) vmtf_find_next_undef_upd
  :: \<open>(nat, nat)ann_lits \<Rightarrow> vmtf_remove_int \<Rightarrow>
        (((nat, nat)ann_lits \<times> vmtf_remove_int) \<times> nat option)nres\<close>
where
  \<open>vmtf_find_next_undef_upd = (\<lambda>M vm. do{
      L \<leftarrow> vmtf_find_next_undef vm M;
      RETURN ((M, update_next_search L vm), L)
  })\<close>

definition trail_ref_except_ann_lits where
 \<open>trail_ref_except_ann_lits = {((M, ((A, m, fst_As, lst_As, next_search), removed)), M').
        M = M' \<and> ((A, m, fst_As, lst_As, next_search), removed) \<in> vmtf M}\<close>

definition phase_saver_ref where
  \<open>phase_saver_ref = {(M, M'). M = M' \<and> phase_saving M}\<close>

sepref_register vmtf_find_next_undef_upd
sepref_thm vmtf_find_next_undef_upd_code
  is \<open>uncurry (PR_CONST vmtf_find_next_undef_upd)\<close>
  :: \<open>trail_assn\<^sup>d *\<^sub>a vmtf_remove_conc\<^sup>d \<rightarrow>\<^sub>a
     (hr_comp trail_pol_assn trail_pol *a vmtf_remove_conc) *a
        option_assn uint32_nat_assn\<close>
  supply [[goals_limit=1]]
  supply not_is_None_not_None[simp]
  unfolding vmtf_find_next_undef_upd_def PR_CONST_def
  by sepref

concrete_definition (in -) vmtf_find_next_undef_upd_code
  uses isasat_input_bounded_nempty.vmtf_find_next_undef_upd_code.refine_raw
  is \<open>(uncurry ?f,_)\<in>_\<close>

prepare_code_thms (in -) vmtf_find_next_undef_upd_code_def

lemmas vmtf_find_next_undef_upd_code_ref[sepref_fr_rules] =
   vmtf_find_next_undef_upd_code.refine[OF isasat_input_bounded_nempty_axioms]


definition (in isasat_input_ops)lit_of_found_atm where
\<open>lit_of_found_atm \<phi> L = SPEC (\<lambda>K. (L = None \<longrightarrow> K = None) \<and>
    (L \<noteq> None \<longrightarrow> K \<noteq> None \<and> atm_of (the K) = the L))\<close>

definition (in isasat_input_ops) find_undefined_atm
  :: \<open>(nat,nat) ann_lits \<Rightarrow> vmtf_remove_int \<Rightarrow>
       (((nat,nat) ann_lits \<times> vmtf_remove_int) \<times> nat option) nres\<close>
where
  \<open>find_undefined_atm M _ = SPEC(\<lambda>((M', vm), L).
     (L \<noteq> None \<longrightarrow> Pos (the L) \<in> snd ` D\<^sub>0 \<and> undefined_atm M (the L)) \<and>
     (L = None \<longrightarrow> (\<forall>K\<in>snd ` D\<^sub>0. defined_lit M K)) \<and> M = M' \<and> vm \<in> vmtf M)\<close>

definition (in isasat_input_ops) find_unassigned_lit_wl_D_heur
  :: \<open>twl_st_wl_heur \<Rightarrow> (twl_st_wl_heur \<times> nat literal option) nres\<close>
where
  \<open>find_unassigned_lit_wl_D_heur = (\<lambda>(M, N, D, WS, Q, vm, \<phi>, clvls). do {
      ASSERT(vm \<in> vmtf M \<and> phase_saving \<phi>);
      ((M, vm), L) \<leftarrow> find_undefined_atm M vm;
      L \<leftarrow> lit_of_found_atm \<phi> L;
      RETURN ((M, N, D, WS, Q, vm, \<phi>, clvls), L)
    })\<close>

definition find_unassigned_lit_wl_D_heur_pre where
  \<open>find_unassigned_lit_wl_D_heur_pre S \<longleftrightarrow>
    (
      \<exists>T U.
        (S, T) \<in> state_wl_l None \<and>
        (T, U) \<in> twl_st_l None \<and>
        twl_struct_invs U \<and>
        literals_are_\<L>\<^sub>i\<^sub>n S \<and>
        get_conflict_wl S = None
    )\<close>
lemma find_unassigned_lit_wl_D'_find_unassigned_lit_wl_D:
  \<open>(find_unassigned_lit_wl_D_heur, find_unassigned_lit_wl_D) \<in>
     [find_unassigned_lit_wl_D_heur_pre]\<^sub>f
    twl_st_heur \<rightarrow> \<langle>{((T, L), (T', L')). (T, T') \<in> twl_st_heur \<and> L = L' \<and>
         (L \<noteq> None \<longrightarrow> undefined_lit (get_trail_wl T') (the L) \<and> the L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l) \<and>
         get_conflict_wl T' = None}\<rangle>nres_rel\<close>
proof -
  have [simp]: \<open>undefined_lit M (Pos (atm_of y)) = undefined_lit M y\<close> for M y
    by (auto simp: defined_lit_map)
  have [simp]: \<open>defined_atm M (atm_of y) = defined_lit M y\<close> for M y
    by (auto simp: defined_lit_map defined_atm_def)

  have ID_R: \<open>Id \<times>\<^sub>r \<langle>Id\<rangle>option_rel = Id\<close>
    by auto
  have atms: \<open>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l =
         atms_of_mm (mset `# init_clss_lf N) \<union>
         atms_of_mm NE \<and> D = None\<close>
      if inv: \<open>find_unassigned_lit_wl_D_heur_pre (M, N, D, NE, UE, WS, Q)\<close>
      for M N D NE UE WS Q
  proof -
    obtain T U where
      S_T: \<open>((M, N, D, NE, UE, WS, Q), T) \<in> state_wl_l None\<close> and
      T_U: \<open>(T, U) \<in> twl_st_l None\<close> and
      inv: \<open>twl_struct_invs U\<close> and
      \<A>\<^sub>i\<^sub>n : \<open>literals_are_\<L>\<^sub>i\<^sub>n (M, N, D, NE, UE, WS, Q)\<close> and
      confl: \<open>get_conflict_wl (M, N, D, NE, UE, WS, Q) = None\<close>
      using inv unfolding find_unassigned_lit_wl_D_heur_pre_def
       apply - apply normalize_goal+
       by blast

    have \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of U)\<close> and
        unit: \<open>entailed_clss_inv U\<close>
      using inv unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      by fast+
    then show ?thesis
      using \<A>\<^sub>i\<^sub>n confl S_T T_U unfolding is_\<L>\<^sub>a\<^sub>l\<^sub>l_alt_def state_wl_l_def twl_st_l_def apply -
      by (subst (asm) all_clss_l_ran_m[symmetric], subst (asm) image_mset_union)
        (auto simp: cdcl\<^sub>W_restart_mset.no_strange_atm_def entailed_clss_inv.simps
          mset_take_mset_drop_mset mset_take_mset_drop_mset'
          clauses_def simp del: entailed_clss_inv.simps)
  qed

  have [dest]: \<open>(S, T) \<in> twl_st_heur \<Longrightarrow> \<phi> = get_phase_saver_heur S \<Longrightarrow> phase_saving \<phi>\<close> for S T \<phi>
    by (auto simp: twl_st_heur_def)

  show ?thesis
   unfolding find_unassigned_lit_wl_D_heur_def find_unassigned_lit_wl_D_def find_undefined_atm_def
    ID_R lit_of_found_atm_def
   apply (intro frefI nres_relI)
   apply clarify
   apply refine_vcg
   unfolding RETURN_RES_refine_iff
   by (auto simp add: twl_st_heur_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff Ball_def image_image
       mset_take_mset_drop_mset' atms
        simp del: twl_st_of_wl.simps dest!: atms)
qed


lemma vmtf_find_next_undef_upd:
  \<open>(uncurry vmtf_find_next_undef_upd, uncurry find_undefined_atm) \<in>
     [\<lambda>(M, vm). vm \<in> vmtf M]\<^sub>f Id \<times>\<^sub>f Id \<rightarrow> \<langle>Id \<times>\<^sub>f Id \<times>\<^sub>f \<langle>nat_rel\<rangle>option_rel\<rangle>nres_rel\<close>
  unfolding vmtf_find_next_undef_upd_def trail_ref_except_ann_lits_def find_undefined_atm_def
    update_next_search_def uncurry_def
  apply (intro frefI nres_relI)
  apply (clarify)
  apply (rule bind_refine_spec)
   prefer 2
   apply (rule vmtf_find_next_undef_ref[simplified])
  by (auto intro!: RETURN_SPEC_refine simp: image_image defined_atm_def[symmetric])


lemma find_undefined_atm_hnr[sepref_fr_rules]:
  \<open>(uncurry vmtf_find_next_undef_upd_code, uncurry (PR_CONST find_undefined_atm))
    \<in> [\<lambda>(b, a). a \<in> vmtf b]\<^sub>a trail_assn\<^sup>d *\<^sub>a vmtf_remove_conc\<^sup>d \<rightarrow>
   (trail_assn *a vmtf_remove_conc) *a option_assn uint32_nat_assn\<close>
  using vmtf_find_next_undef_upd_code_ref[unfolded PR_CONST_def, FCOMP vmtf_find_next_undef_upd]
  unfolding PR_CONST_def
  .

definition (in isasat_input_ops) lit_of_found_atm_D
  :: \<open>bool list \<Rightarrow> nat option \<Rightarrow> (nat literal option)nres\<close> where
  \<open>lit_of_found_atm_D = (\<lambda>(\<phi>::bool list) L. do{
      case L of
        None \<Rightarrow> RETURN None
      | Some L \<Rightarrow> do {
          if \<phi>!L then RETURN (Some (Pos L)) else RETURN (Some (Neg L))
        }
  })\<close>

definition (in isasat_input_ops) lit_of_found_atm_D_pre where
\<open>lit_of_found_atm_D_pre = (\<lambda>(\<phi>, L). L \<noteq> None \<longrightarrow> (Pos (the L) \<in> snd ` D\<^sub>0 \<and> the L < length \<phi>))\<close>

sepref_thm lit_of_found_atm_D_code
  is \<open>uncurry (PR_CONST lit_of_found_atm_D)\<close>
  :: \<open>[lit_of_found_atm_D_pre]\<^sub>a
      (array_assn bool_assn)\<^sup>k *\<^sub>a (option_assn uint32_nat_assn)\<^sup>d \<rightarrow>
          option_assn unat_lit_assn\<close>
  supply [[goals_limit=1]]
  supply not_is_None_not_None[simp] Pos_unat_lit_assn[sepref_fr_rules]
    Neg_unat_lit_assn[sepref_fr_rules]
  unfolding lit_of_found_atm_D_def PR_CONST_def lit_of_found_atm_D_pre_def
  by sepref

concrete_definition (in -) lit_of_found_atm_D_code
   uses isasat_input_bounded_nempty.lit_of_found_atm_D_code.refine_raw
   is \<open>(uncurry ?f,_)\<in>_\<close>

prepare_code_thms (in -) lit_of_found_atm_D_code_def

lemmas lit_of_found_atm_D_hnr[sepref_fr_rules] =
   lit_of_found_atm_D_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

lemma lit_of_found_atm_D_lit_of_found_atm:
  \<open>(uncurry (PR_CONST lit_of_found_atm_D), uncurry lit_of_found_atm) \<in>
   [lit_of_found_atm_D_pre]\<^sub>f Id \<times>\<^sub>f Id \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  unfolding lit_of_found_atm_D_def PR_CONST_def lit_of_found_atm_def
  by (auto split: option.splits)


lemma lit_of_found_atm_hnr[sepref_fr_rules]:
  \<open>(uncurry lit_of_found_atm_D_code, uncurry lit_of_found_atm)
   \<in> [lit_of_found_atm_D_pre]\<^sub>a
     phase_saver_conc\<^sup>k *\<^sub>a (option_assn uint32_nat_assn)\<^sup>d \<rightarrow>
     option_assn unat_lit_assn\<close>
  using lit_of_found_atm_D_hnr[FCOMP lit_of_found_atm_D_lit_of_found_atm] by simp

lemma find_unassigned_lit_wl_D_code_helper:
  assumes
    \<open>RETURN ((a1'h, (db, dc, dd, de), df), a2'g) \<le> find_undefined_atm a1' ((cj, ck, cl, cm), cn)\<close>
      and
    \<open>phase_saving a2'f\<close>
  shows \<open>lit_of_found_atm_D_pre (a2'f, a2'g)\<close>
  using assms by (auto simp: find_undefined_atm_def lit_of_found_atm_D_pre_def phase_saving_def
      in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)


sepref_register find_undefined_atm
sepref_thm find_unassigned_lit_wl_D_code
  is \<open>PR_CONST find_unassigned_lit_wl_D_heur\<close>
  :: \<open>isasat_assn\<^sup>d \<rightarrow>\<^sub>a (isasat_assn *a option_assn unat_lit_assn)\<close>
  supply [[goals_limit=1]] find_unassigned_lit_wl_D_code_helper[simp]
  unfolding find_unassigned_lit_wl_D_heur_def isasat_assn_def PR_CONST_def
  by sepref

concrete_definition (in -) find_unassigned_lit_wl_D_code
   uses isasat_input_bounded_nempty.find_unassigned_lit_wl_D_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) find_unassigned_lit_wl_D_code_def

lemmas find_unassigned_lit_wl_D_heur_hnr[sepref_fr_rules] =
   find_unassigned_lit_wl_D_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

definition (in isasat_input_ops) decide_lit_wl_heur :: \<open>nat literal \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur\<close> where
  \<open>decide_lit_wl_heur = (\<lambda>L' (M, N, D, Q, W, vmtf, \<phi>, clvls, cach, lbd, outl, stats).
      (Decided L' # M, N, D, {#- L'#}, W, vmtf, \<phi>, clvls, cach, lbd, outl, incr_decision stats))\<close>

sepref_thm decide_lit_wl_code
  is \<open>uncurry (RETURN oo decide_lit_wl_heur)\<close>
  :: \<open>[\<lambda>(L, S). undefined_lit (get_trail_wl_heur S) L \<and> get_conflict_wl_heur S = None \<and>
        L \<in> snd ` D\<^sub>0]\<^sub>a
     unat_lit_assn\<^sup>k *\<^sub>a isasat_assn\<^sup>d \<rightarrow> isasat_assn\<close>
  supply [[goals_limit=1]] find_unassigned_lit_wl_D_code_helper[simp]
  unfolding decide_lit_wl_heur_def isasat_assn_def PR_CONST_def
    cons_trail_Decided_def[symmetric]
  apply (rewrite at \<open>(_, add_mset _ \<hole>, _)\<close> lms_fold_custom_empty)+
  by sepref

concrete_definition (in -) decide_lit_wl_code
  uses isasat_input_bounded_nempty.decide_lit_wl_code.refine_raw
  is \<open>(uncurry ?f, _) \<in> _\<close>

prepare_code_thms (in -) decide_lit_wl_code_def

lemmas decide_lit_wl_heur_hnr[sepref_fr_rules] =
  decide_lit_wl_code.refine[OF isasat_input_bounded_nempty_axioms]

definition(in isasat_input_ops) decide_wl_or_skip_D_heur
  :: \<open>twl_st_wl_heur \<Rightarrow> (bool \<times> twl_st_wl_heur) nres\<close>
where
  \<open>decide_wl_or_skip_D_heur S = (do {
    (S, L) \<leftarrow> find_unassigned_lit_wl_D_heur S;
    case L of
      None \<Rightarrow> RETURN (True, S)
    | Some L \<Rightarrow>
       do {ASSERT(undefined_lit (get_trail_wl_heur S) L \<and> get_conflict_wl_heur S = None \<and>
             L \<in> snd ` D\<^sub>0);
         RETURN (False, decide_lit_wl_heur L S) }
  })
\<close>

lemma decide_wl_or_skip_D_heur_decide_wl_or_skip_D:
  \<open>(decide_wl_or_skip_D_heur, decide_wl_or_skip_D) \<in> twl_st_heur \<rightarrow>\<^sub>f \<langle>bool_rel \<times>\<^sub>f twl_st_heur\<rangle> nres_rel\<close>
  supply [[goals_limit=1]]
  unfolding decide_wl_or_skip_D_heur_def decide_wl_or_skip_D_def decide_wl_or_skip_D_pre_def
   decide_l_or_skip_pre_def twl_st_of_wl.simps[symmetric]
  apply (intro nres_relI frefI)
  apply (refine_vcg find_unassigned_lit_wl_D'_find_unassigned_lit_wl_D[THEN fref_to_Down])
  subgoal
    unfolding decide_wl_or_skip_pre_def find_unassigned_lit_wl_D_heur_pre_def
      decide_wl_or_skip_pre_def decide_l_or_skip_pre_def
     apply normalize_goal+
     apply (rule_tac x = xa in exI)
     apply (rule_tac x = xb in exI)
     apply auto
     done
  subgoal by (auto simp del: simp: twl_st_heur_def)
  subgoal by (auto simp del: simp: twl_st_heur_def)
  subgoal by (auto simp del: simp: twl_st_heur_def)
  subgoal by (auto simp del: simp: twl_st_heur_def)
  subgoal by (auto simp del: simp: twl_st_heur_def)
  subgoal by (auto simp: twl_st_heur_def decide_lit_wl_heur_def
        decide_lit_wl_def counts_maximum_level_def intro!: vmtf_consD)
  done

sepref_register decide_wl_or_skip_D find_unassigned_lit_wl_D_heur decide_lit_wl_heur
sepref_thm decide_wl_or_skip_D_code
  is \<open>PR_CONST decide_wl_or_skip_D_heur\<close>
  :: \<open>isasat_assn\<^sup>d \<rightarrow>\<^sub>a bool_assn *a isasat_assn\<close>
  unfolding decide_wl_or_skip_D_heur_def PR_CONST_def
  supply [[goals_limit = 1]]
    find_unassigned_lit_wl_D_def[simp] image_image[simp]
  by sepref

concrete_definition (in -) decide_wl_or_skip_D_code
   uses isasat_input_bounded_nempty.decide_wl_or_skip_D_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) decide_wl_or_skip_D_code_def

lemmas decide_wl_or_skip_D_hnr[sepref_fr_rules] =
   decide_wl_or_skip_D_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]



paragraph \<open>Combining Together: the Other Rules\<close>

definition (in isasat_input_ops) cdcl_twl_o_prog_wl_D_heur
 :: \<open>twl_st_wl_heur \<Rightarrow> (bool \<times> twl_st_wl_heur) nres\<close>
where
  \<open>cdcl_twl_o_prog_wl_D_heur S =
    do {
      if get_conflict_wl_heur S = None
      then decide_wl_or_skip_D_heur S
      else do {

        if count_decided_st S > zero_uint32_nat
        then do {
          T \<leftarrow> skip_and_resolve_loop_wl_D_heur S;
          U \<leftarrow> backtrack_wl_D_nlit_heur T;
          RETURN (False, U)
        }
        else RETURN (True, S)
      }
    }
  \<close>

sepref_register get_conflict_wl_is_None decide_wl_or_skip_D_heur skip_and_resolve_loop_wl_D_heur
  backtrack_wl_D_nlit_heur

(* TODO Move + kill get_conflict_wl_is_Nil *)
definition (in -)get_conflict_wl_heur_is_Nil :: \<open>twl_st_wl_heur \<Rightarrow> bool\<close> where
  \<open>get_conflict_wl_heur_is_Nil = (\<lambda>(M, N, D, NE, UE, Q, W). D \<noteq> None \<and> Multiset.is_empty (the D))\<close>

lemma get_conflict_wl_heur_is_Nil_alt_def:
  \<open>get_conflict_wl_heur_is_Nil S \<longleftrightarrow> get_conflict_wl_heur S = Some {#}\<close>
  by (cases S) (auto simp: get_conflict_wl_heur_is_Nil_def Multiset.is_empty_def)

lemma get_conflict_wl_heur_is_Nil_get_conflict_wll_is_Nil_heur:
  \<open>RETURN o get_conflict_wl_heur_is_Nil = get_conflict_wll_is_Nil_heur\<close>
  by (auto intro!: ext simp: get_conflict_wl_heur_is_Nil_def get_conflict_wll_is_Nil_heur_def
      split: if_splits option.splits)

lemma [sepref_fr_rules]: \<open>(get_conflict_wll_is_Nil_code, RETURN \<circ> get_conflict_wl_heur_is_Nil)
\<in> isasat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  using get_conflict_wll_is_Nil_code[unfolded PR_CONST_def
    get_conflict_wl_heur_is_Nil_get_conflict_wll_is_Nil_heur[symmetric]]
  .

(* End Move *)

sepref_register cdcl_twl_o_prog_wl_D

sepref_thm cdcl_twl_o_prog_wl_D_code
  is \<open>PR_CONST cdcl_twl_o_prog_wl_D_heur\<close>
  :: \<open>isasat_assn\<^sup>d \<rightarrow>\<^sub>a bool_assn *a isasat_assn\<close>
  unfolding cdcl_twl_o_prog_wl_D_heur_def PR_CONST_def
  unfolding get_conflict_wl_is_None get_conflict_wl_get_conflict_wl_is_Nil
    get_conflict_wl_is_None_heur_alt_def[symmetric]
   get_conflict_wl_heur_is_Nil_alt_def[symmetric]
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) cdcl_twl_o_prog_wl_D_code
   uses isasat_input_bounded_nempty.cdcl_twl_o_prog_wl_D_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) cdcl_twl_o_prog_wl_D_code_def

lemmas cdcl_twl_o_prog_wl_D_code[sepref_fr_rules] =
   cdcl_twl_o_prog_wl_D_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

lemma (in isasat_input_ops) twl_st_heur_count_decided_st_alt_def:
  fixes S :: twl_st_wl_heur
  shows \<open>(S, T) \<in> twl_st_heur \<Longrightarrow> count_decided_st S = count_decided (get_trail_wl T)\<close>
  unfolding count_decided_st_def twl_st_heur_def
  by (cases S) auto

lemma cdcl_twl_o_prog_wl_D_heur_cdcl_twl_o_prog_wl_D:
  \<open>(cdcl_twl_o_prog_wl_D_heur, cdcl_twl_o_prog_wl_D) \<in> twl_st_heur \<rightarrow>\<^sub>f \<langle>bool_rel \<times>\<^sub>f twl_st_heur\<rangle>nres_rel\<close>
  unfolding cdcl_twl_o_prog_wl_D_heur_def cdcl_twl_o_prog_wl_D_def
  apply (intro frefI nres_relI)
  apply (refine_vcg
      decide_wl_or_skip_D_heur_decide_wl_or_skip_D[THEN fref_to_Down]
      skip_and_resolve_loop_wl_D_heur_skip_and_resolve_loop_wl_D[THEN fref_to_Down]
      backtrack_wl_D_nlit_backtrack_wl_D[THEN fref_to_Down])
  subgoal by (auto simp: twl_st_heur_state_simp)
  subgoal by (auto simp: twl_st_heur_state_simp twl_st_heur_count_decided_st_alt_def)
  subgoal by (auto simp: twl_st_heur_state_simp)
  subgoal by (auto simp: twl_st_heur_state_simp)
  done

paragraph \<open>Combining Together: Full Strategy\<close>

definition (in isasat_input_ops) cdcl_twl_stgy_prog_wl_D_heur
   :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close>
where
  \<open>cdcl_twl_stgy_prog_wl_D_heur S\<^sub>0 =
  do {
    do {
      (brk, T) \<leftarrow> WHILE\<^sub>T
        (\<lambda>(brk, _). \<not>brk)
        (\<lambda>(brk, S).
        do {
          T \<leftarrow> unit_propagation_outer_loop_wl_D_heur S;
          cdcl_twl_o_prog_wl_D_heur T
        })
        (False, S\<^sub>0);
      RETURN T
    }
  }
  \<close>


lemma cdcl_twl_stgy_prog_wl_D_heur_cdcl_twl_stgy_prog_wl_D:
  \<open>(cdcl_twl_stgy_prog_wl_D_heur, cdcl_twl_stgy_prog_wl_D) \<in> twl_st_heur \<rightarrow>\<^sub>f \<langle>twl_st_heur\<rangle>nres_rel\<close>
  unfolding cdcl_twl_stgy_prog_wl_D_heur_def cdcl_twl_stgy_prog_wl_D_def
  apply (intro frefI nres_relI)
  apply (refine_vcg
      unit_propagation_outer_loop_wl_D_heur_unit_propagation_outer_loop_wl_D[THEN fref_to_Down]
      cdcl_twl_o_prog_wl_D_heur_cdcl_twl_o_prog_wl_D[THEN fref_to_Down])
  subgoal by (auto simp: twl_st_heur_state_simp)
  subgoal by (auto simp: twl_st_heur_state_simp)
  subgoal by (auto simp: twl_st_heur_state_simp)
  subgoal by (auto simp: twl_st_heur_state_simp)
  done

sepref_register cdcl_twl_stgy_prog_wl_D unit_propagation_outer_loop_wl_D_heur
  cdcl_twl_o_prog_wl_D_heur

sepref_thm cdcl_twl_stgy_prog_wl_D_code
  is \<open>PR_CONST cdcl_twl_stgy_prog_wl_D_heur\<close>
  :: \<open>isasat_assn\<^sup>d \<rightarrow>\<^sub>a isasat_assn\<close>
  unfolding cdcl_twl_stgy_prog_wl_D_heur_def PR_CONST_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) cdcl_twl_stgy_prog_wl_D_code
   uses isasat_input_bounded_nempty.cdcl_twl_stgy_prog_wl_D_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) cdcl_twl_stgy_prog_wl_D_code_def

lemmas cdcl_twl_stgy_prog_wl_D_code[sepref_fr_rules] =
   cdcl_twl_stgy_prog_wl_D_code.refine[of \<A>\<^sub>i\<^sub>n]

end

export_code cdcl_twl_stgy_prog_wl_D_code in SML_imp module_name SAT_Solver
  file "code/CDCL_Cached_Array_Trail.sml"

end
