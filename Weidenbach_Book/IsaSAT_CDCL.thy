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
      L \<leftarrow>  vmtf_find_next_undef vm M;
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


definition lit_of_found_atm where
\<open>lit_of_found_atm \<phi> L = SPEC (\<lambda>K. (L = None \<longrightarrow> K = None) \<and>
    (L \<noteq> None \<longrightarrow> K \<noteq> None \<and> atm_of (the K) = the L))\<close>

definition (in isasat_input_ops) find_undefined_atm
  :: \<open>(nat,nat) ann_lits \<Rightarrow> vmtf_remove_int \<Rightarrow>
       (((nat,nat) ann_lits \<times> vmtf_remove_int) \<times> nat option) nres\<close>
where
  \<open>find_undefined_atm M _ = SPEC(\<lambda>((M', vm), L).
     (L \<noteq> None \<longrightarrow> Pos (the L) \<in> snd ` D\<^sub>0 \<and> undefined_atm M (the L)) \<and>
     (L = None \<longrightarrow> (\<forall>K\<in>snd ` D\<^sub>0. defined_lit M K)) \<and> M = M' \<and> vm \<in> vmtf M)\<close>

definition find_unassigned_lit_wl_D_heur
  :: \<open>twl_st_wl_heur \<Rightarrow> (twl_st_wl_heur \<times> nat literal option) nres\<close>
where
  \<open>find_unassigned_lit_wl_D_heur = (\<lambda>(M, N, U, D, WS, Q, vm, \<phi>, clvls). do {
      ((M, vm), L) \<leftarrow> find_undefined_atm M vm;
      L \<leftarrow> lit_of_found_atm \<phi> L;
      RETURN ((M, N, U, D, WS, Q, vm, \<phi>, clvls), L)
    })\<close>

lemma find_unassigned_lit_wl_D'_find_unassigned_lit_wl_D:
  \<open>(find_unassigned_lit_wl_D_heur, find_unassigned_lit_wl_D) \<in>
     [\<lambda>S. twl_struct_invs (twl_st_of_wl None S) \<and> literals_are_\<L>\<^sub>i\<^sub>n S \<and> get_conflict_wl S = None]\<^sub>f
    twl_st_heur \<rightarrow> \<langle>twl_st_heur \<times>\<^sub>r \<langle>nat_lit_lit_rel\<rangle>option_rel\<rangle>nres_rel\<close>
proof -
  have [simp]: \<open>undefined_lit M (Pos (atm_of y)) = undefined_lit M y\<close> for M y
    by (auto simp: defined_lit_map)
  have [simp]: \<open>defined_atm M (atm_of y) = defined_lit M y\<close> for M y
    by (auto simp: defined_lit_map defined_atm_def)

  have ID_R: \<open>Id \<times>\<^sub>r \<langle>Id\<rangle>option_rel = Id\<close>
    by auto
  have atms: \<open>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l =
         atms_of_ms ((\<lambda>x. mset (take 2 x) + mset (drop 2 x)) ` set (take U (tl N))) \<union>
         atms_of_mm NP \<and> (\<forall>y. atm_of y \<in> atms_of_mm NP \<longrightarrow> defined_lit M y)\<close>
      if inv: \<open>twl_struct_invs (twl_st_of_wl None (M, N, U, D, NP, UP, WS, Q))\<close> and
        \<A>\<^sub>i\<^sub>n: \<open>literals_are_\<L>\<^sub>i\<^sub>n (M, N, U, D, NP, UP, WS, Q)\<close> and
        confl: \<open>get_conflict_wl (M, N, U, D, NP, UP, WS, Q) = None\<close>
      for M N U D NP UP WS Q
  proof -
    have \<open>cdcl\<^sub>W_restart_mset.no_strange_atm
            (state\<^sub>W_of (twl_st_of_wl None (M, N, U, D, NP, UP, WS, Q)))\<close> and
        unit: \<open>unit_clss_inv (twl_st_of_wl None (M, N, U, D, NP, UP, WS, Q))\<close>
      using inv unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      by fast+
    moreover have \<open>defined_lit M L\<close> if NP: \<open>atm_of L\<in> atms_of_mm NP\<close> for L
    proof -
      obtain C where C_NP: \<open>C \<in># NP\<close> and L_C: \<open>atm_of L \<in> atms_of C\<close>
         using NP unfolding atms_of_ms_def by auto
      have \<open>C\<in>set_mset NP \<Longrightarrow> \<exists>L. C = {#L#} \<and> get_level M L = 0 \<and> L \<in> lits_of_l M\<close> for C
         using unit confl by auto
      from this[of C] obtain L' where \<open>C = {#L'#}\<close> and \<open>L' \<in> lits_of_l M\<close>
         using C_NP by auto
      then show ?thesis
        using L_C by (auto simp: Decided_Propagated_in_iff_in_lits_of_l atm_of_eq_atm_of)
    qed
    ultimately show ?thesis
      using \<A>\<^sub>i\<^sub>n unfolding is_\<L>\<^sub>a\<^sub>l\<^sub>l_alt_def
      by (auto simp: cdcl\<^sub>W_restart_mset.no_strange_atm_def
        mset_take_mset_drop_mset mset_take_mset_drop_mset' clauses_def simp del: unit_clss_inv.simps)
  qed
  show ?thesis
   unfolding find_unassigned_lit_wl_D_heur_def find_unassigned_lit_wl_D_def find_undefined_atm_def
    ID_R lit_of_found_atm_def
   apply (intro frefI nres_relI)
   apply clarify
   apply refine_vcg
   unfolding RETURN_RES_refine_iff
   by (auto simp: twl_st_heur_def atms in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff Ball_def image_image
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
    \<open>RETURN ((a1'h, (db, dc, dd, de), df), a2'g) \<le> find_undefined_atm a1' ((cj, ck, cl, cm), cn)\<close> and
    \<open>phase_saving a2'f\<close>
  shows \<open>lit_of_found_atm_D_pre (a2'f, a2'g)\<close>
  using assms by (auto simp: find_undefined_atm_def lit_of_found_atm_D_pre_def phase_saving_def
      in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)


sepref_register find_undefined_atm
sepref_thm find_unassigned_lit_wl_D_code
  is \<open>PR_CONST find_unassigned_lit_wl_D_heur\<close>
  :: \<open>[\<lambda>(M, N, U, D, WS, Q, vm, \<phi>, clvls). vm \<in> vmtf M \<and> phase_saving \<phi>]\<^sub>a
     twl_st_heur_assn\<^sup>d \<rightarrow> (twl_st_heur_assn *a option_assn unat_lit_assn)\<close>
  supply [[goals_limit=1]] find_unassigned_lit_wl_D_code_helper[simp]
  unfolding find_unassigned_lit_wl_D_heur_def twl_st_heur_assn_def PR_CONST_def
  by sepref

concrete_definition (in -) find_unassigned_lit_wl_D_code
   uses isasat_input_bounded_nempty.find_unassigned_lit_wl_D_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) find_unassigned_lit_wl_D_code_def

lemmas find_unassigned_lit_wl_D_heur_hnr[sepref_fr_rules] =
   find_unassigned_lit_wl_D_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

definition find_unassigned_lit_wl_D_pre where
  \<open>find_unassigned_lit_wl_D_pre = (\<lambda>S. twl_struct_invs (twl_st_of_wl None S) \<and> literals_are_\<L>\<^sub>i\<^sub>n S \<and>
             get_conflict_wl S = None)\<close>

lemma find_unassigned_lit_wl_D_hnr[sepref_fr_rules]:
  \<open>(find_unassigned_lit_wl_D_code, PR_CONST find_unassigned_lit_wl_D)
  \<in> [find_unassigned_lit_wl_D_pre]\<^sub>a
    twl_st_assn\<^sup>d \<rightarrow> twl_st_assn *a option_assn unat_lit_assn\<close>
    (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
  \<in> [comp_PRE twl_st_heur
       (\<lambda>S. twl_struct_invs (twl_st_of_wl None S) \<and>
             literals_are_\<L>\<^sub>i\<^sub>n S \<and>
             get_conflict_wl S = None)
       (\<lambda>_ (M, N, U, D, WS, Q, vm, \<phi>, clvls).
           vm \<in> vmtf M \<and> phase_saving \<phi>)
       (\<lambda>_. True)]\<^sub>a hrp_comp (twl_st_heur_assn\<^sup>d)
                       twl_st_heur \<rightarrow> hr_comp
         (twl_st_heur_assn *a option_assn unat_lit_assn)
         (twl_st_heur \<times>\<^sub>f \<langle>nat_lit_lit_rel\<rangle>option_rel)\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF find_unassigned_lit_wl_D_heur_hnr[unfolded PR_CONST_def]
        find_unassigned_lit_wl_D'_find_unassigned_lit_wl_D[unfolded PR_CONST_def]]
    unfolding PR_CONST_def
    .
  have pre: \<open>?pre x \<Longrightarrow> ?pre' x\<close> for x
    unfolding comp_PRE_def find_unassigned_lit_wl_D_pre_def
      by (auto simp: comp_PRE_def twl_st_assn_def twl_st_heur_def
          map_fun_rel_def intro!: ext)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def[symmetric]
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f apply assumption
    using pre ..
qed

lemma decide_wl_or_skip_D_helper:
  assumes
    \<open>decide_wl_or_skip_D_pre (a, aa, ab, ac, ad, ae, af, b)\<close>
  shows \<open>find_unassigned_lit_wl_D_pre (a, aa, ab, ac, ad, ae, af, b)\<close> and
     \<open>get_conflict_wl (a, aa, ab, ac, ad, ae, af, b) = None\<close>
  using assms unfolding decide_wl_or_skip_D_pre_def find_unassigned_lit_wl_D_pre_def
  decide_wl_or_skip_pre_def decide_l_or_skip_pre_def
  by auto

definition decide_lit_wl_heur :: \<open>nat literal \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur\<close> where
  \<open>decide_lit_wl_heur = (\<lambda>L' (M, N, U, D, Q, W, vmtf, \<phi>, clvls, cach, lbd, stats).
      (Decided L' # M, N, U, D, {#- L'#}, W, vmtf, \<phi>, clvls, cach, lbd, incr_decision stats))\<close>

lemma decide_lit_wl_heur_decide_lit_wl:
  \<open>(uncurry (RETURN oo decide_lit_wl_heur), uncurry (RETURN oo decide_lit_wl)) \<in>
     [\<lambda>(L, S). undefined_lit (get_trail_wl S) L \<and> get_conflict_wl S = None]\<^sub>f nat_lit_lit_rel \<times>\<^sub>r twl_st_heur \<rightarrow> \<langle>twl_st_heur\<rangle>nres_rel\<close>
  unfolding decide_lit_wl_heur_def decide_lit_wl_def
  by (intro frefI nres_relI)
    (auto simp: twl_st_heur_def intro: vmtf_consD)


sepref_thm decide_lit_wl_code
  is \<open>uncurry (RETURN oo (PR_CONST decide_lit_wl_heur))\<close>
  :: \<open>[\<lambda>(L, (M, N, U, D, WS, Q, vm, \<phi>)). undefined_lit M L \<and> L \<in> snd ` D\<^sub>0]\<^sub>a
     unat_lit_assn\<^sup>k *\<^sub>a twl_st_heur_assn\<^sup>d \<rightarrow> twl_st_heur_assn\<close>
  supply [[goals_limit=1]] find_unassigned_lit_wl_D_code_helper[simp]
  unfolding decide_lit_wl_heur_def twl_st_heur_assn_def PR_CONST_def
    cons_trail_Decided_def[symmetric]
  apply (rewrite at \<open>(_, add_mset _ \<hole>, _)\<close> lms_fold_custom_empty)+
  by sepref

concrete_definition (in -) decide_lit_wl_code
  uses isasat_input_bounded_nempty.decide_lit_wl_code.refine_raw
  is \<open>(uncurry ?f, _) \<in> _\<close>

prepare_code_thms (in -) decide_lit_wl_code_def

lemmas decide_lit_wl_heur_hnr[sepref_fr_rules] =
  decide_lit_wl_code.refine[OF isasat_input_bounded_nempty_axioms]

lemma decide_lit_wl_hnr[sepref_fr_rules]:
  \<open>(uncurry decide_lit_wl_code, uncurry (RETURN \<circ>\<circ> decide_lit_wl))
  \<in> [\<lambda>(L, S). undefined_lit (get_trail_wl S) L  \<and> L \<in> snd ` D\<^sub>0 \<and>
      get_conflict_wl S = None]\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a twl_st_assn\<^sup>d \<rightarrow>  twl_st_assn\<close>
    (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
  \<in> [comp_PRE (nat_lit_lit_rel \<times>\<^sub>f twl_st_heur)
       (\<lambda>(L, S). undefined_lit (get_trail_wl S) L \<and>
           get_conflict_wl S = None)
       (\<lambda>_ (L, M, N, U, D, WS, Q, vm, \<phi>).
           undefined_lit M L \<and> L \<in> snd ` D\<^sub>0)
       (\<lambda>_. True)]\<^sub>a hrp_comp
                       (unat_lit_assn\<^sup>k *\<^sub>a
                        twl_st_heur_assn\<^sup>d)
                       (nat_lit_lit_rel \<times>\<^sub>f
                        twl_st_heur) \<rightarrow> hr_comp
           twl_st_heur_assn twl_st_heur\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF decide_lit_wl_heur_hnr[unfolded PR_CONST_def]
        decide_lit_wl_heur_decide_lit_wl] .
  have pre: \<open>?pre x \<Longrightarrow> ?pre' x\<close> for x
    by (auto simp: comp_PRE_def twl_st_heur_def image_image intro!: ext)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f apply assumption
    using pre ..
qed

sepref_register decide_wl_or_skip_D find_unassigned_lit_wl_D
sepref_thm decide_wl_or_skip_D_code
  is \<open>PR_CONST decide_wl_or_skip_D\<close>
  :: \<open>twl_st_assn\<^sup>d \<rightarrow>\<^sub>a bool_assn *a twl_st_assn\<close>
  unfolding decide_wl_or_skip_D_def PR_CONST_def
  supply [[goals_limit = 1]] decide_wl_or_skip_D_helper[simp, intro]
    find_unassigned_lit_wl_D_def[simp] image_image[simp]
  by sepref

concrete_definition (in -) decide_wl_or_skip_D_code
  uses isasat_input_bounded_nempty.decide_wl_or_skip_D_code.refine_raw
  is \<open>(?f, _) \<in> _\<close>

prepare_code_thms (in -) decide_wl_or_skip_D_code_def

lemmas decide_wl_or_skip_D_hnr[sepref_fr_rules] =
  decide_wl_or_skip_D_code.refine[OF isasat_input_bounded_nempty_axioms]


paragraph \<open>Combining Together: the Other Rules\<close>

sepref_register get_conflict_wl_is_None

sepref_register cdcl_twl_o_prog_wl_D
sepref_thm cdcl_twl_o_prog_wl_D_code
  is \<open>PR_CONST cdcl_twl_o_prog_wl_D\<close>
  :: \<open>twl_st_assn\<^sup>d \<rightarrow>\<^sub>a bool_assn *a twl_st_assn\<close>
  unfolding cdcl_twl_o_prog_wl_D_def PR_CONST_def
  unfolding get_conflict_wl_is_None get_conflict_wl_get_conflict_wl_is_Nil
    get_conflict_wl_is_None_def[symmetric]
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) cdcl_twl_o_prog_wl_D_code
   uses isasat_input_bounded_nempty.cdcl_twl_o_prog_wl_D_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) cdcl_twl_o_prog_wl_D_code_def

lemmas cdcl_twl_o_prog_wl_D_code[sepref_fr_rules] =
   cdcl_twl_o_prog_wl_D_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]


paragraph \<open>Combining Together: Full Strategy\<close>

sepref_register cdcl_twl_stgy_prog_wl_D
sepref_thm cdcl_twl_stgy_prog_wl_D_code
  is \<open>PR_CONST cdcl_twl_stgy_prog_wl_D\<close>
  :: \<open>twl_st_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_assn\<close>
  unfolding cdcl_twl_stgy_prog_wl_D_def PR_CONST_def
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