theory IsaSAT_Decide
  imports IsaSAT_Setup IsaSAT_VMTF
begin


chapter \<open>Decide\<close>

lemma (in -)not_is_None_not_None: \<open>\<not>is_None s \<Longrightarrow> s \<noteq> None\<close>
  by (auto split: option.splits)

definition vmtf_find_next_undef_upd
  :: \<open>nat multiset \<Rightarrow> (nat,nat)ann_lits \<Rightarrow> vmtf_remove_int \<Rightarrow>
        (((nat,nat)ann_lits \<times> vmtf_remove_int) \<times> nat option)nres\<close>
where
  \<open>vmtf_find_next_undef_upd \<A> = (\<lambda>M vm. do{
      L \<leftarrow> vmtf_find_next_undef \<A> vm M;
      RETURN ((M, update_next_search L vm), L)
  })\<close>

definition isa_vmtf_find_next_undef_upd
  :: \<open>trail_pol \<Rightarrow> isa_vmtf_remove_int \<Rightarrow>
        ((trail_pol \<times> isa_vmtf_remove_int) \<times> nat option)nres\<close>
where
  \<open>isa_vmtf_find_next_undef_upd = (\<lambda>M vm. do{
      L \<leftarrow> isa_vmtf_find_next_undef vm M;
      RETURN ((M, update_next_search L vm), L)
  })\<close>

lemma isa_vmtf_find_next_undef_vmtf_find_next_undef:
  \<open>(uncurry isa_vmtf_find_next_undef_upd, uncurry (vmtf_find_next_undef_upd \<A>)) \<in>
       trail_pol \<A>  \<times>\<^sub>r  (Id \<times>\<^sub>r distinct_atoms_rel \<A>) \<rightarrow>\<^sub>f
          \<langle>trail_pol \<A> \<times>\<^sub>f  (Id \<times>\<^sub>r distinct_atoms_rel \<A>) \<times>\<^sub>f  \<langle>nat_rel\<rangle>option_rel\<rangle>nres_rel \<close>
  unfolding isa_vmtf_find_next_undef_upd_def vmtf_find_next_undef_upd_def uncurry_def
    defined_atm_def[symmetric]
  apply (intro frefI nres_relI)
  apply (refine_rcg isa_vmtf_find_next_undef_vmtf_find_next_undef[THEN fref_to_Down_curry])
  subgoal by auto
  subgoal by (auto simp: update_next_search_def split: prod.splits)
  done

definition lit_of_found_atm where
\<open>lit_of_found_atm \<phi> L = SPEC (\<lambda>K. (L = None \<longrightarrow> K = None) \<and>
    (L \<noteq> None \<longrightarrow> K \<noteq> None \<and> atm_of (the K) = the L))\<close>

definition find_undefined_atm
  :: \<open>nat multiset \<Rightarrow> (nat,nat) ann_lits \<Rightarrow> vmtf_remove_int \<Rightarrow>
       (((nat,nat) ann_lits \<times> vmtf_remove_int) \<times> nat option) nres\<close>
where
  \<open>find_undefined_atm \<A> M _ = SPEC(\<lambda>((M', vm), L).
     (L \<noteq> None \<longrightarrow> Pos (the L) \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A> \<and> undefined_atm M (the L)) \<and>
     (L = None \<longrightarrow> (\<forall>K\<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>. defined_lit M K)) \<and> M = M' \<and> vm \<in> vmtf \<A> M)\<close>

definition lit_of_found_atm_D_pre where
\<open>lit_of_found_atm_D_pre \<A> = (\<lambda>((\<phi>, _), L). L \<noteq> None \<longrightarrow>
       (the L \<le> uint32_max div 2 \<and> the L \<in># \<A> \<and> phase_save_heur_rel \<A> \<phi> ))\<close>

definition get_saved_phase_heur_pre :: \<open>nat option \<Rightarrow> restart_heuristics \<Rightarrow> bool\<close> where
  \<open>get_saved_phase_heur_pre L = (\<lambda>heur.
       L \<noteq> None \<longrightarrow> get_next_phase_heur_pre_stats True (the L) heur)\<close>

definition find_unassigned_lit_wl_D_heur
  :: \<open>isasat \<Rightarrow> (isasat \<times> nat literal option) nres\<close>
where
  \<open>find_unassigned_lit_wl_D_heur = (\<lambda>S. do {
      let M = get_trail_wl_heur S;
      let vm = get_vmtf_heur S;
      let heur = get_heur S;
      let heur = set_fully_propagated_heur heur;
      ((M, vm), L) \<leftarrow> isa_vmtf_find_next_undef_upd M vm;
      ASSERT(get_saved_phase_heur_pre (L) (get_content heur));
        L \<leftarrow> lit_of_found_atm heur L;
      let S = set_trail_wl_heur M S;
      let S = set_vmtf_wl_heur vm S;
      let S = set_heur_wl_heur heur S;
      RETURN (S, L)
    })\<close>

lemma lit_of_found_atm_D_pre:
  \<open>heuristic_rel \<A> heur \<Longrightarrow> isasat_input_bounded \<A> \<Longrightarrow> (L \<noteq> None \<Longrightarrow> the L \<in># \<A>) \<Longrightarrow>
    get_saved_phase_heur_pre (L) (get_content heur)\<close>
  by (auto simp: lit_of_found_atm_D_pre_def phase_saving_def heuristic_rel_def phase_save_heur_rel_def
    get_saved_phase_heur_pre_def get_next_phase_pre_def heuristic_rel_stats_def get_next_phase_heur_pre_stats_def
    atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff dest: bspec[of _ _ \<open>Pos (the L)\<close>])

definition find_unassigned_lit_wl_D_heur_pre where
  \<open>find_unassigned_lit_wl_D_heur_pre S \<longleftrightarrow>
    (
      \<exists>T U.
        (S, T) \<in> state_wl_l None \<and>
        (T, U) \<in> twl_st_l None \<and>
        twl_struct_invs U \<and>
        literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st S) S \<and>
        get_conflict_wl S = None
    )\<close>

lemma vmtf_find_next_undef_upd:
  \<open>(uncurry (vmtf_find_next_undef_upd \<A>), uncurry (find_undefined_atm \<A>)) \<in>
     [\<lambda>(M, vm). vm \<in> vmtf \<A> M]\<^sub>f Id \<times>\<^sub>f Id \<rightarrow> \<langle>Id \<times>\<^sub>f Id \<times>\<^sub>f \<langle>nat_rel\<rangle>option_rel\<rangle>nres_rel\<close>
  unfolding vmtf_find_next_undef_upd_def find_undefined_atm_def
    update_next_search_def uncurry_def
  apply (intro frefI nres_relI)
  apply (clarify)
  apply (rule bind_refine_spec)
   prefer 2
   apply (rule vmtf_find_next_undef_ref[simplified])
  by (auto intro!: RETURN_SPEC_refine simp: image_image defined_atm_def[symmetric])

lemma find_unassigned_lit_wl_D'_find_unassigned_lit_wl_D:
  \<open>(find_unassigned_lit_wl_D_heur, find_unassigned_lit_wl) \<in>
     [find_unassigned_lit_wl_D_heur_pre]\<^sub>f
    {(S, T). (S, T) \<in> twl_st_heur''' r \<and> learned_clss_count S = u} \<rightarrow>
     \<langle>{((T, L), (T', L')). (T, T') \<in> twl_st_heur''' r  \<and> L = L' \<and> learned_clss_count T = u \<and>
         (L \<noteq> None \<longrightarrow> undefined_lit (get_trail_wl T') (the L) \<and> the L \<in># all_lits_st T') \<and>
         get_conflict_wl T' = None}\<rangle>nres_rel\<close>
proof -
  have [simp]: \<open>undefined_lit M (Pos (atm_of y)) = undefined_lit M y\<close> for M y
    by (auto simp: defined_lit_map)
  have [simp]: \<open>defined_atm M (atm_of y) = defined_lit M y\<close> for M y
    by (auto simp: defined_lit_map defined_atm_def)

  have ID_R: \<open>Id \<times>\<^sub>r \<langle>Id\<rangle>option_rel = Id\<close>
    by auto

  define unassigned_atm where
     \<open>unassigned_atm S L \<longleftrightarrow> (\<exists> M N D NE UE NS US WS Q.
         S = (M, N, D, NE, UE, NS, US, WS, Q) \<and>
         (L \<noteq> None \<longrightarrow>
            undefined_lit M (the L) \<and> the L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st S) \<and>
            atm_of (the L) \<in># all_atms_st S) \<and>
         (L = None \<longrightarrow> (\<nexists>L'. undefined_lit M L' \<and>
             atm_of L' \<in># all_atms_st S)))\<close>
    for L :: \<open>nat literal option\<close> and S :: \<open>nat twl_st_wl\<close>

  have all_lits_st_atm: \<open>L \<in># all_lits_st S \<longleftrightarrow> atm_of L \<in># all_atms_st S\<close> for L S
    unfolding all_lits_st_def all_atms_st_def in_all_lits_of_mm_ain_atms_of_iff
      all_lits_def all_atms_def by (metis atm_of_all_lits_of_mm(1))

  have find_unassigned_lit_wl_D_alt_def:
   \<open>find_unassigned_lit_wl S = do {
     L \<leftarrow> SPEC(unassigned_atm S);
     L \<leftarrow> RES {L, map_option uminus L};
     SPEC(\<lambda>((M, N, D, NE, UE, N0, U0, WS, Q), L').
         S = (M, N, D, NE, UE, N0, U0, WS, Q) \<and> L = L')
   }\<close> for S
   unfolding find_unassigned_lit_wl_def RES_RES_RETURN_RES unassigned_atm_def
    RES_RES_RETURN_RES all_lits_def in_all_lits_of_mm_ain_atms_of_iff
    in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n in_set_all_atms_iff all_lits_st_atm
  by (cases S) auto

  have isa_vmtf_find_next_undef_upd:
    \<open>isa_vmtf_find_next_undef_upd (get_trail_wl_heur S)
       (get_vmtf_heur S)
      \<le> \<Down> {(((M, vm), A), L). A = map_option atm_of L \<and>
              unassigned_atm (bt, bu, bv, bw, bx, by, bz, baa, bab) L \<and>
             vm \<in> isa_vmtf (all_atms_st (bt, bu, bv, bw, bx, by, bz, baa, bab)) bt \<and>
             (L \<noteq> None \<longrightarrow> the A \<in># all_atms_st (bt, bu, bv, bw, bx, by, bz, baa, bab)) \<and>
             (M, bt) \<in> trail_pol (all_atms_st (bt, bu, bv, bw, bx, by, bz, baa, bab))}
         (SPEC (unassigned_atm (bt, bu, bv, bw, bx, by, bz, baa, bab)))\<close>
	  (is \<open>_ \<le> \<Down> ?find _\<close>)
    if
      pre: \<open>find_unassigned_lit_wl_D_heur_pre (bt, bu, bv, bw, bx, by, bz, baa, bab)\<close> and
      T: \<open>(S,
	bt, bu, bv, bw, bx, by, bz, baa, bab)
       \<in> twl_st_heur\<close> and
      \<open>r =
       length
	(get_clauses_wl_heur
	  S)\<close>
     for a aa ab ac ad b ae af ag ba ah ai aj ak al am bb an bc ao ap aq bd ar as at
	 au av aw be ax ay az bf bg bh bi bj bk bl bm bn bo bp bq br bs bt bu bv
	 bw bx "by" bz heur baa bab stats S
  proof -
    let ?\<A> = \<open>all_atms_st (bt, bu, bv, bw, bx, by, bz, baa, bab)\<close>
    have pol:
      \<open>(get_trail_wl_heur S, bt) \<in> trail_pol ?\<A>\<close>
      using that by (cases bz; auto simp: twl_st_heur_def)
    obtain vm0 where
       vm0: \<open>(snd (get_vmtf_heur S), vm0) \<in> distinct_atoms_rel ?\<A>\<close> and
       vm: \<open>((fst (get_vmtf_heur S)), vm0) \<in> vmtf ?\<A> bt\<close>
      using T by (cases bz; cases \<open>get_vmtf_heur S\<close>; auto simp: twl_st_heur_def isa_vmtf_def)
    have [intro]:
       \<open>Multiset.Ball (\<L>\<^sub>a\<^sub>l\<^sub>l ?\<A>) (defined_lit bt) \<Longrightarrow>
	 atm_of L' \<in># ?\<A> \<Longrightarrow>
		undefined_lit bt L'\<Longrightarrow> False\<close> for L'
      by (auto simp: atms_of_ms_def
	   all_lits_of_mm_union ran_m_def all_lits_of_mm_add_mset \<L>\<^sub>a\<^sub>l\<^sub>l_union
	   eq_commute[of _ \<open>the (fmlookup _ _)\<close>] \<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_all_lits_of_m
	  atms_of_def \<L>\<^sub>a\<^sub>l\<^sub>l_add_mset
	 dest!: multi_member_split
	  )

    show ?thesis
      apply (rule order.trans)
      apply (rule isa_vmtf_find_next_undef_vmtf_find_next_undef[of ?\<A>, THEN fref_to_Down_curry,
	 of _ _ bt \<open>(fst (get_vmtf_heur S), vm0)\<close>])
      subgoal by fast
      subgoal
	 using pol vm0 by (cases \<open>get_vmtf_heur S\<close>) (auto simp: twl_st_heur_def all_atms_def[symmetric])
      apply (rule order.trans)
      apply (rule ref_two_step')
      apply (rule vmtf_find_next_undef_upd[THEN fref_to_Down_curry, of ?\<A> bt \<open>(fst (get_vmtf_heur S), vm0)\<close>])
      subgoal using vm by (auto simp: all_atms_def)
      subgoal by auto
      subgoal using vm vm0 pre
        apply (cases bab)
	apply (auto 5 0 simp: find_undefined_atm_def unassigned_atm_def conc_fun_RES all_atms_def[symmetric]
	   mset_take_mset_drop_mset'
	   intro!: RES_refine intro: isa_vmtfI)
	apply (auto intro: isa_vmtfI simp: defined_atm_def)
	apply (rule_tac x = \<open>Some (Pos y)\<close> in exI)
	apply (auto intro: isa_vmtfI simp: defined_atm_def  in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n
	 in_set_all_atms_iff)
	done
    done
  qed

  have lit_of_found_atm: \<open>lit_of_found_atm ao' x2a
	\<le> \<Down> {(L, L'). L = L' \<and> map_option atm_of  L = x2a}
	   (RES {L, map_option uminus L})\<close>
    if
      \<open>find_unassigned_lit_wl_D_heur_pre (bt, bu, bv, bw, bx, by, bz, baa, bab)\<close> and
      \<open>(S, bt, bu, bv, bw, bx, by, bz, baa, bab) \<in> twl_st_heur\<close> and
      \<open>r = length (get_clauses_wl_heur S)\<close> and
      \<open>(x, L) \<in> ?find bt bu bv bw bx by bz baa bab\<close> and
      \<open>x1 = (x1a, x2)\<close> and
      \<open>x = (x1, x2a)\<close>
     for a aa ab ac ad b ae af ag ba ah ai aj ak al am bb an bc ao ap aq bd ar as at
       au av aw be ax ay az bf bg bh bi bj bk bl bm bn bo bp bq br bs bt bu bv
       bw bx "by" bz x L x1 x1a x2 x2a heur baa bab ao' stats S
  proof -
    show ?thesis
      using that unfolding lit_of_found_atm_def
      by (auto simp: atm_of_eq_atm_of twl_st_heur_def intro!: RES_refine)
  qed
  have [dest]: \<open>find_unassigned_lit_wl_D_heur_pre (ca, cb, cc, cd, ce, cf, cg, ch, ci, cx, cy) \<Longrightarrow> cc = None\<close>
    for ca cb cc cd ce cf cg ch ci cy cx
    unfolding find_unassigned_lit_wl_D_heur_pre_def by auto
  show ?thesis
    unfolding find_unassigned_lit_wl_D_heur_def find_unassigned_lit_wl_D_alt_def find_undefined_atm_def
      ID_R Let_def
    apply (intro frefI nres_relI)
    apply clarify
    apply refine_vcg
    apply (rule isa_vmtf_find_next_undef_upd; assumption)
    subgoal
      by (rule lit_of_found_atm_D_pre)
       (auto simp add: twl_st_heur_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff Ball_def image_image
        mset_take_mset_drop_mset' all_atms_def[symmetric] unassigned_atm_def
          simp del: twl_st_of_wl.simps dest!: intro!: RETURN_RES_refine)
    apply (rule lit_of_found_atm; assumption)
    subgoal for a aa ab ac ad b ae af ag ba ah ai aj ak al am bb an bc ao L L'
      by (cases am)
       (clarsimp_all simp: twl_st_heur_def unassigned_atm_def atm_of_eq_atm_of uminus_\<A>\<^sub>i\<^sub>n_iff learned_clss_count_def
         all_lits_st_alt_def[symmetric]
        simp del: twl_st_of_wl.simps dest!: intro!: RETURN_RES_refine;
        auto simp: atm_of_eq_atm_of uminus_\<A>\<^sub>i\<^sub>n_iff all_atms_st_def; fail)+
    done
qed



definition lit_of_found_atm_D
  :: \<open>isasat_restart_heuristics \<Rightarrow>  nat option \<Rightarrow> (nat literal option)nres\<close> where
  \<open>lit_of_found_atm_D = (\<lambda>heur L. do{
      case L of
        None \<Rightarrow> RETURN None
      | Some L \<Rightarrow> do {
          b \<leftarrow> get_next_phase_heur (current_restart_phase heur = QUIET_PHASE) L heur;
          if b
          then RETURN (Some (Pos L)) else RETURN (Some (Neg L))
        }
  })\<close>

lemma nofail_get_next_phase:
  \<open>get_next_phase_heur_pre_stats True L  (get_restart_heuristics \<phi>) \<Longrightarrow>
                nofail (get_next_phase_heur b L \<phi>)\<close>
  by (cases \<phi>) (auto simp: phase_save_heur_rel_def phase_saving_def get_next_phase_heur_def get_next_phase_heur_stats_def
    get_next_phase_heur_pre_stats_def get_next_phase_stats_def
    nofail_def bind_ASSERT_eq_if \<L>\<^sub>a\<^sub>l\<^sub>l_add_mset atms_of_def get_next_phase_pre_def split: if_splits
    dest!: multi_member_split)
    term get_saved_phase_heur_pre 
lemma lit_of_found_atm_D_lit_of_found_atm:
  \<open>(uncurry lit_of_found_atm_D, uncurry lit_of_found_atm) \<in>
  [\<lambda>((\<phi>), x). get_saved_phase_heur_pre x (get_restart_heuristics \<phi>)]\<^sub>f Id \<times>\<^sub>f Id \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  unfolding lit_of_found_atm_D_def lit_of_found_atm_def uncurry_def
  by (auto split: option.splits if_splits simp: pw_le_iff refine_pw_simps lit_of_found_atm_D_pre_def
    nofail_get_next_phase get_saved_phase_heur_pre_def  nofail_get_next_phase)

definition decide_lit_wl_heur :: \<open>nat literal \<Rightarrow> isasat \<Rightarrow> isasat nres\<close> where
  \<open>decide_lit_wl_heur = (\<lambda>L' S. do {
      let M = get_trail_wl_heur S;
      let stats = get_stats_heur S;
      ASSERT(isa_length_trail_pre M);
      let j = isa_length_trail M;
      let S = set_literals_to_update_wl_heur j S;
      ASSERT(cons_trail_Decided_tr_pre (L', M));
      let M = cons_trail_Decided_tr L' M;
      let S = set_trail_wl_heur M S;
      let S = set_stats_wl_heur stats S;
      RETURN S})\<close>

definition mop_get_saved_phase_heur_st :: \<open>nat \<Rightarrow> isasat \<Rightarrow> bool nres\<close> where
   \<open>mop_get_saved_phase_heur_st = (\<lambda>L S. mop_get_saved_phase_heur L (get_heur S))\<close>

definition decide_wl_or_skip_D_heur
  :: \<open>isasat \<Rightarrow> (bool \<times> isasat) nres\<close>
where
  \<open>decide_wl_or_skip_D_heur S = (do {
    (S, L) \<leftarrow> find_unassigned_lit_wl_D_heur S;
    case L of
      None \<Rightarrow> RETURN (True, S)
    | Some L \<Rightarrow> do {
        T \<leftarrow> decide_lit_wl_heur L S;
        RETURN (False, T)}
  })
\<close>

lemma all_atms_st_cons_trail_Decided[simp]:
  \<open>all_atms_st (cons_trail_Decided x'a x1b, oth) = all_atms_st (x1b, oth)\<close> and
  all_atms_st_cons_trail_empty_Q:
  \<open>NO_MATCH {#} Q \<Longrightarrow>
     all_atms_st (x1b, N, D, NS, US, NEk, UEk, NE, UE, N0, U0, Q, W) = all_atms_st (x1b, N, D, NS, US, NEk, UEk, NE, UE, N0, U0, {#}, W)\<close>
  by (cases oth) (auto simp: cons_trail_Decided_def all_atms_st_def)

lemma decide_wl_or_skip_D_heur_decide_wl_or_skip_D:
  \<open>(decide_wl_or_skip_D_heur, decide_wl_or_skip) \<in>
    {(S, T). (S, T) \<in> twl_st_heur''' r \<and> learned_clss_count S =u} \<rightarrow>\<^sub>f
    \<langle>bool_rel \<times>\<^sub>f {(S, T). (S, T) \<in> twl_st_heur''' r \<and> learned_clss_count S =u}\<rangle> nres_rel\<close>
  (is \<open>_ \<in> ?A \<rightarrow>\<^sub>f _\<close>)
proof -
  have [simp]:
    \<open>rev (cons_trail_Decided L M) = rev M @ [Decided L]\<close>
    \<open>no_dup (cons_trail_Decided L M) = no_dup (Decided L # M)\<close>
    \<open>isa_vmtf \<A> (cons_trail_Decided L M) = isa_vmtf \<A> (Decided L # M)\<close>
    for M L \<A>
    by (auto simp: cons_trail_Decided_def)

  have final: \<open>decide_lit_wl_heur xb x1a
	\<le> SPEC
	   (\<lambda>T.  do {
                  RETURN (False, T)}
		\<le> SPEC
		   (\<lambda>c. (c, False, decide_lit_wl x'a x1)
			\<in> bool_rel \<times>\<^sub>f ?A))\<close>
    if
      \<open>(x, y) \<in> {(S, T). (S, T) \<in> twl_st_heur''' r \<and> learned_clss_count S = u}\<close> and
      \<open>(xa, x')
       \<in> {((T, L), T', L').
	  (T, T') \<in> ?A \<and>
	  L = L' \<and>
	  (L \<noteq> None \<longrightarrow>
	   undefined_lit (get_trail_wl T') (the L) \<and>
	   the L \<in># all_lits_st T') \<and>
	  get_conflict_wl T' = None}\<close> and
      st:
        \<open>x' = (x1, x2)\<close>
        \<open>xa = (x1a, x2a)\<close>
        \<open>x2a = Some xb\<close>
        \<open>x2 = Some x'a\<close> and
      \<open>(xb, x'a) \<in> nat_lit_lit_rel\<close>
    for x y xa x' x1 x2 x1a x2a xb x'a
  proof -
    show ?thesis
      unfolding decide_lit_wl_heur_def
        decide_lit_wl_def
      apply refine_vcg
      subgoal
        by (rule isa_length_trail_pre[of _ \<open>get_trail_wl x1\<close> \<open>all_atms_st x1\<close>])
	  (use that(2) in \<open>auto simp: twl_st_heur_def st all_atms_def[symmetric]\<close>)
      subgoal
        by (rule cons_trail_Decided_tr_pre[of _ \<open>get_trail_wl x1\<close> \<open>all_atms_st x1\<close>])
	  (use that(2) in \<open>auto simp: twl_st_heur_def st all_atms_def[symmetric]
          all_lits_st_alt_def[symmetric]\<close>)
      subgoal
        using that(2) unfolding cons_trail_Decided_def[symmetric] st
        apply (clarsimp simp: twl_st_heur_def)[]
        apply (clarsimp simp add: twl_st_heur_def all_atms_def[symmetric]
	   isa_length_trail_length_u[THEN fref_to_Down_unRET_Id] out_learned_def
          all_lits_st_alt_def[symmetric] all_atms_st_cons_trail_empty_Q
	  intro!: cons_trail_Decided_tr[THEN fref_to_Down_unRET_uncurry]
	    isa_vmtf_consD2)
        by (auto simp add: twl_st_heur_def all_atms_def[symmetric] learned_clss_count_def
	   isa_length_trail_length_u[THEN fref_to_Down_unRET_Id] out_learned_def
          all_lits_st_alt_def[symmetric] all_atms_st_cons_trail_empty_Q
	  intro!: cons_trail_Decided_tr[THEN fref_to_Down_unRET_uncurry]
	    isa_vmtf_consD2)
      done
  qed

  have decide_wl_or_skip_alt_def: \<open>decide_wl_or_skip S = (do {
    ASSERT(decide_wl_or_skip_pre S);
    (S, L) \<leftarrow> find_unassigned_lit_wl S;
    case L of
      None \<Rightarrow> RETURN (True, S)
    | Some L \<Rightarrow> RETURN (False, decide_lit_wl L S)
  })\<close> for S
  unfolding decide_wl_or_skip_def by auto
  show ?thesis
    supply [[goals_limit=1]]
    unfolding decide_wl_or_skip_D_heur_def decide_wl_or_skip_alt_def decide_wl_or_skip_pre_def
     decide_l_or_skip_pre_def twl_st_of_wl.simps[symmetric]
    apply (intro nres_relI frefI same_in_Id_option_rel)
    apply (refine_vcg find_unassigned_lit_wl_D'_find_unassigned_lit_wl_D[of r u, THEN fref_to_Down])
    subgoal for x y
      unfolding decide_wl_or_skip_pre_def find_unassigned_lit_wl_D_heur_pre_def
	decide_wl_or_skip_pre_def decide_l_or_skip_pre_def decide_or_skip_pre_def
       apply normalize_goal+
       apply (rule_tac x = xa in exI)
       apply (rule_tac x = xb in exI)
       apply auto
       done
    apply (rule same_in_Id_option_rel)
    subgoal by (auto simp del: simp: twl_st_heur_def)
    subgoal by auto
      apply (rule final; assumption?)
      apply auto
    done
 qed


lemma bind_triple_unfold:
  \<open>do {
    ((M, vm), L) \<leftarrow> (P :: _ nres);
    f ((M, vm), L)
} =
do {
    x \<leftarrow> P;
    f x
}\<close>
  by (intro bind_cong) auto

definition get_next_phase_st :: \<open>bool \<Rightarrow> nat \<Rightarrow> isasat \<Rightarrow> (bool) nres\<close> where
  \<open>get_next_phase_st = (\<lambda>b L S.
     (get_next_phase_heur b L (get_heur S)))\<close>

definition find_unassigned_lit_wl_D_heur2
  :: \<open>isasat \<Rightarrow> (isasat \<times> nat option) nres\<close>
where
  \<open>find_unassigned_lit_wl_D_heur2 = (\<lambda>S. do {
      ((M, vm), L) \<leftarrow> isa_vmtf_find_next_undef_upd (get_trail_wl_heur S) (get_vmtf_heur S);
      RETURN (set_heur_wl_heur (set_fully_propagated_heur (get_heur S)) (set_trail_wl_heur M (set_vmtf_wl_heur vm S)), L)
    })\<close>

definition decide_wl_or_skip_D_heur' where
  \<open>decide_wl_or_skip_D_heur' = (\<lambda>S. do {
      (S, L) \<leftarrow> find_unassigned_lit_wl_D_heur2 S;
      ASSERT(get_saved_phase_heur_pre L (get_restart_heuristics (get_heur S)));
      case L of
       None \<Rightarrow> RETURN (True, S)
     | Some L \<Rightarrow> do {
        L \<leftarrow> do {
            b \<leftarrow> get_next_phase_st (get_target_opts S = TARGET_ALWAYS \<or>
                   (get_target_opts S = TARGET_QUIET_ONLY \<and> get_restart_phase S = QUIET_PHASE)) L S;
              RETURN (if b then Pos L else Neg L)};
        T \<leftarrow> decide_lit_wl_heur L S;
        RETURN (False, T)
      }
    })
\<close>
lemma decide_wl_or_skip_D_heur'_decide_wl_or_skip_D_heur:
  \<open>decide_wl_or_skip_D_heur' S \<le> \<Down>Id (decide_wl_or_skip_D_heur S)\<close>
proof -
  have [iff]:
    \<open>{K. (\<exists>y. K = Some y) \<and> atm_of (the K) = x2d} = {Some (Pos x2d), Some (Neg x2d)}\<close> for x2d
    apply (auto simp: atm_of_eq_atm_of)
    apply (case_tac y)
    apply auto
    done
  have H: \<open>do {
    L \<leftarrow>do {ASSERT \<phi>; P};
    Q L} =
    do {ASSERT \<phi>; L \<leftarrow> P; Q L} \<close> for P Q \<phi>
    by auto
  have H: \<open>A \<le> \<Down>Id B \<Longrightarrow> B \<le> \<Down>Id A \<Longrightarrow>A = B\<close> for A B
    by auto
  have K: \<open>RES {Some (Pos x2), Some (Neg x2)} \<le> \<Down> {(x, y). x = Some y} (RES {Pos x2, Neg x2})\<close>
    \<open>RES {(Pos x2), (Neg x2)} \<le> \<Down> {(y, x). x = Some y} (RES {Some (Pos x2), Some (Neg x2)})\<close>  for x2
    by (auto intro!: RES_refine)
  have [simp]: \<open>IsaSAT_Decide.get_saved_phase_heur_pre a (get_restart_heuristics (set_fully_propagated_heur (S))) =
    IsaSAT_Decide.get_saved_phase_heur_pre a (get_restart_heuristics (S))\<close> for S a
    by (cases S)(auto simp: IsaSAT_Decide.get_saved_phase_heur_pre_def get_next_phase_heur_pre_stats_def
      get_next_phase_pre_def set_fully_propagated_heur_def set_fully_propagated_heur_stats_def)
  have S: \<open>decide_wl_or_skip_D_heur S =
       (do {
                   ((M, vm), L) \<leftarrow> isa_vmtf_find_next_undef_upd (get_trail_wl_heur S) (get_vmtf_heur S);
                   ASSERT (IsaSAT_Decide.get_saved_phase_heur_pre L (get_restart_heuristics (get_heur S)));
                   case L of None \<Rightarrow> RETURN (True, set_heur_wl_heur (set_fully_propagated_heur (get_heur S)) (set_vmtf_wl_heur vm (set_trail_wl_heur M S)))
                     | Some L \<Rightarrow> do {
                       _ \<leftarrow> SPEC (\<lambda>_::bool. True);
                       L \<leftarrow>RES {Pos L, Neg L};
                      T \<leftarrow> decide_lit_wl_heur L (set_heur_wl_heur (set_fully_propagated_heur (get_heur S)) (set_vmtf_wl_heur vm (set_trail_wl_heur M S)));
                      RETURN (False, T)
                     }})\<close> for S a b c d e f g h i  j k l m n p q r
     unfolding decide_wl_or_skip_D_heur_def find_unassigned_lit_wl_D_heur_def Let_def
     apply (auto intro!: bind_cong[OF refl] simp: lit_of_found_atm_def split: option.splits)
     apply (rule H)
     subgoal
       apply (refine_rcg K)
       apply auto
       done
     subgoal
       apply (refine_rcg K)
       apply auto
       done
     done
  have [refine]: \<open>get_saved_phase_heur_pre x2c (get_restart_heuristics XX) \<Longrightarrow>
     x2c = Some x'a \<Longrightarrow> XX=YY \<Longrightarrow>
    get_next_phase_heur b x'a YY \<le> (SPEC (\<lambda>_::bool. True))\<close> for x'a x1d x1e x1f x1g x2g b XX x2c YY
    by (auto simp: get_next_phase_heur_def get_saved_phase_heur_pre_def get_next_phase_pre_def
      get_next_phase_heur_stats_def get_next_phase_stats_def get_next_phase_heur_pre_stats_def
      split: prod.splits)
  have [refine]: \<open>xa =  x'a \<Longrightarrow> RETURN (if xb then Pos xa else Neg xa)
       \<le> \<Down> Id (RES {Pos x'a, Neg x'a})\<close> for xb x'a xa
    by auto
  have [refine]: \<open>decide_lit_wl_heur L S
    \<le> \<Down> Id
        (decide_lit_wl_heur La Sa)\<close> if \<open>(L, La) \<in> Id\<close> \<open>(S, Sa) \<in> Id\<close> for L La S Sa
    using that by auto
  have [intro!]: \<open>IsaSAT_Decide.get_saved_phase_heur_pre (snd pa) (get_restart_heuristics l) \<Longrightarrow>
    IsaSAT_Decide.get_saved_phase_heur_pre (snd pa) (get_restart_heuristics (set_fully_propagated_heur l))\<close> for pa l
    by (cases l; cases pa) (auto simp: IsaSAT_Decide.get_saved_phase_heur_pre_def get_next_phase_heur_pre_stats_def
      get_next_phase_pre_def set_fully_propagated_heur_stats_def
      set_fully_propagated_heur_def)
  show ?thesis
    apply (cases S, simp only: S)
    unfolding find_unassigned_lit_wl_D_heur_def
      nres_monad3 prod.case find_unassigned_lit_wl_D_heur_def
      prod.case decide_wl_or_skip_D_heur'_def get_next_phase_st_def
      find_unassigned_lit_wl_D_heur2_def
      case_prod_beta snd_conv fst_conv bind_to_let_conv
    apply (subst Let_def)
    apply (refine_vcg
      lit_of_found_atm_D_lit_of_found_atm[THEN fref_to_Down_curry, THEN order_trans]
      same_in_Id_option_rel)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    apply assumption back
    subgoal by auto
    subgoal by (auto simp: set_fully_propagated_heur_def split: prod.splits)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

lemma decide_wl_or_skip_D_heur'_decide_wl_or_skip_D_heur2:
  \<open>(decide_wl_or_skip_D_heur', decide_wl_or_skip_D_heur) \<in> Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (use decide_wl_or_skip_D_heur'_decide_wl_or_skip_D_heur in auto)

end