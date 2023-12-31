theory IsaSAT_Decide
  imports IsaSAT_Decide_Defs
begin

lemma (in -)not_is_None_not_None: \<open>\<not>is_None s \<Longrightarrow> s \<noteq> None\<close>
  by (auto split: option.splits)


definition bump_find_next_undef where \<open>
  bump_find_next_undef \<A> x M = (case x of Bump_Heuristics hstable focused foc tobmp \<Rightarrow>
  if foc then do {
    L \<leftarrow> vmtf_find_next_undef \<A> focused M;
    RETURN (L, Bump_Heuristics hstable (update_next_search L focused) foc tobmp)
    } else  do {
    (L, hstable) \<leftarrow> acids_find_next_undef \<A> hstable M;
    RETURN (L, Bump_Heuristics hstable focused foc tobmp)
  })\<close>

definition bump_find_next_undef_upd
  :: \<open>nat multiset \<Rightarrow> (nat,nat)ann_lits \<Rightarrow> bump_heuristics \<Rightarrow>
        (((nat,nat)ann_lits \<times> bump_heuristics) \<times> nat option)nres\<close>
where
  \<open>bump_find_next_undef_upd \<A> = (\<lambda>M vm. do{
      (L, vm) \<leftarrow> bump_find_next_undef \<A> vm M;
      RETURN ((M, vm), L)
  })\<close>


lemma isa_bump_find_next_undef_bump_find_next_undef:
  \<open>(uncurry isa_bump_find_next_undef, uncurry (bump_find_next_undef \<A>)) \<in>
      Id \<times>\<^sub>r trail_pol \<A>  \<rightarrow>\<^sub>f \<langle>\<langle>nat_rel\<rangle>option_rel \<times>\<^sub>r Id\<rangle>nres_rel \<close>
  unfolding isa_bump_find_next_undef_def bump_find_next_undef_def uncurry_def
    defined_atm_def[symmetric]
  apply (intro frefI nres_relI)
  apply (case_tac \<open>x\<close>, case_tac \<open>fst x\<close>,  case_tac \<open>y\<close>, case_tac \<open>fst y\<close>, hypsubst, clarsimp simp only: fst_conv tuple4.case)
  apply (refine_rcg isa_vmtf_find_next_undef_vmtf_find_next_undef[THEN fref_to_Down_curry]
    isa_acids_find_next_undef_acids_find_next_undef[THEN fref_to_Down_curry])
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  done

lemma isa_vmtf_find_next_undef_vmtf_find_next_undef:
  \<open>(uncurry isa_vmtf_find_next_undef_upd, uncurry (bump_find_next_undef_upd \<A>)) \<in>
       trail_pol \<A>  \<times>\<^sub>r  Id \<rightarrow>\<^sub>f
          \<langle>trail_pol \<A> \<times>\<^sub>f Id \<times>\<^sub>f  \<langle>nat_rel\<rangle>option_rel\<rangle>nres_rel \<close>
  unfolding isa_vmtf_find_next_undef_upd_def isa_vmtf_find_next_undef_upd_def uncurry_def
    defined_atm_def[symmetric] bump_find_next_undef_upd_def
  apply (intro frefI nres_relI)
  apply (refine_rcg isa_bump_find_next_undef_bump_find_next_undef[THEN fref_to_Down_curry])
  subgoal by auto
  subgoal by (auto simp: update_next_search_def split: prod.splits)
  done
term isa_bump_find_next_undef
term bump_find_next_undef
lemma bump_find_next_undef_ref:
  assumes
    vmtf: \<open>x \<in> bump_heur \<A> M\<close>
  shows \<open>bump_find_next_undef \<A> x M
    \<le> \<Down> Id (SPEC (\<lambda>(L, bmp).
        (L \<noteq> None \<longrightarrow> bmp \<in> bump_heur \<A> (Decided (Pos (the L)) # M)) \<and>
        (L = None \<longrightarrow> bmp \<in> bump_heur \<A> M) \<and>
        (L = None \<longrightarrow> (\<forall>L\<in>#\<L>\<^sub>a\<^sub>l\<^sub>l \<A>. defined_lit M L)) \<and>
    (L \<noteq> None \<longrightarrow> Pos (the L) \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A> \<and> undefined_lit M (Pos (the L)))))\<close>
  using assms
  unfolding bump_find_next_undef_def
  apply (cases \<open>get_focused_heuristics x\<close>; cases \<open>get_stable_heuristics x\<close>)
  apply (cases x, simp only: tuple4.case)
  by (refine_vcg lhs_step_If)
   (auto intro!: vmtf_find_next_undef_ref[THEN order_trans]
      acids_find_next_undef[THEN order_trans] dest: vmtf_consD
    simp: bump_heur_def update_next_search_def)

definition find_undefined_atm
  :: \<open>nat multiset \<Rightarrow> (nat,nat) ann_lits \<Rightarrow> bump_heuristics \<Rightarrow>
       (((nat,nat) ann_lits \<times> bump_heuristics) \<times> nat option) nres\<close>
where
  \<open>find_undefined_atm \<A> M _ = SPEC(\<lambda>((M', vm), L).
     (L \<noteq> None \<longrightarrow> Pos (the L) \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A> \<and> undefined_atm M (the L)) \<and>
  (L = None \<longrightarrow> (\<forall>K\<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>. defined_lit M K)) \<and> M = M' \<and>
  (L = None \<longrightarrow> vm \<in> bump_heur \<A> M)\<and>
  (L \<noteq> None \<longrightarrow> vm \<in> bump_heur \<A> (Decided (Pos (the L)) # M)))\<close>

definition lit_of_found_atm_D_pre where
\<open>lit_of_found_atm_D_pre \<A> = (\<lambda>((\<phi>, _), L). L \<noteq> None \<longrightarrow>
       (the L \<le> unat32_max div 2 \<and> the L \<in># \<A> \<and> phase_save_heur_rel \<A> \<phi> ))\<close>

lemma lit_of_found_atm_D_pre:
  \<open>heuristic_rel \<A> heur \<Longrightarrow> isasat_input_bounded \<A> \<Longrightarrow> (L \<noteq> None \<Longrightarrow> the L \<in># \<A>) \<Longrightarrow>
    get_saved_phase_option_heur_pre (L) (get_content heur)\<close>
  by (auto simp: lit_of_found_atm_D_pre_def phase_saving_def heuristic_rel_def phase_save_heur_rel_def
    get_saved_phase_option_heur_pre_def get_next_phase_pre_def heuristic_rel_stats_def get_next_phase_heur_pre_stats_def
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

definition twl_st_heur_decide_find :: \<open>nat literal \<Rightarrow> (isasat \<times> nat twl_st_wl) set\<close> where
[unfolded Let_def]: \<open>twl_st_heur_decide_find L =
  {(S, T).
  let M' = get_trail_wl_heur S; N' = get_clauses_wl_heur S; D' = get_conflict_wl_heur S;
    W' = get_watched_wl_heur S; j = literals_to_update_wl_heur S; outl = get_outlearned_heur S;
    cach = get_conflict_cach S; clvls = get_count_max_lvls_heur S;
    vm = get_vmtf_heur S;
    vdom = get_aivdom S; heur = get_heur S; old_arena = get_old_arena S;
    lcount = get_learned_count S;
    occs = get_occs S in
  let M = get_trail_wl T; LM = Decided (L) # get_trail_wl T;
      N = get_clauses_wl T;  D = get_conflict_wl T;
      Q = literals_to_update_wl T;
      W = get_watched_wl T; N0 = get_init_clauses0_wl T; U0 = get_learned_clauses0_wl T;
      NS = get_subsumed_init_clauses_wl T; US = get_subsumed_learned_clauses_wl T;
      NEk = get_kept_unit_init_clss_wl T; UEk = get_kept_unit_learned_clss_wl T;
      NE = get_unkept_unit_init_clss_wl T; UE = get_unkept_unit_learned_clss_wl T in
    (M', M) \<in> trail_pol (all_atms_st T) \<and>
    valid_arena N' N (set (get_vdom_aivdom vdom)) \<and>
    (D', D) \<in> option_lookup_clause_rel (all_atms_st T) \<and>
    (D = None \<longrightarrow> j \<le> length M) \<and>
    Q = uminus `# lit_of `# mset (drop j (rev M)) \<and>
    (W', W) \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 (all_atms_st T)) \<and>
    vm \<in> bump_heur (all_atms_st T) LM \<and>
    no_dup M \<and>
    clvls \<in> counts_maximum_level M D \<and>
    cach_refinement_empty (all_atms_st T) cach \<and>
    out_learned M D outl \<and>
    clss_size_corr N NE UE NEk UEk NS US N0 U0 lcount \<and>
    vdom_m (all_atms_st T) W N \<subseteq> set (get_vdom_aivdom vdom) \<and>
    aivdom_inv_dec vdom (dom_m N) \<and>
    isasat_input_bounded (all_atms_st T) \<and>
    isasat_input_nempty (all_atms_st T) \<and>
    old_arena = [] \<and>
    heuristic_rel (all_atms_st T) heur \<and>
    (occs, empty_occs_list (all_atms_st T)) \<in> occurrence_list_ref
  }\<close>


abbreviation twl_st_heur_decide_find'''
   :: \<open>nat literal \<Rightarrow> nat \<Rightarrow> (isasat \<times> nat twl_st_wl) set\<close>
where
\<open>twl_st_heur_decide_find''' L r \<equiv> {(S, T). (S, T) \<in> twl_st_heur_decide_find L \<and>
           length (get_clauses_wl_heur S) = r}\<close>

lemma vmtf_find_next_undef_upd:
  \<open>(uncurry (bump_find_next_undef_upd \<A>), uncurry (find_undefined_atm \<A>)) \<in>
     [\<lambda>(M, vm). vm \<in> bump_heur \<A> M]\<^sub>f Id \<times>\<^sub>f Id \<rightarrow> \<langle>Id \<times>\<^sub>f Id \<times>\<^sub>f \<langle>nat_rel\<rangle>option_rel\<rangle>nres_rel\<close>
  unfolding bump_find_next_undef_upd_def find_undefined_atm_def
    update_next_search_def uncurry_def
  apply (intro frefI nres_relI)
  apply (clarify)
  apply (rule bind_refine_spec)
   prefer 2
   apply (rule bump_find_next_undef_ref[simplified])
  by (auto intro!: RETURN_SPEC_refine simp: image_image defined_atm_def[symmetric])

lemma find_unassigned_lit_wl_D'_find_unassigned_lit_wl_D:
  \<open>(find_unassigned_lit_wl_D_heur, find_unassigned_lit_wl) \<in>
     [find_unassigned_lit_wl_D_heur_pre]\<^sub>f
    {(S, T). (S, T) \<in> twl_st_heur''' r \<and> learned_clss_count S = u} \<rightarrow>
  \<langle>{((T, L), (T', L')). (L \<noteq> None \<longrightarrow> (T, T') \<in> twl_st_heur_decide_find''' (the L) r)  \<and>
         (L = None \<longrightarrow> (T, T') \<in> twl_st_heur''' r)  \<and>  L = L' \<and> learned_clss_count T = u \<and>
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
             (L \<noteq> None \<longrightarrow> vm \<in> bump_heur (all_atms_st (bt, bu, bv, bw, bx, by, bz, baa, bab)) (Decided (Pos (the A)) # bt)) \<and>
             (L = None \<longrightarrow> vm \<in> bump_heur (all_atms_st (bt, bu, bv, bw, bx, by, bz, baa, bab)) bt) \<and>
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
	 of _ _ bt \<open>get_vmtf_heur S\<close>])
      subgoal by fast
      subgoal
	 using pol by (cases \<open>get_vmtf_heur S\<close>) (auto simp: twl_st_heur_def all_atms_def[symmetric])
      apply (rule order.trans)
      apply (rule ref_two_step')
      apply (rule vmtf_find_next_undef_upd[THEN fref_to_Down_curry, of ?\<A> bt \<open>get_vmtf_heur S\<close>])
      subgoal using T by (auto simp: all_atms_def twl_st_heur_def)
      subgoal by auto
      subgoal using pre
        apply (cases bab)
	apply (auto 5 0 simp: find_undefined_atm_def unassigned_atm_def conc_fun_RES all_atms_def[symmetric]
	   mset_take_mset_drop_mset'
	   intro!: RES_refine intro: )
	apply (auto intro:  simp: defined_atm_def)
	apply (rule_tac x = \<open>Some (Pos ya)\<close> in exI)
	apply (auto intro: simp: defined_atm_def  in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n
	  in_set_all_atms_iff)
	apply (rule_tac x = \<open>Some (Pos y)\<close> in exI)
	apply (auto intro: simp: defined_atm_def  in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n
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
  have [simp]: \<open>vmtf \<A> (Decided (Pos (atm_of ap)) # aa) = vmtf \<A> (Decided ap # aa)\<close>
    \<open>vmtf \<A> (Decided (-ap) # aa) = vmtf \<A> (Decided ap # aa)\<close> for \<A> ap aa
    unfolding vmtf_def vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def
    by auto
  have [simp]: \<open>acids \<A> (Decided (Pos (atm_of ap)) # aa) = acids \<A> (Decided ap # aa)\<close>
    \<open>acids \<A> (Decided (-ap) # aa) = acids \<A> (Decided ap # aa)\<close> for \<A> ap aa
    unfolding acids_def defined_lit_map
    by auto
  have [simp]: \<open>bump_heur \<A> (Decided (Pos (atm_of ap)) # aa)= bump_heur \<A> (Decided ap # aa)\<close>
    \<open>bump_heur \<A> (Decided (-ap) # aa) = bump_heur \<A> (Decided ap # aa)\<close> for \<A> ap aa bc
    unfolding bump_heur_def
    by auto
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
      (clarsimp_all simp: twl_st_heur_def twl_st_heur_decide_find_def unassigned_atm_def atm_of_eq_atm_of uminus_\<A>\<^sub>i\<^sub>n_iff learned_clss_count_def
         all_lits_st_alt_def[symmetric]
        simp del: twl_st_of_wl.simps dest!: intro!: RETURN_RES_refine;
        auto simp: atm_of_eq_atm_of uminus_\<A>\<^sub>i\<^sub>n_iff all_atms_st_def; fail)+
    done
qed


lemma nofail_get_next_phase:
  \<open>get_next_phase_heur_pre_stats True L  (get_restart_heuristics \<phi>) \<Longrightarrow>
                nofail (get_next_phase_heur b L \<phi>)\<close>
  by (cases \<phi>) (auto simp: phase_save_heur_rel_def phase_saving_def get_next_phase_heur_def get_next_phase_heur_stats_def
    get_next_phase_heur_pre_stats_def get_next_phase_stats_def
    nofail_def bind_ASSERT_eq_if \<L>\<^sub>a\<^sub>l\<^sub>l_add_mset atms_of_def get_next_phase_pre_def split: if_splits
    dest!: multi_member_split)


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
    \<open>bump_heur \<A> (cons_trail_Decided L M) = bump_heur \<A> (Decided L # M)\<close>
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
    (L \<noteq> None \<longrightarrow> (T, T') \<in> twl_st_heur_decide_find''' (the L) r) \<and>
    (L = None \<longrightarrow> (T, T') \<in> twl_st_heur''' r) \<and>
    L = L' \<and>
    learned_clss_count T = u \<and>
    (L \<noteq> None \<longrightarrow>
     undefined_lit (get_trail_wl T') (the L) \<and> the L \<in># all_lits_st T') \<and>
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
	  (use that(2) in \<open>auto simp: twl_st_heur_decide_find_def twl_st_heur_def st all_atms_def[symmetric]\<close>)
      subgoal
        by (rule cons_trail_Decided_tr_pre[of _ \<open>get_trail_wl x1\<close> \<open>all_atms_st x1\<close>])
	  (use that(2) in \<open>auto simp: twl_st_heur_decide_find_def st all_atms_def[symmetric]
          all_lits_st_alt_def[symmetric]\<close>)
      subgoal
        using that(2) unfolding cons_trail_Decided_def[symmetric] st
        apply (clarsimp simp: twl_st_heur_def)[]
        apply (clarsimp simp add: twl_st_heur_def twl_st_heur_decide_find_def all_atms_def[symmetric]
	   isa_length_trail_length_u[THEN fref_to_Down_unRET_Id] out_learned_def
          all_lits_st_alt_def[symmetric] all_atms_st_cons_trail_empty_Q
	  intro!: cons_trail_Decided_tr[THEN fref_to_Down_unRET_uncurry]
	    isa_vmtf_consD)
        by (auto simp add: twl_st_heur_def all_atms_def[symmetric] learned_clss_count_def
	   isa_length_trail_length_u[THEN fref_to_Down_unRET_Id] out_learned_def
          all_lits_st_alt_def[symmetric] all_atms_st_cons_trail_empty_Q
	  intro!: cons_trail_Decided_tr[THEN fref_to_Down_unRET_uncurry]
	    isa_vmtf_consD)
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
    by (rule final; assumption?)
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

lemma decide_wl_or_skip_D_heur'_decide_wl_or_skip_D_heur2:
  \<open>(decide_wl_or_skip_D_heur', decide_wl_or_skip_D_heur) \<in> Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (use decide_wl_or_skip_D_heur'_decide_wl_or_skip_D_heur in auto)

end
