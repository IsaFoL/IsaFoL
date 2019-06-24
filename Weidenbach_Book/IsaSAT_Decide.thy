theory IsaSAT_Decide
  imports IsaSAT_Setup IsaSAT_VMTF
begin


paragraph \<open>Decide\<close>

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
\<open>lit_of_found_atm_D_pre = (\<lambda>(\<phi>, L). L \<noteq> None \<longrightarrow> (the L < length \<phi> \<and> the L \<le> uint32_max div 2))\<close>

definition find_unassigned_lit_wl_D_heur
  :: \<open>twl_st_wl_heur \<Rightarrow> (twl_st_wl_heur \<times> nat literal option) nres\<close>
where
  \<open>find_unassigned_lit_wl_D_heur = (\<lambda>(M, N, D, WS, Q, vm, \<phi>, clvls). do {
      ((M, vm), L) \<leftarrow> isa_vmtf_find_next_undef_upd M vm;
      ASSERT(lit_of_found_atm_D_pre (\<phi>, L));
      L \<leftarrow> lit_of_found_atm \<phi> L;
      RETURN ((M, N, D, WS, Q, vm, \<phi>, clvls), L)
    })\<close>

lemma lit_of_found_atm_D_pre:
  \<open>phase_saving \<A> \<phi> \<Longrightarrow> isasat_input_bounded \<A> \<Longrightarrow> (L \<noteq> None \<Longrightarrow> the L \<in># \<A>) \<Longrightarrow> lit_of_found_atm_D_pre (\<phi>, L)\<close>
  by (auto simp: lit_of_found_atm_D_pre_def phase_saving_def
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
  \<open>(find_unassigned_lit_wl_D_heur, find_unassigned_lit_wl_D) \<in>
     [find_unassigned_lit_wl_D_heur_pre]\<^sub>f
    twl_st_heur''' r \<rightarrow> \<langle>{((T, L), (T', L')). (T, T') \<in> twl_st_heur''' r  \<and> L = L' \<and>
         (L \<noteq> None \<longrightarrow> undefined_lit (get_trail_wl T') (the L) \<and> the L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st T')) \<and>
         get_conflict_wl T' = None}\<rangle>nres_rel\<close>
proof -
  have [simp]: \<open>undefined_lit M (Pos (atm_of y)) = undefined_lit M y\<close> for M y
    by (auto simp: defined_lit_map)
  have [simp]: \<open>defined_atm M (atm_of y) = defined_lit M y\<close> for M y
    by (auto simp: defined_lit_map defined_atm_def)

  have ID_R: \<open>Id \<times>\<^sub>r \<langle>Id\<rangle>option_rel = Id\<close>
    by auto
  have atms: \<open>atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st (M, N, D, NE, UE, WS, Q))) =
         atms_of_mm (mset `# init_clss_lf N) \<union>
         atms_of_mm NE \<and> D = None\<close> (is ?A) and
    atms_2: \<open>set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (all_atms N (NE + UE))) = set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (all_atms N NE))\<close> (is ?B) and
    atms_3: \<open>y \<in> atms_of_ms ((\<lambda>x. mset (fst x)) ` set_mset (ran_m N)) \<Longrightarrow>
       y \<notin> atms_of_mm NE \<Longrightarrow>
       y \<in> atms_of_ms ((\<lambda>x. mset (fst x)) ` {a. a \<in># ran_m N \<and> snd a})\<close> (is \<open>?C1 \<Longrightarrow> ?C2 \<Longrightarrow>	?C\<close>)
      if inv: \<open>find_unassigned_lit_wl_D_heur_pre (M, N, D, NE, UE, WS, Q)\<close>
      for M N D NE UE WS Q y
  proof -
    obtain T U where
      S_T: \<open>((M, N, D, NE, UE, WS, Q), T) \<in> state_wl_l None\<close> and
      T_U: \<open>(T, U) \<in> twl_st_l None\<close> and
      inv: \<open>twl_struct_invs U\<close> and
      \<A>\<^sub>i\<^sub>n : \<open>literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st (M, N, D, NE, UE, WS, Q)) (M, N, D, NE, UE, WS, Q)\<close> and
      confl: \<open>get_conflict_wl (M, N, D, NE, UE, WS, Q) = None\<close>
      using inv unfolding find_unassigned_lit_wl_D_heur_pre_def
       apply - apply normalize_goal+
       by blast

    have \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of U)\<close> and
        unit: \<open>entailed_clss_inv U\<close>
      using inv unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      by fast+
    then show ?A
      using \<A>\<^sub>i\<^sub>n confl S_T T_U unfolding is_\<L>\<^sub>a\<^sub>l\<^sub>l_alt_def state_wl_l_def twl_st_l_def
      literals_are_\<L>\<^sub>i\<^sub>n_def all_atms_def all_lits_def
      apply -
      apply (subst (asm) all_clss_l_ran_m[symmetric], subst (asm) image_mset_union)+
      apply (subst all_clss_l_ran_m[symmetric], subst image_mset_union)
      by  (auto simp: cdcl\<^sub>W_restart_mset.no_strange_atm_def entailed_clss_inv.simps
          mset_take_mset_drop_mset mset_take_mset_drop_mset' atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n
          clauses_def simp del: entailed_clss_inv.simps)
    then show ?B and \<open>?C1 \<Longrightarrow> ?C2 \<Longrightarrow> ?C\<close>
      apply -
      unfolding atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n all_atms_def all_lits_def
      apply (subst (asm) all_clss_l_ran_m[symmetric], subst (asm) image_mset_union)+
      apply (subst all_clss_l_ran_m[symmetric], subst image_mset_union)+
      by (auto simp: in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n all_atms_def all_lits_def in_all_lits_of_mm_ain_atms_of_iff
        all_lits_of_mm_union atms_of_def \<L>\<^sub>a\<^sub>l\<^sub>l_union image_Un atm_of_eq_atm_of
	atm_of_all_lits_of_mm atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n)
  qed

  have [dest]: \<open>(S, T) \<in> twl_st_heur \<Longrightarrow> \<phi> = get_phase_saver_heur S \<Longrightarrow> phase_saving (all_atms_st T) \<phi>\<close> for S T \<phi>
    by (auto simp: twl_st_heur_def all_atms_def)
  define unassigned_atm where
    \<open>unassigned_atm S L \<equiv> \<exists> M N D NE UE WS Q.
         S = (M, N, D, NE, UE, WS, Q) \<and>
         (L \<noteq> None \<longrightarrow>
            undefined_lit M (the L) \<and> the L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms N NE) \<and>
            atm_of (the L) \<in> atms_of_mm (clause `# twl_clause_of `# init_clss_lf N + NE)) \<and>
         (L = None \<longrightarrow> (\<nexists>L'. undefined_lit M L' \<and>
            atm_of L' \<in> atms_of_mm (clause `# twl_clause_of `# init_clss_lf N + NE)))\<close>
    for L :: \<open>nat literal option\<close> and S :: \<open>nat twl_st_wl\<close>
  have find_unassigned_lit_wl_D_alt_def:
   \<open>find_unassigned_lit_wl_D S = do {
     L \<leftarrow>  SPEC(unassigned_atm S);
     L \<leftarrow> RES {L, map_option uminus L};
     SPEC(\<lambda>((M, N, D, NE, UE, WS, Q), L').
         S = (M, N, D, NE, UE, WS, Q) \<and> L = L')
   }\<close> for S
   unfolding find_unassigned_lit_wl_D_def RES_RES_RETURN_RES unassigned_atm_def
    RES_RES_RETURN_RES
    by (cases S) (auto simp: mset_take_mset_drop_mset' uminus_\<A>\<^sub>i\<^sub>n_iff)

  have isa_vmtf_find_next_undef_upd:
    \<open>isa_vmtf_find_next_undef_upd (a, aa, ab, ac, ad, b)
       ((aj, ak, al, am, bb), an, bc)
      \<le> \<Down> {(((M, vm), A), L). A = map_option atm_of L \<and>
              unassigned_atm (bt, bu, bv, bw, bx, by, bz) L \<and>
             vm \<in> isa_vmtf (all_atms_st (bt, bu, bv, bw, bx, by, bz)) bt \<and>
             (L \<noteq> None \<longrightarrow> the A \<in># all_atms_st (bt, bu, bv, bw, bx, by, bz)) \<and>
             (M, bt) \<in> trail_pol (all_atms_st (bt, bu, bv, bw, bx, by, bz))}
         (SPEC (unassigned_atm (bt, bu, bv, bw, bx, by, bz)))\<close>
	  (is \<open>_ \<le> \<Down> ?find _\<close>)
    if
      pre: \<open>find_unassigned_lit_wl_D_heur_pre (bt, bu, bv, bw, bx, by, bz)\<close> and
      T: \<open>(((a, aa, ab, ac, ad, b), ae, (af, ag, ba), ah, ai,
	 ((aj, ak, al, am, bb), an, bc), ao, ap, (aq, bd), ar, as,
	 (at, au, av, aw, be), (ax, ay, az, bf, bg), (bh, bi, bj, bk, bl),
	 (bm, bn), bo, bp, bq, br, bs),
	bt, bu, bv, bw, bx, by, bz)
       \<in> twl_st_heur\<close> and
      \<open>r =
       length
	(get_clauses_wl_heur
	  ((a, aa, ab, ac, ad, b), ae, (af, ag, ba), ah, ai,
	   ((aj, ak, al, am, bb), an, bc), ao, ap, (aq, bd), ar, as,
	   (at, au, av, aw, be), (ax, ay, az, bf, bg), (bh, bi, bj, bk, bl),
	   (bm, bn), bo, bp, bq, br, bs))\<close>
     for a aa ab ac ad b ae af ag ba ah ai aj ak al am bb an bc ao ap aq bd ar as at
	 au av aw be ax ay az bf bg bh bi bj bk bl bm bn bo bp bq br bs bt bu bv
	 bw bx "by" bz
  proof -
    let ?\<A> = \<open>all_atms_st (bt, bu, bv, bw, bx, by, bz)\<close>
    have pol:
      \<open>((a, aa, ab, ac, ad, b), bt) \<in> trail_pol (all_atms bu (bw + bx))\<close>
      using that by (auto simp: twl_st_heur_def all_atms_def[symmetric])
    obtain vm0 where
      vm0: \<open>((an, bc), vm0) \<in> distinct_atoms_rel (all_atms bu (bw + bx))\<close> and
      vm: \<open>((aj, ak, al, am, bb), vm0) \<in> vmtf (all_atms bu (bw + bx)) bt\<close>
      using T by (auto simp: twl_st_heur_def all_atms_def[symmetric] isa_vmtf_def)
    have [intro]: \<open>Multiset.Ball (\<L>\<^sub>a\<^sub>l\<^sub>l (all_atms bu (bw + bx))) (defined_lit bt) \<Longrightarrow>
	 atm_of L'
	 \<in> atms_of_ms ((\<lambda>x. mset (fst x)) ` {a. a \<in># ran_m bu \<and> snd a}) \<Longrightarrow>
		undefined_lit bt L' \<Longrightarrow> False\<close>
       \<open>Multiset.Ball (\<L>\<^sub>a\<^sub>l\<^sub>l (all_atms bu (bw + bx))) (defined_lit bt) \<Longrightarrow>
	 atm_of L'
	 \<in> atms_of_mm bw \<Longrightarrow>
		undefined_lit bt L' \<Longrightarrow> False\<close>
       \<open>Multiset.Ball (\<L>\<^sub>a\<^sub>l\<^sub>l (all_atms bu (bw + bx))) (defined_lit bt) \<Longrightarrow>
	 atm_of L'
	 \<in> atms_of_mm bx \<Longrightarrow>
		undefined_lit bt L'\<Longrightarrow> False\<close> for L'
      by (auto simp: all_atms_def atms_of_ms_def atm_of_eq_atm_of all_lits_def
	   all_lits_of_mm_union ran_m_def all_lits_of_mm_add_mset \<L>\<^sub>a\<^sub>l\<^sub>l_union
	   eq_commute[of _ \<open>the (fmlookup _ _)\<close>] \<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_all_lits_of_m
	  atms_of_def
	 dest!: multi_member_split
	  )

    show ?thesis
      apply (rule order.trans)
      apply (rule isa_vmtf_find_next_undef_vmtf_find_next_undef[of ?\<A>, THEN fref_to_Down_curry,
	 of _ _ bt \<open>((aj, ak, al, am, bb), vm0)\<close>])
      subgoal by fast
      subgoal
	 using pol vm0 by (auto simp: twl_st_heur_def all_atms_def[symmetric])
      apply (rule order.trans)
      apply (rule ref_two_step')
      apply (rule vmtf_find_next_undef_upd[THEN fref_to_Down_curry, of ?\<A> bt \<open>((aj, ak, al, am, bb), vm0)\<close>])
      subgoal using vm by (auto simp: all_atms_def)
      subgoal by auto
      subgoal using vm vm0 pre
	apply (auto 5 0 simp: find_undefined_atm_def unassigned_atm_def conc_fun_RES all_atms_def[symmetric]
	   mset_take_mset_drop_mset' atms_2 defined_atm_def
	   intro!: RES_refine intro: isa_vmtfI)
	apply (auto intro: isa_vmtfI simp: defined_atm_def atms_2)
	apply (rule_tac x = \<open>Some (Pos y)\<close> in exI)
	apply (auto intro: isa_vmtfI simp: defined_atm_def atms_2  in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n
	 in_set_all_atms_iff atms_3)
	done
    done
  qed

  have lit_of_found_atm: \<open>lit_of_found_atm ao x2a
	\<le> \<Down> {(L, L'). L = L' \<and> map_option atm_of  L = x2a}
	   (RES {L, map_option uminus L})\<close>
    if
      \<open>find_unassigned_lit_wl_D_heur_pre (bt, bu, bv, bw, bx, by, bz)\<close> and
      \<open>(((a, aa, ab, ac, ad, b), ae, (af, ag, ba), ah, ai,
	 ((aj, ak, al, am, bb), an, bc), ao, ap, (aq, bd), ar, as,
	 (at, au, av, aw, be), (ax, ay, az, bf, bg), (bh, bi, bj, bk, bl),
	 (bm, bn), bo, bp, bq, br, bs),
	bt, bu, bv, bw, bx, by, bz)
       \<in> twl_st_heur\<close> and
      \<open>r =
       length
	(get_clauses_wl_heur
	  ((a, aa, ab, ac, ad, b), ae, (af, ag, ba), ah, ai,
	   ((aj, ak, al, am, bb), an, bc), ao, ap, (aq, bd), ar, as,
	   (at, au, av, aw, be), (ax, ay, az, bf, bg), (bh, bi, bj, bk, bl),
	   (bm, bn), bo, bp, bq, br, bs))\<close> and
      \<open>(x, L) \<in> ?find bt bu bv bw bx by bz\<close> and
      \<open>x1 = (x1a, x2)\<close> and
      \<open>x = (x1, x2a)\<close>
     for a aa ab ac ad b ae af ag ba ah ai aj ak al am bb an bc ao ap aq bd ar as at
       au av aw be ax ay az bf bg bh bi bj bk bl bm bn bo bp bq br bs bt bu bv
       bw bx "by" bz x L x1 x1a x2 x2a
  proof -
    show ?thesis
      using that unfolding lit_of_found_atm_def
      by (auto simp: atm_of_eq_atm_of twl_st_heur_def intro!: RES_refine)
  qed
  show ?thesis
    unfolding find_unassigned_lit_wl_D_heur_def find_unassigned_lit_wl_D_alt_def find_undefined_atm_def
      ID_R
    apply (intro frefI nres_relI)
    apply clarify
    apply refine_vcg
    apply (rule isa_vmtf_find_next_undef_upd; assumption)
    subgoal
      by (rule lit_of_found_atm_D_pre)
       (auto simp add: twl_st_heur_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff Ball_def image_image
        mset_take_mset_drop_mset' atms all_atms_def[symmetric] unassigned_atm_def
          simp del: twl_st_of_wl.simps dest!: atms intro!: RETURN_RES_refine)
    apply (rule lit_of_found_atm; assumption)
    subgoal
      by (auto simp add: twl_st_heur_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff Ball_def image_image
        mset_take_mset_drop_mset' atms all_atms_def[symmetric] unassigned_atm_def
        atm_of_eq_atm_of
          simp del: twl_st_of_wl.simps dest!: atms intro!: RETURN_RES_refine)
    done
qed



definition lit_of_found_atm_D
  :: \<open>bool list \<Rightarrow> nat option \<Rightarrow> (nat literal option)nres\<close> where
  \<open>lit_of_found_atm_D = (\<lambda>(\<phi>::bool list) L. do{
      case L of
        None \<Rightarrow> RETURN None
      | Some L \<Rightarrow> do {
          if \<phi>!L then RETURN (Some (Pos L)) else RETURN (Some (Neg L))
        }
  })\<close>


lemma lit_of_found_atm_D_lit_of_found_atm:
  \<open>(uncurry lit_of_found_atm_D, uncurry lit_of_found_atm) \<in>
   [lit_of_found_atm_D_pre]\<^sub>f Id \<times>\<^sub>f Id \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  unfolding lit_of_found_atm_D_def lit_of_found_atm_def
  by (auto split: option.splits)



definition decide_lit_wl_heur :: \<open>nat literal \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close> where
  \<open>decide_lit_wl_heur = (\<lambda>L' (M, N, D, Q, W, vmtf, \<phi>, clvls, cach, lbd, outl, stats, fema, sema). do {
      ASSERT(isa_length_trail_pre M);
      let j = isa_length_trail M;
      ASSERT(cons_trail_Decided_tr_pre (L', M));
      RETURN (cons_trail_Decided_tr L' M, N, D, j, W, vmtf, \<phi>, clvls, cach, lbd, outl, incr_decision stats,
         fema, sema)})\<close>


definition decide_wl_or_skip_D_heur
  :: \<open>twl_st_wl_heur \<Rightarrow> (bool \<times> twl_st_wl_heur) nres\<close>
where
  \<open>decide_wl_or_skip_D_heur S = (do {
    (S, L) \<leftarrow> find_unassigned_lit_wl_D_heur S;
    case L of
      None \<Rightarrow> RETURN (True, S)
    | Some L \<Rightarrow> do {T \<leftarrow> decide_lit_wl_heur L S; RETURN (False, T)}
  })
\<close>

lemma decide_wl_or_skip_D_heur_decide_wl_or_skip_D:
  \<open>(decide_wl_or_skip_D_heur, decide_wl_or_skip_D) \<in> twl_st_heur''' r \<rightarrow>\<^sub>f \<langle>bool_rel \<times>\<^sub>f twl_st_heur''' r\<rangle> nres_rel\<close>
proof -
  have [simp]:
    \<open>rev (cons_trail_Decided L M) = rev M @ [Decided L]\<close>
    \<open>no_dup (cons_trail_Decided L M) = no_dup (Decided L # M)\<close>
    \<open>isa_vmtf \<A> (cons_trail_Decided L M) = isa_vmtf \<A> (Decided L # M)\<close>
    for M L \<A>
    by (auto simp: cons_trail_Decided_def)

  have final: \<open>decide_lit_wl_heur xb x1a
	\<le> SPEC
	   (\<lambda>T. RETURN (False, T)
		\<le> SPEC
		   (\<lambda>c. (c, False, decide_lit_wl x'a x1)
			\<in> bool_rel \<times>\<^sub>f twl_st_heur''' r))\<close>
    if
      \<open>(x, y) \<in> twl_st_heur''' r\<close> and
      \<open>decide_wl_or_skip_pre y \<and> literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st y) y\<close> and
      \<open>(xa, x')
       \<in> {((T, L), T', L').
	  (T, T') \<in> twl_st_heur''' r \<and>
	  L = L' \<and>
	  (L \<noteq> None \<longrightarrow>
	   undefined_lit (get_trail_wl T') (the L) \<and>
	   the L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st T')) \<and>
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
      apply (cases x1a)
      apply refine_vcg
      subgoal
        by (rule isa_length_trail_pre[of _ \<open>get_trail_wl x1\<close> \<open>all_atms_st x1\<close>])
	  (use that(3) in \<open>auto simp: twl_st_heur_def st all_atms_def[symmetric]\<close>)
      subgoal
        by (rule cons_trail_Decided_tr_pre[of _ \<open>get_trail_wl x1\<close> \<open>all_atms_st x1\<close>])
	  (use that(3) in \<open>auto simp: twl_st_heur_def st all_atms_def[symmetric]\<close>)
      subgoal
        using that(2,3) unfolding cons_trail_Decided_def[symmetric] st
        by (auto simp add: twl_st_heur_def all_atms_def[symmetric]
	   isa_length_trail_length_u[THEN fref_to_Down_unRET_Id] out_learned_def
	  intro!: cons_trail_Decided_tr[THEN fref_to_Down_unRET_uncurry]
	    isa_vmtf_consD2)
      done
  qed

  show ?thesis
    supply [[goals_limit=1]]
    unfolding decide_wl_or_skip_D_heur_def decide_wl_or_skip_D_def decide_wl_or_skip_D_pre_def
     decide_l_or_skip_pre_def twl_st_of_wl.simps[symmetric]
    apply (intro nres_relI frefI same_in_Id_option_rel)
    apply (refine_vcg find_unassigned_lit_wl_D'_find_unassigned_lit_wl_D[of r, THEN fref_to_Down])
    subgoal
      unfolding decide_wl_or_skip_pre_def find_unassigned_lit_wl_D_heur_pre_def
	decide_wl_or_skip_pre_def decide_l_or_skip_pre_def
       apply normalize_goal+
       apply (rule_tac x = xa in exI)
       apply (rule_tac x = xb in exI)
       apply auto
      done
    apply (rule same_in_Id_option_rel)
    subgoal by (auto simp del: simp: twl_st_heur_def)
    subgoal by (auto simp del: simp: twl_st_heur_def)
    apply (rule final; assumption)
    done
 qed

end