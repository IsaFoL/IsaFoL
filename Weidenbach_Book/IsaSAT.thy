theory IsaSAT
imports IsaSAT_Restart IsaSAT_Initialisation
begin

text \<open>
  We cannot use \<^term>\<open>cdcl_twl_stgy_restart\<close> since we do not always end in a final state
  for \<^term>\<open>cdcl_twl_stgy\<close>.
\<close>
definition conclusive_TWL_run :: \<open>'v twl_st \<Rightarrow> 'v twl_st nres\<close> where
  \<open>conclusive_TWL_run S =
     SPEC(\<lambda>T. \<exists>n n'. cdcl_twl_stgy_restart_with_leftovers\<^sup>*\<^sup>* (S, n) (T, n') \<and> final_twl_state T)\<close>


context isasat_input_bounded_nempty
begin
lemma cdcl_twl_stgy_restart_prog_spec: \<open>twl_struct_invs S \<Longrightarrow>
  twl_stgy_invs S \<Longrightarrow>
  clauses_to_update S = {#} \<Longrightarrow>
  get_conflict S = None \<Longrightarrow>
  cdcl_twl_stgy_restart_prog S \<le> conclusive_TWL_run S\<close>
  apply (rule order_trans)
  apply (rule cdcl_twl_stgy_prog_spec; assumption?)
  unfolding conclusive_TWL_run_def
  by auto

lemma cdcl_twl_stgy_restart_prog_l_spec_final:
  assumes
    \<open>cdcl_twl_stgy_prog_l_pre S S'\<close>
  shows
    \<open>cdcl_twl_stgy_restart_prog_l S \<le> \<Down> (twl_st_l None) (conclusive_TWL_run S')\<close>
  apply (rule order_trans[OF
     cdcl_twl_stgy_restart_prog_l_cdcl_twl_stgy_restart_prog[THEN fref_to_Down, of S S']])
  subgoal using assms unfolding cdcl_twl_stgy_prog_l_pre_def by auto
  subgoal using assms unfolding cdcl_twl_stgy_prog_l_pre_def by auto
  subgoal
    apply (rule ref_two_step)
     prefer 2
     apply (rule cdcl_twl_stgy_restart_prog_spec)
    using assms unfolding cdcl_twl_stgy_prog_l_pre_def by (auto simp: twl_st_l intro: conc_fun_R_mono)
  done

lemma cdcl_twl_stgy_restart_prog_wl_spec_final:
  assumes
    \<open>cdcl_twl_stgy_prog_wl_pre S S'\<close>
  shows
    \<open>cdcl_twl_stgy_restart_prog_wl S \<le> \<Down> (state_wl_l None O twl_st_l None) (conclusive_TWL_run S')\<close>
proof -
  obtain T where T: \<open>(S, T) \<in> state_wl_l None\<close> \<open>cdcl_twl_stgy_prog_l_pre T S'\<close> \<open>correct_watching S\<close>
    using assms unfolding cdcl_twl_stgy_prog_wl_pre_def by blast
  show ?thesis
    apply (rule order_trans[OF cdcl_twl_stgy_restart_prog_wl_spec["to_\<Down>", of S T]])
    subgoal using T by auto
    subgoal
      apply (rule order_trans)
      apply (rule ref_two_step')
       apply (rule cdcl_twl_stgy_restart_prog_l_spec_final[of _ S'])
      subgoal using T by fast
      subgoal unfolding conc_fun_chain by auto
      done
    done
qed

theorem cdcl_twl_stgy_restart_prog_wl_D_spec:
  assumes \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close>
  shows \<open>cdcl_twl_stgy_restart_prog_wl_D S \<le> \<Down> {(T', T). T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n T}
     (cdcl_twl_stgy_restart_prog_wl S)\<close>
proof -
  have 1: \<open>((False, S, 0), False, S, 0) \<in>
     {((brk', T', n'), brk, T, n). brk = brk' \<and> T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n T \<and> n = n'}\<close>
    using assms by fast
  have 2: \<open>unit_propagation_outer_loop_wl_D S \<le> \<Down> {(T', T). T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n T}
       (unit_propagation_outer_loop_wl T)\<close> if \<open>S = T\<close> \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close> for S T
    using unit_propagation_outer_loop_wl_D_spec[of S] that by fast
  have 3: \<open>cdcl_twl_o_prog_wl_D S \<le> \<Down> {((b', T'), b, T). b = b' \<and> T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n T}
    (cdcl_twl_o_prog_wl T)\<close> if \<open>S = T\<close> \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close> for S T
    using cdcl_twl_o_prog_wl_D_spec[of S] that by fast
  show ?thesis
    unfolding cdcl_twl_stgy_restart_prog_wl_D_def cdcl_twl_stgy_restart_prog_wl_def
    apply (refine_vcg 1 2 3 restart_prog_wl_D_restart_prog_wl[THEN fref_to_Down_curry2])
    subgoal by auto
    subgoal by auto
    subgoal by fast
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

lemma cdcl_twl_stgy_restart_prog_wl_D_spec_final:
  assumes
    \<open>cdcl_twl_stgy_prog_wl_D_pre S S'\<close>
  shows
    \<open>cdcl_twl_stgy_restart_prog_wl_D S \<le> \<Down> (state_wl_l None O twl_st_l None) (conclusive_TWL_run S')\<close>
proof -
  have T: \<open>cdcl_twl_stgy_prog_wl_pre S S' \<and> literals_are_\<L>\<^sub>i\<^sub>n S\<close>
    using assms unfolding cdcl_twl_stgy_prog_wl_D_pre_def by blast
  show ?thesis
    apply (rule order_trans[OF cdcl_twl_stgy_restart_prog_wl_D_spec])
    subgoal using T by auto
    subgoal
      apply (rule order_trans)
      apply (rule ref_two_step')
       apply (rule cdcl_twl_stgy_restart_prog_wl_spec_final[of _ S'])
      subgoal using T by fast
      subgoal unfolding conc_fun_chain by (rule conc_fun_R_mono) blast
      done
    done
qed
end

text \<open>This is temporary copy of IsaSAT and should replace it eventually.\<close>
lemma distinct_nat_of_uint32[iff]:
  \<open>distinct_mset (nat_of_uint32 `# A) \<longleftrightarrow> distinct_mset A\<close>
  \<open>distinct (map nat_of_uint32 xs) \<longleftrightarrow> distinct xs\<close>
  using distinct_image_mset_inj[of nat_of_uint32]
  by (auto simp: inj_on_def distinct_map)

definition cdcl_twl_stgy_restart_prog_wl_D where
  \<open>cdcl_twl_stgy_restart_prog_wl_D \<equiv> isasat_restart_ops.cdcl_twl_stgy_restart_prog_wl_D id\<close>

declare isasat_input_bounded.append_el_aa_hnr[sepref_fr_rules]
declare isasat_input_bounded.polarity_pol_code_polarity_refine[sepref_fr_rules]
  isasat_input_bounded.cons_trail_Propagated_tr_code_cons_trail_Propagated_tr[sepref_fr_rules]

definition conclusive_CDCL_run where
  \<open>conclusive_CDCL_run CS T U \<longleftrightarrow>
      (\<exists>n n'. cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart_stgy\<^sup>*\<^sup>* (T, n) (U, n') \<and> no_step cdcl\<^sub>W_restart_mset.cdcl\<^sub>W (U)) \<or>
          (CS \<noteq> {#} \<and> conflicting U \<noteq> None \<and> count_decided (trail U) = 0 \<and>
          unsatisfiable (set_mset CS))\<close>

text \<open>to get a full SAT:
  \<^item> either we fully apply \<^term>\<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<close> (up to restarts)
  \<^item> or we can stop early.
\<close>
definition SAT :: \<open>nat clauses \<Rightarrow> nat cdcl\<^sub>W_restart_mset nres\<close> where
  \<open>SAT CS = do{
    let T = init_state CS;
    SPEC (conclusive_CDCL_run CS T)
  }\<close>

text \<open>In the following program, the condition \<^term>\<open>length CS < uint_max - 1\<close> is only necessary
  to simplify the refinement and should not be necessary.\<close>
(* if b \<and> length CS < uint_max - 1 \<comment> \<open>simplifies the refinement\<close>
    then
     do {
      let S = isasat_input_ops.init_state_wl (mset_set \<A>\<^sub>i\<^sub>n');
      T \<leftarrow> init_dt_wl CS (to_init_state S);
      let T = from_init_state T;
      if get_conflict_wl T \<noteq> None
      then RETURN T
      else if CS = [] then RETURN (([], fmempty, None, {#}, {#}, {#}, \<lambda>_. undefined))
      else do {
         ASSERT (extract_atms_clss CS {} \<noteq> {});
         ASSERT(isasat_input_bounded_nempty (mset_set \<A>\<^sub>i\<^sub>n'));
         ASSERT(mset `# ran_mf (get_clauses_wl T) + get_unit_clauses_wl T = mset `# mset CS);
         ASSERT(learned_clss_l (get_clauses_wl T) = {#});
         isasat_input_ops.cdcl_twl_stgy_prog_break_wl_D (mset_set \<A>\<^sub>i\<^sub>n') (finalise_init T)
      }
   }
   else *)
definition (in -) SAT_wl :: \<open>nat clause_l list \<Rightarrow> nat twl_st_wl nres\<close> where
  \<open>SAT_wl CS = do{
    let \<A>\<^sub>i\<^sub>n' = extract_atms_clss CS {};
    b \<leftarrow> SPEC(\<lambda>_::bool. True);

  do {
      let S = isasat_input_ops.init_state_wl;
      T \<leftarrow> init_dt_wl_full CS (to_init_state S);
      let T = from_init_state T;
      if get_conflict_wl T \<noteq> None
      then RETURN T
      else if CS = [] then RETURN (([], fmempty, None, {#}, {#}, {#}, \<lambda>_. undefined))
      else do {
         ASSERT (extract_atms_clss CS {} \<noteq> {});
         ASSERT(isasat_input_bounded_nempty (mset_set \<A>\<^sub>i\<^sub>n'));
         ASSERT(mset `# ran_mf (get_clauses_wl T) + get_unit_clauses_wl T = mset `# mset CS);
         ASSERT(learned_clss_l (get_clauses_wl T) = {#});
         cdcl_twl_stgy_restart_prog_wl_D (mset_set \<A>\<^sub>i\<^sub>n') (finalise_init T)
      }
   }
  }\<close>


definition extract_model_of_state where
  \<open>extract_model_of_state U = Some (map lit_of (get_trail_wl U))\<close>

definition extract_model_of_state_heur where
  \<open>extract_model_of_state_heur U = Some (map lit_of (get_trail_wl_heur U))\<close>

definition extract_stats where
  [simp]: \<open>extract_stats U = None\<close>

definition extract_stats_init where
  [simp]: \<open>extract_stats_init = None\<close>

    (* if b \<and> length CS < uint_max - 1
    then do {
      let S = isasat_input_ops.init_state_wl \<A>\<^sub>i\<^sub>n';
      let S = to_init_state S;
      T \<leftarrow> init_dt_wl CS S;
      let T = from_init_state T;
      if \<not>get_conflict_wl_is_None_init T
      then RETURN (None)
      else if CS = [] then RETURN (Some [])
      else do {
         ASSERT(\<A>\<^sub>i\<^sub>n' \<noteq> {#});
         ASSERT(isasat_input_bounded_nempty \<A>\<^sub>i\<^sub>n');
         ASSERT(mset `# ran_mf (get_clauses_wl T) + get_unit_clauses_wl T = mset `# mset CS);
         ASSERT(size (learned_clss_l (get_clauses_wl T)) = 0);
         let T = finalise_init T;
         U \<leftarrow> isasat_input_ops.cdcl_twl_stgy_prog_break_wl_D \<A>\<^sub>i\<^sub>n' T;
         RETURN (if get_conflict_wl U = None then extract_model_of_state U else extract_stats U)
      }
    }
    else *)
definition IsaSAT :: \<open>nat clause_l list \<Rightarrow> nat literal list option nres\<close> where
  \<open>IsaSAT CS = do{
    let \<A>\<^sub>i\<^sub>n' = mset_set (extract_atms_clss CS {});
    ASSERT(isasat_input_bounded \<A>\<^sub>i\<^sub>n');
    ASSERT(distinct_mset \<A>\<^sub>i\<^sub>n');
    b \<leftarrow> SPEC(\<lambda>_::bool. True);
     do {
      let S = isasat_input_ops.init_state_wl;
      let S = to_init_state S;
      T \<leftarrow> init_dt_wl_full CS S;
      let T = from_init_state T;
      if \<not>get_conflict_wl_is_None_init T
      then RETURN (None)
      else if CS = [] then RETURN (Some [])
      else do {
         ASSERT(\<A>\<^sub>i\<^sub>n' \<noteq> {#});
         ASSERT(isasat_input_bounded_nempty \<A>\<^sub>i\<^sub>n');
         ASSERT(mset `# ran_mf (get_clauses_wl T) + get_unit_clauses_wl T = mset `# mset CS);
         ASSERT(size (learned_clss_l (get_clauses_wl T)) = 0);
         let T = finalise_init T;
         U \<leftarrow> cdcl_twl_stgy_restart_prog_wl_D \<A>\<^sub>i\<^sub>n' T;
         RETURN (if get_conflict_wl U = None then extract_model_of_state U else extract_stats U)
      }
    }
  }\<close>


definition extract_model_of_state_stat :: \<open>twl_st_wl_heur \<Rightarrow> nat literal list option \<times> stats\<close> where
  \<open>extract_model_of_state_stat U =
     (Some (map lit_of (rev (get_trail_wl_heur U))),
       (\<lambda>(M, _,  _, _, _ ,_ ,_ ,_, _, _, _, stat, _, _). stat) U)\<close>

definition extract_state_stat :: \<open>twl_st_wl_heur \<Rightarrow> nat literal list option \<times> stats\<close> where
  \<open>extract_state_stat U =
     (None,
       (\<lambda>(M, _, _, _, _ ,_ ,_ ,_, _, _, _, stat, _, _). stat) U)\<close>

definition empty_conflict :: \<open>nat literal list option\<close> where
  \<open>empty_conflict = Some []\<close>

definition (in -)empty_conflict_code :: \<open>(_ list option \<times> stats) nres\<close> where
  \<open>empty_conflict_code = do{
     let M0 = op_arl_empty;
     let M1 = Some M0;
     RETURN (M1, (zero_uint64, zero_uint64, zero_uint64, zero_uint64, zero_uint64))}\<close>

abbreviation (in -) model_stat_assn where
  \<open>model_stat_assn \<equiv> option_assn (arl_assn unat_lit_assn) *a stats_assn\<close>
(* heap_array_empty *)
sepref_definition (in -) empty_conflict_code'
  is \<open>uncurry0 (empty_conflict_code)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a model_stat_assn\<close>
  unfolding empty_conflict_code_def
  apply (rewrite in \<open>let _ =  \<hole> in _\<close> annotate_assn[where A=\<open>arl_assn unat_lit_assn\<close>])
  by sepref

declare empty_conflict_code'.refine[sepref_fr_rules]

definition empty_init_code :: \<open>_ list option \<times> stats\<close> where
  \<open>empty_init_code = (None, (zero_uint64, zero_uint64, zero_uint64, zero_uint64, zero_uint64))\<close>

sepref_definition (in -) empty_init_code'
  is \<open>uncurry0 (RETURN empty_init_code)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a model_stat_assn\<close>
  unfolding empty_init_code_def
  by sepref

declare empty_init_code'.refine[sepref_fr_rules]

lemma init_dt_wl_code_refine[sepref_fr_rules]:
  \<open>(uncurry2 (\<lambda>_. init_dt_wl_heur_full_code), uncurry2 (isasat_input_ops.init_dt_wl_heur_full))
  \<in> [\<lambda>((N, S), S'). isasat_input_bounded \<A>\<^sub>i\<^sub>n \<and> N = \<A>\<^sub>i\<^sub>n]\<^sub>a
    ghost_assn\<^sup>k *\<^sub>a (list_assn (list_assn unat_lit_assn))\<^sup>k *\<^sub>a (isasat_input_ops.isasat_init_assn \<A>\<^sub>i\<^sub>n)\<^sup>d \<rightarrow>
    isasat_input_ops.isasat_init_assn \<A>\<^sub>i\<^sub>n\<close>
  unfolding PR_CONST_def
  unfolding hfref_def hn_refine_def
  apply (subst in_pair_collect_simp)
  apply (intro allI impI)
  subgoal for a c
    using init_dt_wl_heur_full_code.refine[of \<A>\<^sub>i\<^sub>n,
      unfolded in_pair_collect_simp hfref_def hn_refine_def PR_CONST_def,
      rule_format, of \<open>(snd (fst c), snd c)\<close> \<open>(snd (fst a), snd a)\<close>]
    by (cases a)
       (sep_auto dest!: frame_rule_left[of \<open>_ * isasat_input_ops.isasat_init_assn _ _ _\<close> _ _
            \<open>ghost_assn \<A>\<^sub>i\<^sub>n (fst (fst a))\<close>])
  done
(*
lemma init_dt_wl_fast_code_refine[sepref_fr_rules]:
  \<open>(uncurry2 (\<lambda>_. init_dt_wl_fast_code), uncurry2 (isasat_input_ops.init_dt_wl_heur_fast))
  \<in> [\<lambda>((N, S), S'). isasat_input_bounded \<A>\<^sub>i\<^sub>n \<and> N = \<A>\<^sub>i\<^sub>n]\<^sub>a
    ghost_assn\<^sup>k *\<^sub>a (list_assn (list_assn unat_lit_assn))\<^sup>d *\<^sub>a
     (isasat_input_ops.isasat_init_fast_assn \<A>\<^sub>i\<^sub>n)\<^sup>d \<rightarrow>
    isasat_input_ops.isasat_init_fast_assn \<A>\<^sub>i\<^sub>n\<close>
  unfolding PR_CONST_def
  unfolding hfref_def hn_refine_def
  apply (subst in_pair_collect_simp)
  apply (intro allI impI)
  subgoal for a c
    using init_dt_wl_fast_code.refine[of \<A>\<^sub>i\<^sub>n,
      unfolded in_pair_collect_simp hfref_def hn_refine_def PR_CONST_def,
      rule_format, of \<open>(snd (fst c), snd c)\<close> \<open>(snd (fst a), snd a)\<close>]
    by (cases a)
       (sep_auto dest!: frame_rule_left[of \<open>_ * isasat_input_ops.isasat_init_fast_assn _ _ _\<close> _ _
            \<open>ghost_assn \<A>\<^sub>i\<^sub>n (fst (fst a))\<close>])
  done*)

definition (in -)convert_state where
  \<open>convert_state _ S = S\<close>

lemma (in -) convert_state_hnr:
  \<open>(uncurry (return oo (\<lambda>_ S. S)), uncurry (RETURN oo convert_state))
   \<in> [\<lambda>(N, S). N = \<A>\<^sub>i\<^sub>n \<and> N = \<A>\<^sub>i\<^sub>n']\<^sub>a
     ghost_assn\<^sup>k *\<^sub>a (isasat_input_ops.isasat_init_assn \<A>\<^sub>i\<^sub>n)\<^sup>d \<rightarrow>
     isasat_input_ops.isasat_init_assn \<A>\<^sub>i\<^sub>n'\<close>
  by sepref_to_hoare (sep_auto simp: convert_state_def)

(*
lemma (in -) convert_state_fast_hnr:
  \<open>(uncurry (return oo (\<lambda>_ S. S)), uncurry (RETURN oo convert_state))
   \<in> [\<lambda>(N, S). N = \<A>\<^sub>i\<^sub>n \<and> N = \<A>\<^sub>i\<^sub>n']\<^sub>a
     ghost_assn\<^sup>k *\<^sub>a (isasat_input_ops.isasat_init_fast_assn \<A>\<^sub>i\<^sub>n)\<^sup>d \<rightarrow>
     isasat_input_ops.isasat_init_fast_assn \<A>\<^sub>i\<^sub>n'\<close>
  by sepref_to_hoare (sep_auto simp: convert_state_def)*)

definition IsaSAT_use_fast_mode where
  \<open>IsaSAT_use_fast_mode = True\<close>

lemma IsaSAT_use_fast_mode[sepref_fr_rules]:
  \<open>(uncurry0 (return IsaSAT_use_fast_mode), uncurry0 (RETURN IsaSAT_use_fast_mode))
   \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare sep_auto
    (* if IsaSAT_use_fast_mode \<and> length CS < uint_max - 1
    then do {
        S \<leftarrow> isasat_input_ops.init_state_wl_heur_fast \<A>\<^sub>i\<^sub>n';
        (T::twl_st_wl_heur_init) \<leftarrow> isasat_input_ops.init_dt_wl_heur_fast \<A>\<^sub>i\<^sub>n'' CS S;
        let T = convert_state \<A>\<^sub>i\<^sub>n'' T;
        if \<not>get_conflict_wl_is_None_heur_init T
        then RETURN empty_init_code
        else if CS = [] then empty_conflict_code
        else do {
           ASSERT(\<A>\<^sub>i\<^sub>n'' \<noteq> {#});
           ASSERT(isasat_input_bounded_nempty \<A>\<^sub>i\<^sub>n'');
           ASSERT(mset `# ran_mf (get_clauses_wl_heur_init T) \<subseteq># mset `# mset CS);
           ASSERT((\<lambda>(M', N', D', Q', W', ((ns, m, fst_As, lst_As, next_search), to_remove), \<phi>, clvls). fst_As \<noteq> None \<and>
             lst_As \<noteq> None) T);
           ASSERT(size (learned_clss_l (get_clauses_wl_heur_init T)) = 0);
           T \<leftarrow> finalise_init_code (T::twl_st_wl_heur_init);
           ASSERT(isasat_fast T);
           U \<leftarrow> isasat_input_ops.cdcl_twl_stgy_prog_break_wl_D_heur_break \<A>\<^sub>i\<^sub>n'' T;
           RETURN (if get_conflict_wl_is_None_heur U then extract_model_of_state_stat U
             else extract_state_stat U)
         }
      }
    else *)
definition IsaSAT_heur :: \<open>opts \<Rightarrow> nat clause_l list \<Rightarrow> (nat literal list option \<times> stats) nres\<close> where
  \<open>IsaSAT_heur opts CS = do{
    ASSERT(\<forall>C\<in>set CS. \<forall>L\<in>set C. nat_of_lit L \<le> uint_max);
    let \<A>\<^sub>i\<^sub>n' = mset_set (extract_atms_clss CS {});
    ASSERT(isasat_input_bounded \<A>\<^sub>i\<^sub>n');
    ASSERT(distinct_mset \<A>\<^sub>i\<^sub>n');
    let \<A>\<^sub>i\<^sub>n'' = virtual_copy \<A>\<^sub>i\<^sub>n';
     do {
        S \<leftarrow> isasat_input_ops.init_state_wl_heur \<A>\<^sub>i\<^sub>n';
        (T::twl_st_wl_heur_init) \<leftarrow> isasat_input_ops.init_dt_wl_heur_full \<A>\<^sub>i\<^sub>n'' CS S;
        let T = convert_state \<A>\<^sub>i\<^sub>n'' T;
        if \<not>get_conflict_wl_is_None_heur_init T
        then RETURN (empty_init_code)
        else if CS = [] then empty_conflict_code
        else do {
           ASSERT(\<A>\<^sub>i\<^sub>n'' \<noteq> {#});
           ASSERT(isasat_input_bounded_nempty \<A>\<^sub>i\<^sub>n'');
           _ \<leftarrow> isasat_information_banner T;
           ASSERT((\<lambda>(M', N', D', Q', W', ((ns, m, fst_As, lst_As, next_search), to_remove), \<phi>, clvls). fst_As \<noteq> None \<and>
             lst_As \<noteq> None) T);
           T \<leftarrow> finalise_init_code opts (T::twl_st_wl_heur_init);
           U \<leftarrow> isasat_input_ops.cdcl_twl_stgy_restart_prog_wl_heur \<A>\<^sub>i\<^sub>n'' T;
           RETURN (if get_conflict_wl_is_None_heur U then extract_model_of_state_stat U
             else extract_state_stat U)
         }
      }
    }\<close>

lemma in_class_in_literals_are_in_\<L>\<^sub>i\<^sub>n:
  assumes \<open>C \<in> set CS\<close>
  shows \<open>isasat_input_ops.literals_are_in_\<L>\<^sub>i\<^sub>n (mset_set (extract_atms_clss CS {})) (mset C)\<close>
  apply (auto simp: isasat_input_ops.literals_are_in_\<L>\<^sub>i\<^sub>n_def extract_atms_clss_alt_def
       isasat_input_ops.\<L>\<^sub>a\<^sub>l\<^sub>l_def all_lits_of_m_def)
  apply (subst insert_absorb[OF assms, symmetric])
  apply auto
  apply (subst (asm)insert_absorb[OF assms, symmetric])
  apply (subst insert_absorb[OF assms, symmetric])
  apply auto
  done

lemma (in -)id_mset_list_assn_list_mset_assn:
  assumes \<open>CONSTRAINT is_pure R\<close>
  shows \<open>(return o id, RETURN o mset) \<in> (list_assn R)\<^sup>d \<rightarrow>\<^sub>a list_mset_assn R\<close>
proof -
  obtain R' where R: \<open>R = pure R'\<close>
    using assms is_pure_conv unfolding CONSTRAINT_def by blast
  then have R': \<open>the_pure R = R'\<close>
    unfolding R by auto
  show ?thesis
    apply (subst R)
    apply (subst list_assn_pure_conv)
    apply sepref_to_hoare
    by (sep_auto simp: list_mset_assn_def R' pure_def list_mset_rel_def mset_rel_def
       p2rel_def rel2p_def[abs_def] rel_mset_def br_def Collect_eq_comp list_rel_def)
qed

lemma cdcl_twl_stgy_prog_wl_D_code_ref':
  \<open>(uncurry (\<lambda>_. cdcl_twl_stgy_prog_wl_D_code), uncurry isasat_input_ops.cdcl_twl_stgy_prog_wl_D_heur)
  \<in> [\<lambda>(N, _). N = \<A>\<^sub>i\<^sub>n \<and> isasat_input_bounded_nempty \<A>\<^sub>i\<^sub>n]\<^sub>a
     (ghost_assn)\<^sup>k *\<^sub>a
    (isasat_input_ops.isasat_unbounded_assn \<A>\<^sub>i\<^sub>n)\<^sup>d \<rightarrow> isasat_input_ops.isasat_unbounded_assn \<A>\<^sub>i\<^sub>n\<close>
  unfolding hfref_def hn_refine_def
  apply (subst in_pair_collect_simp)
  apply (intro allI impI)
  subgoal for a c
    using cdcl_twl_stgy_prog_wl_D_code.refine[of \<A>\<^sub>i\<^sub>n,
      unfolded in_pair_collect_simp hfref_def hn_refine_def PR_CONST_def,
      rule_format, of \<open>snd c\<close> \<open>snd a\<close>]
    apply (cases a)
    by (sep_auto simp:
      dest!: frame_rule_left[of \<open>isasat_input_ops.isasat_unbounded_assn _ _ _\<close> _ _
        \<open>ghost_assn \<A>\<^sub>i\<^sub>n (fst a)\<close>])
  done

(*
lemma cdcl_twl_stgy_prog_wl_D_break_fast_code_ref':
  \<open>(uncurry (\<lambda>_. cdcl_twl_stgy_prog_wl_D_fast_code),
      uncurry isasat_input_ops.cdcl_twl_stgy_prog_break_wl_D_heur_break)
  \<in> [\<lambda>(N, S). N = \<A>\<^sub>i\<^sub>n \<and> isasat_input_bounded_nempty \<A>\<^sub>i\<^sub>n \<and> isasat_fast S]\<^sub>a
     (ghost_assn)\<^sup>k *\<^sub>a
    (isasat_input_ops.isasat_bounded_assn \<A>\<^sub>i\<^sub>n)\<^sup>d \<rightarrow> isasat_input_ops.isasat_unbounded_assn \<A>\<^sub>i\<^sub>n\<close>
  unfolding hfref_def hn_refine_def
  apply (subst in_pair_collect_simp)
  apply (intro allI impI)
  subgoal for a c
    using cdcl_twl_stgy_prog_wl_D_fast_code.refine[of \<A>\<^sub>i\<^sub>n,
      unfolded in_pair_collect_simp hfref_def hn_refine_def PR_CONST_def,
      rule_format, of \<open>snd c\<close> \<open>snd a\<close>]
    by (cases a)
      (sep_auto simp:
      dest!: frame_rule_left[of \<open>isasat_input_ops.isasat_bounded_assn _ _ _\<close> _ _
       \<open>ghost_assn \<A>\<^sub>i\<^sub>n (fst a)\<close>])
  done*)


lemma cdcl_twl_stgy_restart_prog_wl_D_code_ref':
  \<open>(uncurry (\<lambda>_. cdcl_twl_stgy_restart_prog_wl_heur_code), uncurry isasat_input_ops.cdcl_twl_stgy_restart_prog_wl_heur)
  \<in> [\<lambda>(N, _). N = \<A>\<^sub>i\<^sub>n \<and> isasat_input_bounded_nempty \<A>\<^sub>i\<^sub>n]\<^sub>a
     (ghost_assn)\<^sup>k *\<^sub>a
    (isasat_input_ops.isasat_unbounded_assn \<A>\<^sub>i\<^sub>n)\<^sup>d \<rightarrow> isasat_input_ops.isasat_unbounded_assn \<A>\<^sub>i\<^sub>n\<close>
  unfolding hfref_def hn_refine_def
  apply (subst in_pair_collect_simp)
  apply (intro allI impI)
  subgoal for a c
    using cdcl_twl_stgy_restart_prog_wl_heur_code.refine[of \<A>\<^sub>i\<^sub>n,
      unfolded in_pair_collect_simp hfref_def hn_refine_def PR_CONST_def,
      rule_format, of \<open>snd c\<close> \<open>snd a\<close>]
    apply (cases a)
    by (sep_auto simp:
      dest!: frame_rule_left[of \<open>isasat_input_ops.isasat_unbounded_assn _ _ _\<close> _ _
        \<open>ghost_assn \<A>\<^sub>i\<^sub>n (fst a)\<close>])
  done

declare cdcl_twl_stgy_prog_wl_D_code_ref'[to_hnr, OF refl, sepref_fr_rules]
(*declare cdcl_twl_stgy_prog_wl_D_break_fast_code_ref'[to_hnr, OF refl, sepref_fr_rules]*)
declare cdcl_twl_stgy_restart_prog_wl_D_code_ref'[to_hnr, OF refl, sepref_fr_rules]

definition get_trail_wl_code :: \<open>twl_st_wll_trail \<Rightarrow> uint32 array_list option \<times> stats\<close> where
  \<open>get_trail_wl_code = (\<lambda>((M, _), _, _, _, _ ,_ ,_ ,_, _, _, _, stat, _). (Some M, stat))\<close>

definition get_stats_code :: \<open>twl_st_wll_trail \<Rightarrow> uint32 array_list option \<times> stats\<close> where
  \<open>get_stats_code = (\<lambda>((M, _), _, _, _, _ ,_ ,_ ,_, _, _, _, stat, _). (None, stat))\<close>


definition (in -) model_stat_rel where
  \<open>model_stat_rel = {((M', s), M). map_option rev M = M'}\<close>

definition (in -) model_assn where
  \<open>model_assn = hr_comp model_stat_assn model_stat_rel\<close>


context isasat_input_ops
begin

lemma extract_model_of_state_stat_hnr[sepref_fr_rules]:
  \<open>(return o get_trail_wl_code, RETURN o extract_model_of_state_stat) \<in> isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a
       model_stat_assn\<close>
proof -
  have [simp]: \<open>(\<lambda>a c. \<up> ((c, a) \<in> unat_lit_rel)) = unat_lit_assn\<close>
    by (auto simp: unat_lit_rel_def pure_def)
  have [simp]: \<open>id_assn (an, ao, bb) (bs, bt, bu) = (id_assn an bs * id_assn ao bt * id_assn bb bu)\<close>
    for an ao bb bs bt bu :: uint64
    by (auto simp: pure_def)
  show ?thesis
    by sepref_to_hoare
      (sep_auto simp: twl_st_heur_def hr_comp_def trail_pol_def isasat_unbounded_assn_def
        isasat_init_assn_def get_trail_wl_code_def
        extract_model_of_state_def extract_model_of_state_stat_def
        dest!: ann_lits_split_reasons_map_lit_of
        elim!: mod_starE)
qed

lemma get_stats_code[sepref_fr_rules]:
  \<open>(return o get_stats_code, RETURN o extract_state_stat) \<in> isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a
       model_stat_assn\<close>
proof -
  have [simp]: \<open>(\<lambda>a c. \<up> ((c, a) \<in> unat_lit_rel)) = unat_lit_assn\<close>
    by (auto simp: unat_lit_rel_def pure_def)
  have [simp]: \<open>id_assn (an, ao, bb) (bs, bt, bu) = (id_assn an bs * id_assn ao bt * id_assn bb bu)\<close>
    for an ao bb bs bt bu :: uint64
    by (auto simp: pure_def)
  show ?thesis
    by sepref_to_hoare
      (sep_auto simp: twl_st_heur_def hr_comp_def trail_pol_def isasat_unbounded_assn_def
        isasat_init_assn_def get_trail_wl_code_def get_stats_code_def
        extract_model_of_state_def extract_model_of_state_stat_def extract_state_stat_def
        dest!: ann_lits_split_reasons_map_lit_of
        elim!: mod_starE)
qed


end

declare isasat_input_ops.extract_model_of_state_stat_hnr[sepref_fr_rules]
declare isasat_input_ops.finalise_init_hnr[unfolded PR_CONST_def, sepref_fr_rules]
(*declare isasat_input_ops.finalise_init_fast_hnr[unfolded PR_CONST_def, sepref_fr_rules]*)
sepref_register to_init_state from_init_state get_conflict_wl_is_None_init extract_stats
  isasat_input_ops.init_dt_wl_heur

declare init_state_wl_heur_hnr[to_hnr, OF refl, sepref_fr_rules]
  init_dt_wl_heur_full_code.refine[sepref_fr_rules]
  isasat_input_ops.get_stats_code[sepref_fr_rules]
(*  init_state_wl_heur_fast_hnr[to_hnr, OF refl, sepref_fr_rules]*)

lemma uint_max_nat_assn_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return uint_max), uncurry0 (RETURN uint_max)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  by sepref_to_hoare sep_auto


text \<open>Crucial and subtil point for the refinement\<close>
declare convert_state_hnr[to_hnr, OF _ refl, sepref_fr_rules]
  (* convert_state_fast_hnr[to_hnr, OF _ refl, sepref_fr_rules]*)
sepref_register (*isasat_input_ops.init_dt_wl_heur_fast*)
   isasat_input_ops.cdcl_twl_stgy_restart_prog_wl_heur

sepref_definition IsaSAT_code
  is \<open>uncurry IsaSAT_heur\<close>
  :: \<open>opts_assn\<^sup>d *\<^sub>a (list_assn (list_assn unat_lit_assn))\<^sup>k \<rightarrow>\<^sub>a model_stat_assn\<close>
  supply [[goals_limit=1]]
  unfolding IsaSAT_heur_def empty_conflict_def[symmetric]
    get_conflict_wl_is_None extract_model_of_state_def[symmetric]
    extract_stats_def[symmetric]
  supply get_conflict_wl_is_None_heur_init_def[simp]
  isasat_input_bounded.get_conflict_wl_is_None_code_refine[sepref_fr_rules]
  isasat_input_bounded.get_conflict_wl_is_None_init_code_hnr[sepref_fr_rules]
  isasat_input_bounded_nempty.cdcl_twl_stgy_restart_prog_wl_heur_hnr[sepref_fr_rules]
  supply id_mset_list_assn_list_mset_assn[sepref_fr_rules] get_conflict_wl_is_None_def[simp]
   option.splits[split]
   extract_stats_def[simp del]
  apply (rewrite at \<open>extract_atms_clss _ \<hole>\<close> op_extract_list_empty_def[symmetric])
  by sepref

definition nth_u_code' where
  [symmetric, code]: \<open>nth_u_code' = nth_u_code\<close>

code_printing constant nth_u_code' \<rightharpoonup> (SML) "(fn/ ()/ =>/ Array.sub/ ((_),/ Word32.toInt (_)))"

definition nth_u64_code' where
  [symmetric, code]: \<open>nth_u64_code' = nth_u64_code\<close>

code_printing constant nth_u64_code' \<rightharpoonup> (SML) "(fn/ ()/ =>/ Array.sub/ ((_),/ Uint64.toFixedInt (_)))"

definition heap_array_set'_u' where
  [symmetric, code]: \<open>heap_array_set'_u' = heap_array_set'_u\<close>

code_printing constant heap_array_set'_u' \<rightharpoonup>
   (SML) "(fn/ ()/ =>/ Array.update/ ((_),/ (Word32.toInt (_)),/ (_)))"

definition heap_array_set'_u64' where
  [symmetric, code]: \<open>heap_array_set'_u64' = heap_array_set'_u64\<close>

code_printing constant heap_array_set'_u64' \<rightharpoonup>
   (SML) "(fn/ ()/ =>/ Array.update/ ((_),/ (Word64.toInt (_)),/ (_)))"

code_printing constant two_uint32 \<rightharpoonup> (SML) "(Word32.fromInt 2)"

definition length_u_code' where
  [symmetric, code]: \<open>length_u_code' = length_u_code\<close>

code_printing constant length_u_code' \<rightharpoonup> (SML_imp) "(fn/ ()/ =>/ Word32.fromInt (Array.length (_)))"

definition length_aa_u_code' where
  [symmetric, code]: \<open>length_aa_u_code' = length_aa_u_code\<close>

code_printing constant length_aa_u_code' \<rightharpoonup> (SML_imp)
   "(fn/ ()/ =>/ Word32.fromInt (Array.length (Array.sub/ ((fn/ (a,b)/ =>/ a) (_),/ IntInf.toInt (integer'_of'_nat (_))))))"

definition nth_raa_i_u64' where
  [symmetric, code]: \<open>nth_raa_i_u64' = nth_raa_i_u64\<close>

code_printing constant nth_raa_i_u64' \<rightharpoonup> (SML_imp)
   "(fn/ ()/ =>/ Array.sub (Array.sub/ ((fn/ (a,b)/ =>/ a) (_),/ IntInf.toInt (integer'_of'_nat (_))), Uint64.toFixedInt (_)))"

definition length_u64_code' where
  [symmetric, code]: \<open>length_u64_code' = length_u64_code\<close>

code_printing constant length_u64_code' \<rightharpoonup> (SML_imp)
   "(fn/ ()/ =>/ Uint64.fromFixedInt (Array.length (_)))"

code_printing constant arl_get_u \<rightharpoonup> (SML) "(fn/ ()/ =>/ Array.sub/ ((fn/ (a,b)/ =>/ a) ((_)),/ Word32.toInt ((_))))"
(*
definition arl_set_u64' where
  [symmetric, code]: \<open>arl_set_u64' = arl_set_u64\<close>
 *)
lemma arl_set_u64_code[code]: \<open>arl_set_u64 a i x =
   Array_upd_u64 i x (fst a) \<bind> (\<lambda>b. return (b, (snd a)))\<close>
  unfolding arl_set_u64_def arl_set_def heap_array_set'_u64_def arl_set'_u64_def
     heap_array_set_u64_def Array.upd'_def Array_upd_u64_def
  by (cases a) (auto simp: nat_of_uint64_code[symmetric])

lemma arl_set_u_code[code]: \<open>arl_set_u a i x =
   Array_upd_u i x (fst a) \<bind> (\<lambda>b. return (b, (snd a)))\<close>
  unfolding arl_set_u_def arl_set_def heap_array_set'_u64_def arl_set'_u_def
     heap_array_set_u_def Array.upd'_def Array_upd_u_def
  by (cases a) (auto simp: nat_of_uint64_code[symmetric])

(* This equation makes no sense since a resizable array is represent by an array and an infinite
 integer: There is no obvious shortcut.
code_printing constant length_arl_u_code' \<rightharpoonup> (SML_imp)
   "(fn/ ()/ =>/ Word32.fromLargeInt (snd (_)))"  *)
(* code_printing constant nth_u64_code \<rightharpoonup> (SML) "(fn/ ()/ =>/ Array.sub/ ((_),/ Uint64.toFixedInt (_)))" *)


definition arl_get_u64' where
  [symmetric, code]: \<open>arl_get_u64' = arl_get_u64\<close>

code_printing constant arl_get_u64' \<rightharpoonup> (SML) "(fn/ ()/ =>/ Array.sub/ ((fn (a,b) => a) (_),/ Uint64.toFixedInt (_)))"

export_code IsaSAT_code checking SML_imp

code_printing constant \<comment> \<open>print with line break\<close>
  println_string \<rightharpoonup> (SML) "ignore/ (print/ ((_) ^ \"\\n\"))"

export_code IsaSAT_code
    int_of_integer
    integer_of_int
    integer_of_nat
    nat_of_integer
    uint32_of_nat
  in SML_imp module_name SAT_Solver file "code/IsaSAT_solver.sml"

definition TWL_to_clauses_state_conv :: \<open>(nat twl_st_wl \<times> nat cdcl\<^sub>W_restart_mset) set\<close> where
  \<open>TWL_to_clauses_state_conv = twl_st_of_wl None O {(S', S). S = state\<^sub>W_of S'}\<close>

lemma extract_atms_cls_empty_iff: \<open>extract_atms_cls Cs C0 = {} \<longleftrightarrow> (C0 = {} \<and> Cs = [])\<close>
  unfolding extract_atms_cls_def
  by (induction Cs arbitrary: C0) force+

lemma extract_atms_clss_empty_iff:
   \<open>extract_atms_clss CS C0  = {} \<longleftrightarrow> (C0 = {} \<and> (\<forall>C \<in> set CS. C = []))\<close>
  unfolding extract_atms_clss_alt_def
  by auto

lemma is_\<L>\<^sub>a\<^sub>l\<^sub>l_extract_atms_clss:
    \<open>isasat_input_ops.is_\<L>\<^sub>a\<^sub>l\<^sub>l (mset_set (extract_atms_clss CS' {}))
       (all_lits_of_mm (mset `# mset CS'))\<close>
proof -
  have [simp]: \<open>is_neg xb \<Longrightarrow> Pos (atm_of xb) = - xb\<close> for xb
    by (cases xb) auto
  have [simp]: \<open>is_pos xb \<Longrightarrow> Neg (atm_of xb) = - xb\<close> for xb
    by (cases xb) auto
  have [intro]: \<open>\<And>x. x \<in># all_lits_of_mm
               (mset `# mset CS') \<Longrightarrow>
         x \<notin> Neg `
              (\<Union>C\<in>set CS'. atm_of ` set C) \<Longrightarrow>
         x \<in> Pos ` (\<Union>C\<in>set CS'. atm_of ` set C)\<close>
    apply (induction CS')
    subgoal by auto
    subgoal for C CS x
      by (cases x)
        (auto simp: all_lits_of_mm_add_mset image_Un in_all_lits_of_m_ain_atms_of_iff
        atm_of_eq_atm_of uminus_lit_swap)
    done
  show ?thesis
    by (auto simp: extract_atms_clss_alt_def
        isasat_input_ops.is_\<L>\<^sub>a\<^sub>l\<^sub>l_def isasat_input_ops.\<L>\<^sub>a\<^sub>l\<^sub>l_def all_lits_of_mm_add_mset
        all_lits_of_m_add_mset
        dest!: split_list)
qed

(* TODO Move *)

lemma finite_extract_atms_clss[simp]: \<open>finite (extract_atms_clss CS' {})\<close> for CS'
  by (auto simp: extract_atms_clss_alt_def)

lemma in_\<L>\<^sub>a\<^sub>l\<^sub>l_extract_atms_clss_in_all_lits_of_mm:
  shows \<open>L \<in># isasat_input_ops.\<L>\<^sub>a\<^sub>l\<^sub>l (mset_set (extract_atms_clss CS' {})) \<longleftrightarrow>
    L\<in>#all_lits_of_mm (mset `# mset CS')\<close>
    (is \<open>?A \<longleftrightarrow> ?B\<close>)
proof -
  have 1: \<open>?A \<longleftrightarrow> L\<in>#all_lits_of_m (mset_set (Pos ` extract_atms_clss CS' {}))\<close>
    unfolding isasat_input_ops.\<L>\<^sub>a\<^sub>l\<^sub>l_def
    by (cases L)
       (auto simp: in_all_lits_of_m_ain_atms_of_iff atms_of_def image_image)
  also have \<open>\<dots> \<longleftrightarrow> ?B\<close>
    using 1 is_\<L>\<^sub>a\<^sub>l\<^sub>l_extract_atms_clss isasat_input_ops.is_\<L>\<^sub>a\<^sub>l\<^sub>l_def by auto
  finally show ?thesis .
qed

lemma cdcl\<^sub>W_ex_cdcl\<^sub>W_stgy:
  \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W S T \<Longrightarrow> \<exists>U. cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy S U\<close>
  by (meson cdcl\<^sub>W_restart_mset.cdcl\<^sub>W.cases cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy.simps)

lemma rtranclp_cdcl\<^sub>W_cdcl\<^sub>W_init_state:
  \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W\<^sup>*\<^sup>* (init_state {#}) S \<longleftrightarrow> S = init_state {#}\<close>
  unfolding rtranclp_unfold
  by (subst tranclp_unfold_begin)
    (auto simp: cdcl\<^sub>W_stgy_cdcl\<^sub>W_init_state_empty_no_step
       cdcl\<^sub>W_stgy_cdcl\<^sub>W_init_state
      simp del: init_state.simps
       dest: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_cdcl\<^sub>W cdcl\<^sub>W_ex_cdcl\<^sub>W_stgy)

lemma cdcl\<^sub>W_cdcl\<^sub>W_init_state:
  \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W (init_state {#}) S \<longleftrightarrow> False\<close>
  using cdcl\<^sub>W_ex_cdcl\<^sub>W_stgy cdcl\<^sub>W_stgy_cdcl\<^sub>W_init_state_empty_no_step by blast

lemma rtranclp_cdcl\<^sub>W_init_state:
  \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (M, CS, {#}, Some {#}) S \<longleftrightarrow> S = (M, CS, {#}, Some {#})\<close>
  unfolding full_def rtranclp_unfold
  by (subst tranclp_unfold_begin)
     (auto simp:  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy.simps
      cdcl\<^sub>W_restart_mset.conflict.simps cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o.simps
       cdcl\<^sub>W_restart_mset.propagate.simps cdcl\<^sub>W_restart_mset.decide.simps
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_bj.simps cdcl\<^sub>W_restart_mset.backtrack.simps
      cdcl\<^sub>W_restart_mset.skip.simps cdcl\<^sub>W_restart_mset.resolve.simps
      cdcl\<^sub>W_restart_mset_state clauses_def)

lemma (in -) added_only_watched[simp]:
  assumes \<open>(T, T') \<in> added_only_watched \<close>
  shows
     \<open>get_conflict_init_wl T' = get_conflict_wl (fst T)\<close>
     \<open>get_trail_init_wl T' = get_trail_wl (fst T)\<close>
  using assms by (auto simp: added_only_watched_def)

lemma cdcl_twl_stgy_prog_wl_spec_final2:
  shows
    \<open>(SAT_wl, SAT) \<in> [\<lambda>CS. (\<forall>C \<in># CS. distinct_mset C) \<and>
        (\<forall>C \<in># CS. \<forall>L \<in># C. nat_of_lit L \<le> uint_max)]\<^sub>f
     (list_mset_rel O \<langle>list_mset_rel\<rangle> mset_rel) \<rightarrow> \<langle>TWL_to_clauses_state_conv\<rangle>nres_rel\<close>
proof -
  have in_list_mset_rel: \<open>(CS', y) \<in> list_mset_rel \<longleftrightarrow> y = mset CS'\<close> for CS' y
    by (auto simp: list_mset_rel_def br_def)
  have in_list_mset_rel_mset_rel:
    \<open>(mset CS', CS) \<in> \<langle>list_mset_rel\<rangle>mset_rel \<longleftrightarrow> CS = mset `# mset CS'\<close> for CS CS'
    by (auto simp: list_mset_rel_def br_def mset_rel_def p2rel_def rel_mset_def
        rel2p_def[abs_def] list_all2_op_eq_map_right_iff')

  have \<L>\<^sub>a\<^sub>l\<^sub>l:
    \<open>isasat_input_ops.is_\<L>\<^sub>a\<^sub>l\<^sub>l (mset_set (extract_atms_clss CS' {}))
       (all_lits_of_mm (mset `# mset CS'))\<close>
    for CS'
    by (auto simp add: is_\<L>\<^sub>a\<^sub>l\<^sub>l_extract_atms_clss)
  have extract_nempty: \<open>extract_atms_clss xs {} = {} \<longleftrightarrow> set xs = {[]}\<close>
  if
    H: \<open>Multiset.Ball ys distinct_mset \<and> (\<forall>C\<in>#ys. \<forall>L\<in>#C. nat_of_lit L \<le> uint_max)\<close> and
    rel: \<open>(xs, ys) \<in> list_mset_rel O \<langle>list_mset_rel\<rangle>mset_rel\<close> and
    le_xs: \<open>length xs \<noteq> 0\<close>
    for xs ys
    using le_xs unfolding extract_atms_clss_alt_def by (cases xs) auto

  have [simp]: \<open>isasat_input_bounded (mset_set (extract_atms_clss CS' {}))\<close>
    if CS_p: \<open>\<forall>C\<in>set CS'. \<forall>L\<in>set C. nat_of_lit L \<le> uint_max\<close>
    for CS'
    unfolding isasat_input_bounded_def
  proof
    fix L
    assume L: \<open>L \<in># isasat_input_ops.\<L>\<^sub>a\<^sub>l\<^sub>l (mset_set (extract_atms_clss CS' {}))\<close>
    then obtain C where
      L: \<open>C\<in>set CS' \<and> (L \<in>set C \<or> - L \<in> set C)\<close>
      apply (cases L)
      apply (auto simp: extract_atms_clss_alt_def uint_max_def nat_of_uint32_uint32_of_nat_id
          isasat_input_ops.\<L>\<^sub>a\<^sub>l\<^sub>l_def)+
      apply (metis literal.exhaust_sel)+
      done
    have \<open>nat_of_lit L \<le> uint_max \<or> nat_of_lit (-L) \<le> uint_max\<close>
      using L CS_p by auto
    then show \<open>nat_of_lit L \<le> uint_max\<close>
      using L
      by (cases L) (auto simp: extract_atms_clss_alt_def uint_max_def)
  qed


  have conflict_during_init: \<open>RETURN (fst T)
      \<le> \<Down> TWL_to_clauses_state_conv
           (SPEC (conclusive_CDCL_run CS (init_state CS)))\<close>
    if
      \<open>Multiset.Ball CS distinct_mset \<and> (\<forall>C\<in>#CS. \<forall>L\<in>#C. nat_of_lit L \<le> uint_max)\<close> and
      CS'_CS: \<open>(CS', CS) \<in> list_mset_rel O \<langle>list_mset_rel\<rangle>mset_rel\<close> and
      spec: \<open>init_dt_wl_spec_full CS' (([], fmempty, None, {#}, {#}, {#}), {#}) T\<close> and
      confl: \<open>get_conflict_wl (fst T) \<noteq> None\<close>
    for T CS CS'
  proof -
    obtain U V T' W where
      U: \<open>((([], fmempty, None, {#}, {#}, {#}), {#}), U) \<in> state_wl_l_init\<close> and
      T_V: \<open>(T', V) \<in> state_wl_l_init\<close> and
      \<open>correct_watching_init (fst T)\<close> and
      T_T': \<open>(T, T') \<in> added_only_watched\<close> and
      V_W: \<open>(V, W) \<in> twl_st_l_init\<close> and
      struct_invs: \<open>twl_struct_invs_init W\<close> and
      \<open>clauses_to_update_l_init V = {#}\<close> and
      count_dec: \<open>\<forall>s\<in>set (get_trail_l_init V). \<not> is_decided s\<close> and
      \<open>get_conflict_l_init V = None \<longrightarrow>
         literals_to_update_l_init V =
         uminus `# lit_of `# mset (get_trail_l_init V)\<close> and
      clss: \<open>mset `# mset CS' + mset `# ran_mf (get_clauses_l_init U) +
        other_clauses_l_init U +  get_unit_clauses_l_init U =
        mset `# ran_mf (get_clauses_l_init V) + other_clauses_l_init V +
          get_unit_clauses_l_init V\<close> and
      learned_UV: \<open>learned_clss_lf (get_clauses_l_init U) =
        learned_clss_lf (get_clauses_l_init V)\<close> and
      learned: \<open>get_learned_unit_clauses_l_init V = get_learned_unit_clauses_l_init U\<close> and
      \<open>twl_list_invs (fst V)\<close> and
      \<open>twl_stgy_invs (fst W)\<close> and
      \<open>other_clauses_l_init V \<noteq> {#} \<longrightarrow> get_conflict_l_init V \<noteq> None\<close> and
      \<open>{#} \<in># mset `# mset CS' \<longrightarrow> get_conflict_l_init V \<noteq> None\<close> and
      \<open>get_conflict_l_init U \<noteq> None \<longrightarrow>
      get_conflict_l_init U = get_conflict_l_init V\<close>
      using spec unfolding init_dt_wl_spec_def init_dt_spec_def
        init_dt_wl_spec_full_def apply -
      apply normalize_goal+
      apply (rename_tac U T' V W)
      by presburger

    have learned_U: \<open>learned_clss_lf (get_clauses_l_init U) = {#}\<close>
          \<open>get_clauses_l_init U = fmempty\<close>
          \<open>other_clauses_l_init U  = {#}\<close>
          \<open>get_unit_clauses_l_init U = {#}\<close>
      using U T_V V_W T_T'
      by (cases U; auto simp: state_wl_l_init_def state_wl_l_def
         added_only_watched_def state_wl_l_init'_def; fail)+
    then have learned_W: \<open>get_learned_clauses_init W = {#}\<close> \<open>get_unit_learned_clauses_init W = {#}\<close>
      \<open>get_unit_init_clauses_init W = get_unit_clauses_l_init V\<close>
      using U T_V V_W learned learned_UV by (cases T; cases U; cases V;
         auto simp: state_wl_l_init_def state_wl_l_def twl_st_l_init_def; fail)+
    have ran_m_init_U:
      \<open>ran_m (get_clauses_l_init V) = init_clss_l (get_clauses_l_init V)\<close>
      using U T_V V_W learned learned_UV learned_U
      apply (subst all_clss_l_ran_m[symmetric])
      by (cases T; cases U; cases V;
         auto simp: state_wl_l_init_def state_wl_l_def twl_st_l_init_def
         simp del: all_clss_l_ran_m)
    have [simp]: \<open>get_trail_init_wl T' = get_trail_wl (fst T)\<close>
      \<open>other_clauses_init_wl T' = snd T\<close>
      \<open>get_conflict_init_wl T' = get_conflict_wl (fst T)\<close>
      using T_T' by (auto simp: added_only_watched_def)
    have
      \<open>clause `# (get_init_clauses_init W) =
       mset `# (init_clss_lf (get_clauses_l_init V))\<close>
      using U T_V V_W learned learned_UV by (cases T; cases U; cases V;
         auto simp: state_wl_l_init_def state_wl_l_def twl_st_l_init_def
         mset_take_mset_drop_mset' mset_take_mset_drop_mset
         dest!: multi_member_split)
    from arg_cong[OF this, of set_mset]
    have init_clss_W_V: \<open>clause ` set_mset (get_init_clauses_init W)
        = mset ` set_mset (init_clss_lf (get_clauses_l_init V))\<close>
      by auto
    have count_dec: \<open>count_decided (get_trail_wl (fst T)) = 0\<close>
      using count_dec T_V V_W unfolding count_decided_0_iff by (auto simp: twl_st_init
          twl_st_wl_init)
    have CS: \<open>CS = mset `# mset CS'\<close>
      using CS'_CS by (auto simp: in_list_mset_rel in_list_mset_rel_mset_rel)

    have le: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause (state\<^sub>W_of_init W)\<close> and
      all_struct_invs:
        \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of_init W)\<close>
      using struct_invs unfolding twl_struct_invs_init_def
         cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      by fast+
    have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (state\<^sub>W_of_init W)\<close>
      using struct_invs unfolding twl_struct_invs_init_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      by fast
    have \<open>unsatisfiable (set_mset (mset `# mset (rev CS')))\<close>
      using conflict_of_level_unsatisfiable[OF all_struct_invs] count_dec confl learned clss T_V V_W
        learned_U init_clss_W_V learned_W le ran_m_init_U
      by (auto simp: clauses_def mset_take_mset_drop_mset' twl_st_init twl_st_wl_init image_image
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def ac_simps twl_st_l_init)
    then have unsat[simp]: \<open>unsatisfiable (mset ` set CS')\<close>
      by auto
    then have [simp]: \<open>CS' \<noteq> []\<close>
      by (auto simp del: unsat)
    have T_V': \<open>(fst T, fst V) \<in> state_wl_l None\<close>
      using T_V T_T' by (cases V) (auto simp:state_wl_l_init_def added_only_watched_def
        state_wl_l_def state_wl_l_init'_def)
    show ?thesis
      unfolding conclusive_CDCL_run_def
      apply (rule RETURN_SPEC_refine)
      apply (rule exI[of _ \<open>state\<^sub>W_of (fst W)\<close>])
      apply (intro conjI)
      subgoal
        using T_V' V_W unfolding state_wl_l_init_def twl_st_l_init_alt_def
        by (auto simp: TWL_to_clauses_state_conv_def mset_take_mset_drop_mset'
            clauses_def in_list_mset_rel in_list_mset_rel_mset_rel)
      subgoal
        apply (rule disjI2)
        using \<L>\<^sub>a\<^sub>l\<^sub>l struct_invs learned count_dec U clss confl T_V V_W
        by (clarsimp simp: CS twl_st_init twl_st_wl_init twl_st_l_init)
      done
  qed

  have empty_clss:
   \<open>RETURN ([], fmempty, None, {#}, {#}, {#}, \<lambda>_. undefined)
      \<le> \<Down> TWL_to_clauses_state_conv
          (SPEC (conclusive_CDCL_run CS (init_state CS)))\<close>
    if
      \<open>Multiset.Ball CS distinct_mset \<and> (\<forall>C\<in>#CS. \<forall>L\<in>#C. nat_of_lit L \<le> uint_max)\<close> and
      CS'_CS: \<open>(CS', CS) \<in> list_mset_rel O \<langle>list_mset_rel\<rangle>mset_rel\<close> and
      spec: \<open>init_dt_wl_spec_full CS' (([], fmempty, None, {#}, {#}, {#}), {#}) T\<close> and
      confl: \<open>\<not> get_conflict_wl (fst T) \<noteq> None\<close> and
      [simp]: \<open>CS' = []\<close>
    for CS' CS T
  proof -
    let ?init = \<open>([], {#}, {#}, None) :: nat cdcl\<^sub>W_restart_mset\<close>
    let ?init_twl = \<open>([], {#}, {#}, None, {#}, {#}, {#}, {#}) :: nat twl_st\<close>
    let ?init_l = \<open>([], fmempty, None, {#}, {#}, {#}, {#}) :: nat twl_st_l\<close>
    let ?init_wl = \<open>([], fmempty, None, {#}, {#}, {#}, \<lambda>_. undefined) :: nat twl_st_wl\<close>
    have [simp]: \<open>CS = {#}\<close>
      using CS'_CS by (auto simp: in_list_mset_rel in_list_mset_rel_mset_rel)
    have [simp]: \<open>full cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy ?init ?init\<close>
      using full_cdcl\<^sub>W_init_state[of \<open>([], {#}, {#}, None)\<close>] by auto
    have eq: \<open>twl_st_of_wl None = state_wl_l None O twl_st_l None\<close>
      by (auto intro!: ext)
    have \<open>(?init_twl, ?init) \<in> {(S', S). S = state\<^sub>W_of S'}\<close>
      by auto
    moreover have \<open>(?init_l, ?init_twl) \<in> twl_st_l None\<close>
      by (auto simp: twl_st_l_def)
    moreover have \<open>(?init_wl, ?init_l) \<in> state_wl_l None\<close>
      by (auto simp: state_wl_l_def)
    ultimately have \<open>(?init_wl, ?init)
       \<in> (state_wl_l None O twl_st_l None) O {(S', S). S = state\<^sub>W_of S'}\<close>
      by fast

    then show ?thesis
      using spec confl
      unfolding init_dt_wl_spec_def conclusive_CDCL_run_def apply -
      apply (rule RETURN_SPEC_refine)
      apply (rule exI[of _ \<open>([], {#}, {#}, None)\<close>])
      apply (intro conjI)
      subgoal
        unfolding TWL_to_clauses_state_conv_def eq
        by assumption
      subgoal
        by (auto simp: cdcl\<^sub>W_cdcl\<^sub>W_init_state[unfolded init_state.simps])
      done
  qed

  have extract_atms_clss_not_nil: \<open>extract_atms_clss CS' {} \<noteq> {}\<close>
    if
      \<open>Multiset.Ball CS distinct_mset \<and> (\<forall>C\<in>#CS. \<forall>L\<in>#C. nat_of_lit L \<le> uint_max)\<close> and
      CS'_CS: \<open>(CS', CS) \<in> list_mset_rel O \<langle>list_mset_rel\<rangle>mset_rel\<close> and
      spec: \<open>init_dt_wl_spec_full CS' (([], fmempty, None, {#}, {#}, {#}), {#}) T\<close> and
      confl: \<open>\<not> get_conflict_wl (fst T) \<noteq> None\<close> and
      [simp]: \<open>CS' \<noteq> []\<close>
    for CS' CS T
  proof -
    obtain U V T' W where
      U: \<open>((([], fmempty, None, {#}, {#}, {#}), {#}), U) \<in> state_wl_l_init\<close> and
      T_V: \<open>(T', V) \<in> state_wl_l_init\<close> and
      \<open>correct_watching_init (fst T)\<close> and
      T_T': \<open>(T, T') \<in> added_only_watched\<close> and
      V_W: \<open>(V, W) \<in> twl_st_l_init\<close> and
      struct_invs: \<open>twl_struct_invs_init W\<close> and
      \<open>clauses_to_update_l_init V = {#}\<close> and
      count_dec: \<open>\<forall>s\<in>set (get_trail_l_init V). \<not> is_decided s\<close> and
      \<open>get_conflict_l_init V = None \<longrightarrow>
         literals_to_update_l_init V =
         uminus `# lit_of `# mset (get_trail_l_init V)\<close> and
      clss: \<open>mset `# mset CS' + mset `# ran_mf (get_clauses_l_init U) +
        other_clauses_l_init U +  get_unit_clauses_l_init U =
        mset `# ran_mf (get_clauses_l_init V) + other_clauses_l_init V +
          get_unit_clauses_l_init V\<close> and
      learned_UV: \<open>learned_clss_lf (get_clauses_l_init U) =
        learned_clss_lf (get_clauses_l_init V)\<close> and
      learned: \<open>get_learned_unit_clauses_l_init V = get_learned_unit_clauses_l_init U\<close> and
      \<open>twl_list_invs (fst V)\<close> and
      \<open>twl_stgy_invs (fst W)\<close> and
      snd_T_conflict: \<open>other_clauses_l_init V \<noteq> {#} \<longrightarrow> get_conflict_l_init V \<noteq> None\<close> and
      false_in_conflict: \<open>{#} \<in># mset `# mset CS' \<longrightarrow> get_conflict_l_init V \<noteq> None\<close> and
      \<open>get_conflict_l_init U \<noteq> None \<longrightarrow>
        get_conflict_l_init U = get_conflict_l_init V\<close>
      using spec unfolding init_dt_wl_spec_def init_dt_spec_def
        init_dt_wl_spec_full_def apply -
      apply normalize_goal+
      apply (rename_tac U T' V W)
      by presburger
    have CS: \<open>CS = mset `# mset CS'\<close>
      using CS'_CS by (auto simp: in_list_mset_rel in_list_mset_rel_mset_rel)
    have \<open>other_clauses_init_wl T' = {#}\<close>
      using snd_T_conflict confl T_V V_W T_T' by (auto simp: added_only_watched_def
         state_wl_l_init_def state_wl_l_init'_def twl_st_l_init_def)
    have \<open>\<exists>C\<in>set CS'. C \<noteq> []\<close>
    proof (rule ccontr)
      assume \<open>\<not> ?thesis\<close>
      then have E: \<open>\<forall>C\<in>set CS'. C = []\<close>
        by blast
      show False
        by (cases CS'; cases T; cases T')
          (use E false_in_conflict clss confl T_V V_W T_T' in
            \<open>auto simp: clauses_def CS state_wl_l_init_def state_wl_l_init'_def twl_st_l_init_def
            added_only_watched_def\<close>)
    qed
    then show ?thesis
      unfolding extract_atms_clss_empty_iff by auto
  qed

  have CDCL_steps:
    \<open>cdcl_twl_stgy_restart_prog_wl_D (mset_set (extract_atms_clss CS' {})) (fst T)
      \<le> \<Down> TWL_to_clauses_state_conv
          (SPEC (conclusive_CDCL_run CS (init_state CS)))\<close>
      (is ?steps is \<open>_ \<le> \<Down> _ ?Spec\<close>) and
    clauses: \<open>mset `# ran_mf (get_clauses_wl (fst T)) +
         get_unit_clauses_wl (fst T) = mset `# mset CS'\<close>
        (is ?clss) and
    break_CDCL_steps: \<open>cdcl_twl_stgy_restart_prog_wl_D (mset_set (extract_atms_clss CS' {})) (fst T)
    \<le> \<Down> TWL_to_clauses_state_conv (SPEC (conclusive_CDCL_run CS (init_state CS)))\<close>
      (is ?break_steps) and
    learned_clss: \<open>learned_clss_l (get_clauses_wl (fst T)) = {#}\<close> (is ?learned_clss)
    if
      CS_p: \<open>Multiset.Ball CS distinct_mset \<and> (\<forall>C\<in>#CS. \<forall>L\<in>#C. nat_of_lit L \<le> uint_max)\<close> and
      CS'_CS: \<open>(CS', CS) \<in> list_mset_rel O \<langle>list_mset_rel\<rangle>mset_rel\<close> and
      spec: \<open>init_dt_wl_spec_full CS' (([], fmempty, None, {#}, {#}, {#}), {#}) T\<close> and
      confl: \<open>\<not> get_conflict_wl (fst T) \<noteq> None\<close> and
      CS'_nempty: \<open>CS' \<noteq> []\<close> and
      \<open>extract_atms_clss CS' {} \<noteq> {}\<close> and
      [simp]: \<open>isasat_input_bounded_nempty (mset_set (extract_atms_clss CS' {}))\<close>
    for CS' CS T
  proof -
    obtain U V T' W where
      U: \<open>((([], fmempty, None, {#}, {#}, {#}), {#}), U) \<in> state_wl_l_init\<close> and
      T_V: \<open>(T', V) \<in> state_wl_l_init\<close> and
      corr_w: \<open>correct_watching_init (fst T)\<close> and
      T_T': \<open>(T, T') \<in> added_only_watched\<close> and
      V_W: \<open>(V, W) \<in> twl_st_l_init\<close> and
      struct_invs: \<open>twl_struct_invs_init W\<close> and
      clss_upd: \<open>clauses_to_update_l_init V = {#}\<close> and
      count_dec: \<open>\<forall>s\<in>set (get_trail_l_init V). \<not> is_decided s\<close> and
      \<open>get_conflict_l_init V = None \<longrightarrow>
         literals_to_update_l_init V =
         uminus `# lit_of `# mset (get_trail_l_init V)\<close> and
      clss: \<open>mset `# mset CS' + mset `# ran_mf (get_clauses_l_init U) +
        other_clauses_l_init U +  get_unit_clauses_l_init U =
        mset `# ran_mf (get_clauses_l_init V) + other_clauses_l_init V +
          get_unit_clauses_l_init V\<close> and
      learned_UV: \<open>learned_clss_lf (get_clauses_l_init U) =
        learned_clss_lf (get_clauses_l_init V)\<close> and
      learned: \<open>get_learned_unit_clauses_l_init V = get_learned_unit_clauses_l_init U\<close> and
      add_invs: \<open>twl_list_invs (fst V)\<close> and
      stgy_invs: \<open>twl_stgy_invs (fst W)\<close> and
      snd_T_conflict: \<open>other_clauses_l_init V \<noteq> {#} \<longrightarrow> get_conflict_l_init V \<noteq> None\<close> and
      false_in_conflict: \<open>{#} \<in># mset `# mset CS' \<longrightarrow> get_conflict_l_init V \<noteq> None\<close> and
      \<open>get_conflict_l_init U \<noteq> None \<longrightarrow>
        get_conflict_l_init U = get_conflict_l_init V\<close>
      using spec unfolding init_dt_wl_spec_def init_dt_spec_def
        init_dt_wl_spec_full_def apply -
      apply normalize_goal+
      apply (rename_tac U T' V W)
      by presburger
    have snd_T: \<open>other_clauses_init_wl T' = {#}\<close>
      using confl snd_T_conflict T_V V_W T_T'
      by (auto simp: twl_st_init twl_st_l_init twl_st_wl_init)
    have
      struct_invs: \<open>twl_struct_invs (fst W)\<close>
      apply (rule twl_struct_invs_init_twl_struct_invs)
      using snd_T struct_invs T_V V_W
      by (auto simp: twl_st_init twl_st_l_init twl_st_wl_init)
    obtain M N NE Q Wa UE where
      S\<^sub>0: \<open>T = ((M, N, None, NE, UE, Q, Wa), {#})\<close>
      using confl snd_T T_T'
      by (cases T) (auto simp: clauses_def mset_take_mset_drop_mset' added_only_watched_def)
    have learned_U:
      \<open>learned_clss_lf (get_clauses_l_init U) = {#}\<close>
      \<open>get_clauses_l_init U = fmempty\<close>
      \<open>other_clauses_l_init U  = {#}\<close>
      \<open>get_unit_clauses_l_init U = {#}\<close>
      using U T_V V_W T_T'
      by (cases U; auto simp: state_wl_l_init_def state_wl_l_def
           twl_st_l_init_def added_only_watched_def state_wl_l_init'_def; fail)+
    then have learned_W:
      \<open>get_learned_clauses_init W = {#}\<close> \<open>get_unit_learned_clauses_init W = {#}\<close>
      \<open>get_unit_init_clauses_init W = get_unit_clauses_l_init V\<close>
      using U T_V V_W learned learned_UV by (cases T; cases U; cases V;
         auto simp: state_wl_l_init_def state_wl_l_def twl_st_l_init_def; fail)+
    then have [simp]: \<open>UE = {#}\<close>
      using T_V V_W T_T' unfolding S\<^sub>0
      by (auto simp: state_wl_l_init_def state_wl_l_def twl_st_l_init_def
        added_only_watched_def state_wl_l_init'_def)
    have st:
      \<open>get_unit_clauses_l_init V = NE\<close>
      \<open>get_clauses_l_init V = N\<close>
      \<open>other_clauses_l_init V = {#}\<close>
      \<open>(M, trail (state\<^sub>W_of (fst W))) \<in> convert_lits_l N (NE+UE)\<close>
      \<open>get_trail_l_init V = M\<close>
      \<open>cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (fst W)) = mset `# (ran_mf N) + NE\<close>
      using T_V V_W T_T' unfolding S\<^sub>0
      by (auto simp: state_wl_l_init_def state_wl_l_def twl_st_l_init_def
          mset_take_mset_drop_mset mset_take_mset_drop_mset' clauses_def
          added_only_watched_def state_wl_l_init'_def
          simp del: all_clss_l_ran_m
          simp: all_clss_lf_ran_m[symmetric])
    have N_NE: \<open>mset `# ran_mf N + NE = mset `# mset CS'\<close>
      \<open>{#mset (fst x). x \<in># ran_m N#} + NE  = mset `# mset CS'\<close>
      using clss T_V V_W learned_U
      by (auto simp: clauses_def mset_take_mset_drop_mset' S\<^sub>0 st)
    define MW where \<open>MW = trail (state\<^sub>W_of (fst W))\<close>
    have st_W: \<open>state\<^sub>W_of (fst W) = (MW, mset `# mset CS', {#}, None)\<close>
      using T_V V_W learned_UV learned_U clss st T_T' unfolding S\<^sub>0
      by (auto simp: state_wl_l_init_def state_wl_l_def twl_st_l_init_def
          mset_take_mset_drop_mset mset_take_mset_drop_mset' clauses_def MW_def
          added_only_watched_def state_wl_l_init'_def
          simp del: all_clss_l_ran_m
          simp: all_clss_lf_ran_m[symmetric])
    have n_d: \<open>no_dup MW\<close> and
      propa: \<open>\<And>L mark a b. a @ Propagated L mark # b = MW \<Longrightarrow>
            b \<Turnstile>as CNot (remove1_mset L mark) \<and> L \<in># mark\<close> and
      clss_in_clss: \<open>set (get_all_mark_of_propagated MW) \<subseteq> set_mset (mset `# mset CS')\<close>
      using struct_invs unfolding twl_struct_invs_def S\<^sub>0 twl_struct_invs_init_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def st cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def
          N_NE st_W clauses_def
      by simp_all
    have count_dec': \<open>\<forall>L\<in>set MW. \<not>is_decided L\<close>
      using V_W count_dec unfolding st MW_def twl_st_init
      apply (subst twl_st_l_init_no_decision_iff)
       apply assumption
      using count_dec V_W unfolding st MW_def by auto
    have CS: \<open>CS = mset `# mset CS'\<close>
      using CS'_CS by (auto simp: in_list_mset_rel in_list_mset_rel_mset_rel)
    have 0: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* ([], CS, {#}, None)
       (MW, mset `# mset CS', {#}, None)\<close>
      using n_d count_dec' propa clss_in_clss
    proof (induction MW)
      case Nil
      then show ?case by (auto simp: CS)
    next
      case (Cons K MW) note IH = this(1) and H = this(2-) and n_d = this(2) and dec = this(3) and
        propa = this(4) and clss_in_clss = this(5)
      let ?init = \<open>([], CS, {#}, None)\<close>
      let ?int = \<open>(MW, mset `# mset CS', {#}, None)\<close>
      let ?final = \<open>(K # MW, mset `# mset CS', {#}, None)\<close>
      obtain L C where
        K: \<open>K = Propagated L C\<close>
        using dec by (cases K) auto
      have 1: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* ?init ?int\<close>
        apply (rule IH)
        subgoal using n_d by simp
        subgoal using dec by simp
        subgoal for M2 L' mark M1
          using K propa[of \<open>K # M2\<close> L' mark M1]
          by (auto split: if_splits)
        subgoal using clss_in_clss by (auto simp: K)
        done
      have \<open>MW \<Turnstile>as CNot (remove1_mset L C)\<close> and \<open>L \<in># C\<close>
        using propa[of \<open>[]\<close> L C \<open>MW\<close>]
        by (auto simp: K)
      moreover have \<open>C \<in># cdcl\<^sub>W_restart_mset.clauses (MW, mset `# mset CS', {#}, None)\<close>
        using clss_in_clss by (auto simp: K clauses_def split: if_splits)
      ultimately have \<open>cdcl\<^sub>W_restart_mset.propagate ?int
            (Propagated L C # MW, mset `# mset CS', {#}, None)\<close>
        using n_d apply -
        apply (rule cdcl\<^sub>W_restart_mset.propagate_rule[of _ \<open>C\<close> L])
        by (auto simp: K)
      then have 2: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy ?int ?final\<close>
        by (auto simp add: K dest!: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy.propagate')

      show ?case
        apply (rule rtranclp.rtrancl_into_rtrancl[OF 1])
        apply (rule 2)
        .
    qed
    have \<L>\<^sub>a\<^sub>l\<^sub>l: \<open>isasat_input_ops.is_\<L>\<^sub>a\<^sub>l\<^sub>l (mset_set (extract_atms_clss CS' {}))
        (all_lits_of_mm (mset `# mset CS'))\<close>
      by (auto simp add: is_\<L>\<^sub>a\<^sub>l\<^sub>l_extract_atms_clss)
    have [simp]: \<open>isasat_input_bounded (mset_set (extract_atms_clss CS' {}))\<close>
      unfolding isasat_input_bounded_def
    proof
      fix L
      assume L: \<open>L \<in># isasat_input_ops.\<L>\<^sub>a\<^sub>l\<^sub>l (mset_set (extract_atms_clss CS' {}))\<close>
      then obtain C where
        L: \<open>C\<in>set CS' \<and> (L \<in>set C \<or> - L \<in> set C)\<close>
      apply (cases L)
      apply (auto simp: extract_atms_clss_alt_def uint_max_def nat_of_uint32_uint32_of_nat_id
          isasat_input_ops.\<L>\<^sub>a\<^sub>l\<^sub>l_def)+
      apply (metis literal.exhaust_sel)+
      done
      have \<open>\<forall>C\<in>#CS. \<forall>L\<in>#C. nat_of_lit L \<le> uint_max\<close>
        using CS_p by auto
      then have \<open>nat_of_lit L \<le> uint_max \<or> nat_of_lit (-L) \<le> uint_max\<close>
        using L unfolding CS by auto
      then show \<open>nat_of_lit L \<le> uint_max\<close>
        using L
        by (cases L) (auto simp: CS extract_atms_clss_alt_def uint_max_def)
    qed
    have T_V': \<open>(fst T, fst V) \<in> state_wl_l None\<close>
      using T_V T_T' by (auto simp: S\<^sub>0 state_wl_l_def state_wl_l_init_def
        added_only_watched_def state_wl_l_init'_def)
    have V_W': \<open>(fst V, fst W) \<in> twl_st_l None\<close>
      using V_W by (auto simp: S\<^sub>0 twl_st_l_init_def twl_st_l_def)
    have valid_blits: \<open>\<And>L x. x\<in>set (Wa L) \<Longrightarrow>
           case x of (i, K, _) \<Rightarrow> K \<in># all_lits_of_mm (mset `# mset CS')\<close>
      using corr_w unfolding correct_watching_init.simps st
      by (auto simp: st N_NE \<L>\<^sub>a\<^sub>l\<^sub>l S\<^sub>0 isasat_input_ops.literals_are_\<L>\<^sub>i\<^sub>n_def
        isasat_input_ops.blits_in_\<L>\<^sub>i\<^sub>n_def correct_watching.simps
        all_blits_are_in_problem_init.simps
        state_wl_l_def  correct_watching_init.simps in_\<L>\<^sub>a\<^sub>l\<^sub>l_extract_atms_clss_in_all_lits_of_mm)
    have \<open>cdcl_twl_stgy_prog_l_pre (fst V) (fst W)\<close>
      unfolding cdcl_twl_stgy_prog_l_pre_def
      using V_W' struct_invs corr_w add_invs clss confl clss stgy_invs confl T_V clss_upd T_T'
      by (auto simp: twl_st_init twl_st_l_init twl_st_wl_init)

    then have \<open>cdcl_twl_stgy_prog_wl_pre (fst T) (fst W)\<close>
      unfolding cdcl_twl_stgy_prog_wl_pre_def apply -
      apply (rule exI[of _ \<open>fst V\<close>])
      using T_V' corr_w by (simp add: correct_watching_init_correct_watching)
    then have 1: \<open>isasat_input_ops.cdcl_twl_stgy_prog_wl_D_pre (mset_set (extract_atms_clss CS' {})) (fst T) (fst W)\<close>
      unfolding isasat_input_ops.cdcl_twl_stgy_prog_wl_D_pre_def
        cdcl_twl_stgy_prog_wl_pre_def
      by (auto simp: st N_NE \<L>\<^sub>a\<^sub>l\<^sub>l S\<^sub>0 isasat_input_ops.literals_are_\<L>\<^sub>i\<^sub>n_def
        isasat_input_ops.blits_in_\<L>\<^sub>i\<^sub>n_def correct_watching.simps
        all_blits_are_in_problem_init.simps in_\<L>\<^sub>a\<^sub>l\<^sub>l_extract_atms_clss_in_all_lits_of_mm
        state_wl_l_def correct_watching_init.simps
        dest!:  valid_blits)
    have 2:\<open>cdcl_twl_stgy_restart_prog_wl_D (mset_set (extract_atms_clss CS' {}))
             (from_init_state T)
            \<le> \<Down> (state_wl_l None O twl_st_l None)
                 (conclusive_TWL_run (fst W))\<close>
      unfolding cdcl_twl_stgy_restart_prog_wl_D_def
      apply (rule isasat_input_bounded_nempty.cdcl_twl_stgy_restart_prog_wl_D_spec_final
        [of \<open>(mset_set (extract_atms_clss CS' {}))\<close>])
      using CS_p \<L>\<^sub>a\<^sub>l\<^sub>l struct_invs corr_w add_invs clss confl clss
      by (auto simp: from_init_state_def st 1)

    have conclusive_le: \<open>(conclusive_TWL_run (fst W)) \<le> \<Down> ({(S', S). S = state\<^sub>W_of S'}) ?Spec\<close>
      unfolding conc_fun_RES conclusive_TWL_run_def less_eq_nres.simps
    proof
      fix x
      assume \<open>x \<in> {T. \<exists>n n'.
             cdcl_twl_stgy_restart_with_leftovers\<^sup>*\<^sup>* (fst W, n) (T, n') \<and> final_twl_state T}\<close>
      then obtain n n' where
        twl: \<open>cdcl_twl_stgy_restart_with_leftovers\<^sup>*\<^sup>* (fst W, n) (x, n')\<close> and
       final: \<open>final_twl_state x\<close>
        by blast+
      have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart_stgy\<^sup>*\<^sup>* (state\<^sub>W_of (fst W), n) (state\<^sub>W_of x, n')\<close>
        using rtranclp_cdcl_twl_stgy_restart_with_leftovers_cdcl\<^sub>W_restart_stgy[OF twl] struct_invs
          stgy_invs by simp
      with cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_stgy_cdcl\<^sub>W_restart_stgy[OF 0, of n]
      have stgy: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart_stgy\<^sup>*\<^sup>* (([], mset `# mset CS', {#}, None), n)
            (state\<^sub>W_of x, n')\<close>
        unfolding st_W CS by simp
      have struct_invs_x: \<open>twl_struct_invs x\<close>
        using twl struct_invs rtranclp_cdcl_twl_stgy_restart_with_leftovers_twl_struct_invs[OF twl]
        by simp
      then have all_struct_invs_x: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of x)\<close>
        unfolding twl_struct_invs_def
        by blast

      have M_lev: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv ([], mset `# mset CS', {#}, None)\<close>
        by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def)

      have learned: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause ([], mset `# mset CS', {#}, None)\<close>
        unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def
        by auto
      have ent: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init ([], mset `# mset CS', {#}, None)\<close>
        by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def)

      have [simp]: \<open>CS' \<noteq> []\<close>
        using CS'_nempty by (auto simp: CS)

      have entailed: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of x)\<close>
        apply (rule cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_learned_clauses_entailed)
           apply (rule cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_restart_stgy_cdcl\<^sub>W_restart[OF stgy, unfolded fst_conv])
          apply (rule learned)
         apply (rule M_lev)
        apply (rule ent)
        done


      consider
        (ns) \<open>no_step cdcl_twl_stgy x\<close> |
        (stop) \<open>get_conflict x \<noteq> None\<close> and \<open>count_decided (get_trail x) = 0\<close>
        using final unfolding final_twl_state_def by auto
      then show \<open>x \<in> {(S', S). S = state\<^sub>W_of S'}\<inverse> ``
          Collect(conclusive_CDCL_run CS (init_state CS) )\<close>
      proof cases
        case ns
        from no_step_cdcl_twl_stgy_no_step_cdcl\<^sub>W_stgy[OF this]
        have \<open>no_step cdcl\<^sub>W_restart_mset.cdcl\<^sub>W (state\<^sub>W_of x)\<close>
          using struct_invs struct_invs_x by (blast dest: cdcl\<^sub>W_ex_cdcl\<^sub>W_stgy)
        then show ?thesis
          using twl stgy
          unfolding conclusive_CDCL_run_def
          by (auto simp: CS)
      next
        case stop
        have \<open>unsatisfiable (set_mset (init_clss (state\<^sub>W_of x)))\<close>
          apply (rule conflict_of_level_unsatisfiable)
             apply (rule all_struct_invs_x)
          using entailed stop by (auto simp: twl_st)
        then have \<open>unsatisfiable (mset ` set CS')\<close>
          using cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_restart_init_clss[symmetric, OF
             cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_restart_stgy_cdcl\<^sub>W_restart[OF stgy]]
          by auto

        then show ?thesis
          using stop
          by (auto simp: CS twl_st_init twl_st conclusive_CDCL_run_def)
      qed
    qed
    show ?steps
      unfolding TWL_to_clauses_state_conv_def from_init_state_def[symmetric]
      apply (rule order_trans)
       apply (rule 2)
      apply (subst (2) conc_fun_chain[symmetric])
      apply (rule ref_two_step)
       prefer 2
       apply (rule conclusive_le)
      apply simp
      done
    show ?clss
      using clss U unfolding all_clss_lf_ran_m
      by (cases U)
        (auto simp: S\<^sub>0 state_wl_l_init_def state_wl_l_def N_NE)

    have 2:\<open>cdcl_twl_stgy_restart_prog_wl_D (mset_set (extract_atms_clss CS' {}))
             (from_init_state T)
            \<le> \<Down> (state_wl_l None O twl_st_l None)
                 (conclusive_TWL_run (fst W))\<close>
      unfolding cdcl_twl_stgy_restart_prog_wl_D_def
      apply (rule isasat_input_bounded_nempty.cdcl_twl_stgy_restart_prog_wl_D_spec_final
        [of \<open>(mset_set (extract_atms_clss CS' {}))\<close>])
      using CS_p \<L>\<^sub>a\<^sub>l\<^sub>l
        struct_invs corr_w add_invs clss confl clss
      by (auto simp: from_init_state_def st 1)
    show ?break_steps
      unfolding TWL_to_clauses_state_conv_def from_init_state_def[symmetric]
      apply (rule order_trans)
       apply (rule 2)
      apply (subst (2) conc_fun_chain[symmetric])
      apply (rule ref_two_step)
       prefer 2
       apply (rule conclusive_le)
      by simp
    show ?learned_clss
      using learned_U learned_UV T_V T_T'
      by (cases T, cases V) (auto simp: state_wl_l_init_def state_wl_l_def
        added_only_watched_def state_wl_l_init'_def)
  qed

  have init: \<open>init_dt_wl_pre CS' (([], fmempty, None, {#}, {#}, {#}), {#})\<close>
    if \<open>Ball (set CS') distinct\<close> for CS'
    using that
    by (auto simp: init_dt_wl_pre_def init_dt_pre_def state_wl_l_init_def
        twl_st_l_init_def state_wl_l_def correct_watching_init.simps clause_to_update_def
        twl_init_invs all_blits_are_in_problem_init.simps
        state_wl_l_init'_def)

  have [simp]: \<open>finite (extract_atms_clss CS' {})\<close> for CS'
    by  (auto simp: extract_atms_clss_alt_def)

  have K: \<open>mset_set (extract_atms_clss CS' {}) = {#} \<longleftrightarrow> (\<forall>C \<in>set CS'. C = [])\<close> for CS'
    by  (auto simp: extract_atms_clss_alt_def mset_set_empty_iff)
  then have K'[dest]: \<open>x \<in> (extract_atms_clss CS' {}) \<Longrightarrow> \<not>(\<forall>C \<in>set CS'. C = [])\<close> for CS' x
    using K[of CS'] by (auto simp:  mset_set_empty_iff)
  show ?thesis
    unfolding SAT_wl_def SAT_def from_init_state_def to_init_state_def
     isasat_input_ops.empty_watched_alt_def finalise_init_def id_def
    apply (intro frefI nres_relI)
    subgoal for CS' CS
      apply (rewrite at \<open>let _ = extract_atms_clss _ _ in _\<close> Let_def)
      apply (simp only: if_False isasat_input_ops.init_state_wl_def
          isasat_input_ops.empty_watched_alt_def)
      apply (refine_vcg  (* bind_refine_spec*) lhs_step_If init_dt_wl_init_dt_wl_spec
         bind_refine_spec[OF _ init_dt_wl_full_init_dt_wl_spec_full])
      \<comment> \<open>First the fast part:\<close>
      thm spec
      subgoal for b by (rule conflict_during_init)
      subgoal for T by (rule empty_clss)
      subgoal by (rule extract_atms_clss_not_nil)
      subgoal by (auto simp: in_list_mset_rel in_list_mset_rel_mset_rel K
         isasat_input_bounded_nempty_def isasat_input_bounded_nempty_axioms_def)
      subgoal by (rule clauses)
      subgoal by (rule learned_clss)
      subgoal by (rule break_CDCL_steps)
      subgoal by (rule init) (auto simp: in_list_mset_rel in_list_mset_rel_mset_rel)
(*       \<comment> \<open>Now the slow part: \<close>
      subgoal for b by (rule conflict_during_init)
      subgoal for T by (rule empty_clss)
      subgoal by (rule extract_atms_clss_not_nil)
      subgoal by (auto simp: in_list_mset_rel in_list_mset_rel_mset_rel K
         isasat_input_bounded_nempty_def isasat_input_bounded_nempty_axioms_def)
      subgoal by (rule clauses)
      subgoal by (rule learned_clss)
      subgoal by (rule CDCL_steps)
      subgoal by (rule init) (auto simp: in_list_mset_rel in_list_mset_rel_mset_rel) *)
      done
    done
qed

definition model_if_satisfiable :: \<open>nat clauses \<Rightarrow> nat literal list option nres\<close> where
  \<open>model_if_satisfiable CS = SPEC (\<lambda>M.
           if satisfiable (set_mset CS) then M \<noteq> None \<and> set (the M) \<Turnstile>sm CS else M = None)\<close>

definition SAT' :: \<open>nat clauses \<Rightarrow> nat literal list option nres\<close> where
  \<open>SAT' CS = do {
     T \<leftarrow> SAT CS;
     RETURN(if conflicting T = None then Some (map lit_of (trail T)) else None)
  }
\<close>

lemma SAT_model_if_satisfiable:
  \<open>(SAT', model_if_satisfiable) \<in> [\<lambda>CS. (\<forall>C \<in># CS. distinct_mset C)]\<^sub>f Id\<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
    (is \<open>_ \<in>[\<lambda>CS. ?P CS]\<^sub>f Id \<rightarrow> _\<close>)
proof -
  have H: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (init_state CS)\<close>
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (init_state CS)\<close>
    if \<open>?P CS\<close> for CS
    using that by (auto simp:
        twl_struct_invs_def twl_st_inv.simps cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
        cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
        cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def cdcl\<^sub>W_restart_mset.no_smaller_propa_def
        past_invs.simps clauses_def twl_list_invs_def twl_stgy_invs_def clause_to_update_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant_def
        cdcl\<^sub>W_restart_mset.no_smaller_confl_def
        distinct_mset_set_def)
  have H: \<open>s \<in> {M. if satisfiable (set_mset CS) then M \<noteq> None \<and> set (the M) \<Turnstile>sm CS else M = None}\<close>
    if
      dist: \<open>Multiset.Ball CS distinct_mset\<close> and
      [simp]: \<open>CS' = CS\<close> and
      s: \<open>s \<in> (\<lambda>T. if conflicting T = None then Some (map lit_of (trail T)) else None) `
          Collect (conclusive_CDCL_run CS' (init_state CS'))\<close>
    for s :: \<open>nat literal list option\<close> and CS CS'
  proof -
    obtain T where
       s: \<open>(s = Some (map lit_of (trail T)) \<and> conflicting T = None) \<or>
              (s = None \<and> conflicting T \<noteq> None)\<close> and
       conc: \<open>conclusive_CDCL_run CS' ([], CS', {#}, None) T\<close>
      using s by auto force
    consider
      n n' where \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart_stgy\<^sup>*\<^sup>* (([], CS', {#}, None), n) (T, n')\<close>
      \<open>no_step cdcl\<^sub>W_restart_mset.cdcl\<^sub>W T\<close> |
      \<open>CS' \<noteq> {#}\<close> and \<open>conflicting T \<noteq> None\<close> and \<open>backtrack_lvl T = 0\<close> and
         \<open>unsatisfiable (set_mset CS')\<close>
      using conc unfolding conclusive_CDCL_run_def
      by auto
    then show ?thesis
    proof cases
      case (1 n n') note st = this(1) and ns = this(2)
      have \<open>no_step cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy T\<close>
        using ns cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_cdcl\<^sub>W by blast
      then have full_T: \<open>full cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy T T\<close>
        unfolding full_def by blast

      have invs: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant T\<close>
        \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv T\<close>
        using st cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_restart_dcl\<^sub>W_all_struct_inv[OF st]
          cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_restart_dcl\<^sub>W_stgy_invariant[OF st]
          H[OF dist] by auto
      have res: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart\<^sup>*\<^sup>* ([], CS', {#}, None) T\<close>
        using cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_restart_stgy_cdcl\<^sub>W_restart[OF st] by simp
      have ent: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init T\<close>
        using cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_learned_clauses_entailed[OF res] H[OF dist]
        unfolding \<open>CS' = CS\<close> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
        by simp
      have [simp]: \<open>init_clss T = CS\<close>
        using cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_restart_init_clss[OF res] by simp
      show ?thesis
        using cdcl\<^sub>W_restart_mset.full_cdcl\<^sub>W_stgy_inv_normal_form[OF full_T invs ent] s
        by (auto simp: true_annots_true_cls lits_of_def)
    next
      case 2
      moreover have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (init_state CS)\<close>
        unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def
        by auto
      ultimately show ?thesis
        using H[OF dist] cdcl\<^sub>W_restart_mset.full_cdcl\<^sub>W_stgy_inv_normal_form[of \<open>init_state CS\<close>
             \<open>init_state CS\<close>] s
        by auto
    qed
  qed
  show ?thesis
    unfolding SAT'_def model_if_satisfiable_def SAT_def Let_def
    apply (intro frefI nres_relI)
    subgoal for CS' CS
      unfolding RES_RETURN_RES
      apply (rule RES_refine)
      unfolding pair_in_Id_conv bex_triv_one_point1 bex_triv_one_point2
      by (rule H)
    done
qed

lemma SAT_model_if_satisfiable':
  \<open>(uncurry (\<lambda>_. SAT'), uncurry (\<lambda>_. model_if_satisfiable)) \<in>
    [\<lambda>(_, CS). (\<forall>C \<in># CS. distinct_mset C)]\<^sub>f Id \<times>\<^sub>r Id\<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  using SAT_model_if_satisfiable by (auto simp: fref_def)

lemma list_assn_list_mset_rel_clauses_l_assn:
  \<open>(hr_comp (list_assn (list_assn unat_lit_assn)) (list_mset_rel O \<langle>list_mset_rel\<rangle>mset_rel)) xs xs'
     = clauses_l_assn xs xs'\<close>
proof -
  have ex_remove_xs:
    \<open>(\<exists>xs. mset xs = mset x \<and> {#literal_of_nat (nat_of_uint32 x). x \<in># mset xs#} = y) \<longleftrightarrow>
       ({#literal_of_nat (nat_of_uint32 x). x \<in># mset x#} = y)\<close>
    for x y
    by auto

  show ?thesis
    unfolding list_assn_pure_conv list_mset_assn_pure_conv
     list_rel_mset_rel_def
    apply (auto simp: hr_comp_def)
    apply (auto simp: ent_ex_up_swap list_mset_assn_def pure_def)
    using ex_mset[of \<open>map (\<lambda>x. literal_of_nat (nat_of_uint32 x)) `# mset xs'\<close>]
    by (auto simp add: list_mset_rel_def br_def mset_rel_def unat_lit_rel_def
        uint32_nat_rel_def nat_lit_rel_def
        p2rel_def Collect_eq_comp rel2p_def
        list_all2_op_eq_map_map_right_iff rel_mset_def rel2p_def[abs_def]
        list_all2_op_eq_map_right_iff' ex_remove_xs list_rel_def
        list_all2_op_eq_map_right_iff
        simp del: literal_of_nat.simps)
qed

lemma (in isasat_input_ops) twl_st_heur_init_vmtf_next_emptyD:
  \<open>((x1, x1a, x1b, x1c, x1d, ((x1g, x1h, x1i, x1j, x2h), x2i), x1k, x2k), Ta)
       \<in> twl_st_heur_parsing \<Longrightarrow> \<A>\<^sub>i\<^sub>n \<noteq> {#} \<Longrightarrow> x1i \<noteq> None\<close>
  by (auto simp: isasat_input_ops.twl_st_heur_parsing_def isasat_input_ops.vmtf_init_def)

lemma (in isasat_input_ops) twl_st_heur_init_vmtf_fstD:
  \<open>((x1, x1a, x1b, x1c, x1d, ((x1g, x1h, x1i, x1j, x2h), x2i), x1k, x2k), Ta)
       \<in> twl_st_heur_parsing \<Longrightarrow> \<A>\<^sub>i\<^sub>n \<noteq> {#} \<Longrightarrow> x1j \<noteq> None\<close>
  by (auto simp: isasat_input_ops.twl_st_heur_parsing_def isasat_input_ops.vmtf_init_def)


lemma get_conflict_wl_is_None_init_get_conflict_wl_is_None_heur_init[simp]:
  \<open>(Tb, Ta) \<in> isasat_input_ops.twl_st_heur_parsing A \<Longrightarrow>
     get_conflict_wl_is_None_init (from_init_state Ta) = get_conflict_wl_is_None_heur_init Tb\<close>
  by (cases Ta; cases Tb)
    (auto simp: from_init_state_def
      get_conflict_wl_is_None_init_def get_conflict_wl_is_None_heur_init_def
      isasat_input_ops.twl_st_heur_parsing_def isasat_input_ops.option_lookup_clause_rel_def
      get_conflict_wl_is_None_def split: option.splits)


(* lemma(in isasat_input_ops) get_clauses_wl_from_init_get_clauses_wl_heur_init:
  \<open>(T, Ta) \<in> twl_st_heur_init \<Longrightarrow> get_clauses_wl (from_init_state Ta) = get_clauses_wl_heur_init T\<close>
  by (cases T; cases Ta)
    (auto simp: twl_st_heur_init_def twl_st_heur_init_wl_def from_init_state_def)

lemma isasat_input_bounded_nempty_cdcl_twl_stgy_prog_wl_D_heur_break_cdcl_twl_stgy_prog_wl_D':
  \<open>isasat_input_bounded_nempty \<A> \<Longrightarrow> (S, S') \<in> isasat_input_ops.twl_st_heur \<A> \<Longrightarrow> \<A> = \<A>' \<Longrightarrow>
   isasat_input_ops.cdcl_twl_stgy_prog_break_wl_D_heur_break \<A> S
    \<le> \<Down> (isasat_input_ops.twl_st_heur \<A>)
         (isasat_input_ops.cdcl_twl_stgy_prog_break_wl_D \<A>' S')\<close>
  using isasat_input_bounded_nempty.cdcl_twl_stgy_prog_wl_D_heur_break_cdcl_twl_stgy_prog_wl_D
             [THEN fref_to_Down, unfolded comp_def, of \<A> S S']
  by fast *)

lemma isasat_input_bounded_nempty_cdcl_twl_stgy_restart_prog_wl_D_heur_break_cdcl_twl_stgy_prog_wl_D':
  \<open>isasat_input_bounded_nempty \<A> \<Longrightarrow> (S, S') \<in> isasat_input_ops.twl_st_heur \<A> \<Longrightarrow> \<A> = \<A>' \<Longrightarrow>
    isasat_input_ops.cdcl_twl_stgy_restart_prog_wl_heur \<A> S
    \<le> \<Down>(isasat_input_ops.twl_st_heur \<A>)
         (cdcl_twl_stgy_restart_prog_wl_D \<A>' S')\<close>
  unfolding cdcl_twl_stgy_restart_prog_wl_D_def
  using isasat_input_bounded_nempty.cdcl_twl_stgy_restart_prog_wl_heur_cdcl_twl_stgy_restart_prog_wl_D
             [THEN fref_to_Down, unfolded comp_def, of \<A> S S']
  by fast

lemma IsaSAT_heur_IsaSAT: \<open>(uncurry IsaSAT_heur, uncurry (\<lambda>_. IsaSAT)) \<in>
     [\<lambda>(_, CS). Multiset.Ball (mset CS) distinct \<and> (\<forall>C\<in>set CS. \<forall>L\<in>set C. nat_of_lit L \<le> uint_max)]\<^sub>f
     Id \<times>\<^sub>r Id \<rightarrow> \<langle>{((M, stat), M'). map_option rev M = M'}\<rangle>nres_rel\<close>
proof -
  have H: \<open>A + B = C \<Longrightarrow> A \<subseteq># C\<close> for A B C
    by auto
  define f :: \<open>twl_st_wl_heur_init \<Rightarrow> twl_st_wl_heur_init nres\<close> where \<open>f = RETURN\<close>
  have IsaSAT_heur_alt_def: \<open>IsaSAT_heur opts CS = do{
    ASSERT(\<forall>C\<in>set CS. \<forall>L\<in>set C. nat_of_lit L \<le> uint_max);
    let \<A>\<^sub>i\<^sub>n'' = mset_set (extract_atms_clss CS {});
    ASSERT(isasat_input_bounded \<A>\<^sub>i\<^sub>n'');
    ASSERT(distinct_mset \<A>\<^sub>i\<^sub>n'');
    let b = False;
    \<^cancel>\<open>if b \<and> length CS < uint_max - 1
    then do {
        S \<leftarrow> isasat_input_ops.init_state_wl_heur \<A>\<^sub>i\<^sub>n'';
        S \<leftarrow> f S;
        (T::twl_st_wl_heur_init) \<leftarrow> isasat_input_ops.init_dt_wl_heur \<A>\<^sub>i\<^sub>n'' CS S;
        if \<not>get_conflict_wl_is_None_heur_init T
        then RETURN (empty_init_code)
        else if CS = [] then empty_conflict_code
        else do {
           ASSERT(\<A>\<^sub>i\<^sub>n'' \<noteq> {#});
           ASSERT(isasat_input_bounded_nempty \<A>\<^sub>i\<^sub>n'');
           ASSERT((\<lambda>(M', N', D', Q', W', ((ns, m, fst_As, lst_As, next_search), to_remove), \<phi>, clvls). fst_As \<noteq> None \<and>
             lst_As \<noteq> None) T);
           T \<leftarrow> finalise_init_code (T::twl_st_wl_heur_init);
           ASSERT(isasat_fast T);
           U \<leftarrow> isasat_input_ops.cdcl_twl_stgy_prog_wl_D_heur \<A>\<^sub>i\<^sub>n'' T;
           RETURN (if get_conflict_wl_is_None_heur U then extract_model_of_state_stat U
             else extract_state_stat U)
         }
      }
    else\<close>
        S \<leftarrow> isasat_input_ops.init_state_wl_heur \<A>\<^sub>i\<^sub>n'';
        S \<leftarrow> f S;
        (T::twl_st_wl_heur_init) \<leftarrow> isasat_input_ops.init_dt_wl_heur_full \<A>\<^sub>i\<^sub>n'' CS S;
        if \<not>get_conflict_wl_is_None_heur_init T
        then RETURN (empty_init_code)
        else if CS = [] then empty_conflict_code
        else do {
           ASSERT(\<A>\<^sub>i\<^sub>n'' \<noteq> {#});
           ASSERT(isasat_input_bounded_nempty \<A>\<^sub>i\<^sub>n'');
           ASSERT((\<lambda>(M', N', D', Q', W', ((ns, m, fst_As, lst_As, next_search), to_remove), \<phi>, clvls). fst_As \<noteq> None \<and>
             lst_As \<noteq> None) T);
           T \<leftarrow> finalise_init_code opts (T::twl_st_wl_heur_init);
           U \<leftarrow> isasat_input_ops.cdcl_twl_stgy_restart_prog_wl_heur \<A>\<^sub>i\<^sub>n'' T;
           RETURN (if get_conflict_wl_is_None_heur U then extract_model_of_state_stat U
             else extract_state_stat U)
         }

    }\<close>  (is \<open>?A = ?B\<close>) for CS opts
  proof -
    have [simp]: \<open>ASSERT \<Phi> \<bind> (\<lambda>_. P) \<le> ASSERT \<Phi> \<bind> (\<lambda>_. Q) \<longleftrightarrow> (\<Phi> \<longrightarrow> P \<le> Q)\<close> for \<Phi> P Q
      using Refine_Basic.le_ASSERTI_pres by auto

    have 1: \<open>?A \<le> ?B\<close>
      unfolding IsaSAT_heur_def Let_def isasat_input_ops.init_state_wl_heur_fast_def f_def
        empty_conflict_code_def empty_conflict_code_def empty_init_code_def convert_state_def
        isasat_information_banner_def
      apply (refine_vcg lhs_step_If)
       apply (auto intro!:  Refine_Basic.bind_mono)
      (* apply (subst isasat_input_ops.init_dt_wl_heur_fast_init_dt_wl_heur)
      apply (auto simp: isasat_input_ops.init_state_wl_heur_def map_fun_rel_def
          RES_RES_RETURN_RES RETURN_def in_class_in_literals_are_in_\<L>\<^sub>i\<^sub>n Max_dom_fmempty) *)
      done

    have 2: \<open>?B \<le> ?A\<close>
      unfolding IsaSAT_heur_def Let_def isasat_input_ops.init_state_wl_heur_fast_def f_def
        empty_conflict_code_def empty_conflict_code_def empty_init_code_def convert_state_def
        isasat_information_banner_def
      apply (refine_vcg lhs_step_If)
      apply (auto intro!:  Refine_Basic.bind_mono)
      (* apply (subst isasat_input_ops.init_dt_wl_heur_fast_init_dt_wl_heur)
      apply (auto simp: isasat_input_ops.init_state_wl_heur_def map_fun_rel_def
          RES_RES_RETURN_RES RETURN_def in_class_in_literals_are_in_\<L>\<^sub>i\<^sub>n Max_dom_fmempty) *)
      done
    show ?thesis using 1 2 by simp
  qed

  have [refine]: \<open>inres
        (isasat_input_ops.init_state_wl_heur
          (mset_set (extract_atms_clss x {})))
        S \<Longrightarrow>
       (S, isasat_input_ops.init_state_wl)
       \<in> isasat_input_ops.twl_st_heur_parsing_no_WL_wl N \<Longrightarrow>
       f S
       \<le> \<Down> {(T, (T', OS)). (T, (T', OS)) \<in> isasat_input_ops.twl_st_heur_parsing_no_WL N}
          (RETURN (to_init_state isasat_input_ops.init_state_wl))\<close>
    (is \<open>_ \<Longrightarrow>_ \<Longrightarrow> _ \<le> \<Down> ?init _\<close>)
    for S T' N x
    by (auto simp: f_def inres_def isasat_input_ops.init_state_wl_heur_def
        RES_RETURN_RES RES_RES_RETURN_RES)
     (auto simp: f_def to_init_state_def isasat_input_ops.twl_st_heur_parsing_no_WL_def
      isasat_input_ops.twl_st_heur_parsing_no_WL_wl_def isasat_input_ops.init_state_wl_def)


  have init: \<open>isasat_input_ops.init_dt_wl_heur_full (mset_set (extract_atms_clss CS {})) CS T'
      \<le> \<Down> (isasat_input_ops.twl_st_heur_parsing (mset_set (extract_atms_clss CS' {})))
          (init_dt_wl_full CS'
             (to_init_state (isasat_input_ops.init_state_wl)))\<close>
    if
      distinct: \<open>Multiset.Ball (mset CS') distinct\<close> and
      SS': \<open>(CS, CS') \<in> Id\<close> and
      bounded: \<open>isasat_input_bounded (mset_set (extract_atms_clss CS' {}))\<close> and
      TT': \<open>inres (f T) T'\<close> and
      T': \<open>(T', to_init_state (isasat_input_ops.init_state_wl))
        \<in> {(T, T', OS).
          (T, (T', OS)) \<in> isasat_input_ops.twl_st_heur_parsing_no_WL (mset_set (extract_atms_clss CS' {}))}\<close>
    for CS CS' T T'
  proof -
    have SS': \<open>CS = CS'\<close>
      using SS' by auto
    have [simp]: \<open>T = T'\<close>
      using TT' unfolding f_def by auto
    have H: \<open>C \<in> set CS' \<Longrightarrow> \<exists>CS'''. set CS' = insert C CS'''\<close> for C
      by auto
    have [simp]: \<open>C \<in> set CS' \<Longrightarrow>
       isasat_input_ops.literals_are_in_\<L>\<^sub>i\<^sub>n (mset_set (extract_atms_clss CS' {})) (mset C)\<close> for C
      apply (auto simp: isasat_input_ops.literals_are_in_\<L>\<^sub>i\<^sub>n_def isasat_input_ops.\<L>\<^sub>a\<^sub>l\<^sub>l_def
          extract_atms_clss_alt_def in_all_lits_of_m_ain_atms_of_iff atm_of_eq_atm_of
          atms_of_s_def image_image image_Un in_image_uminus_uminus[symmetric]
          dest!: H)
      apply (metis (no_types, lifting) image_iff literal.exhaust_sel)+
      done
    have pre: \<open>init_dt_wl_pre CS' (to_init_state isasat_input_ops.init_state_wl)\<close>
      using distinct
      unfolding init_dt_wl_pre_def init_dt_pre_def
      by (auto simp: state_wl_l_init_def isasat_input_ops.init_state_wl_def
        to_init_state_def state_wl_l_init'_def twl_st_l_init_def
        twl_init_invs)
    show ?thesis
      unfolding SS'
      apply (rule isasat_input_bounded.init_dt_wl_heur_full_init_dt_wl_full)
      subgoal by (rule bounded)
      subgoal by (rule pre)
      subgoal using T' by (auto simp: isasat_input_ops.twl_st_heur_parsing_no_WL_wl_def)
      subgoal using T' distinct by (auto simp: isasat_input_ops.twl_st_heur_parsing_no_WL_wl_def
            distinct_mset_set_def)
      subgoal using T' by (cases \<open>to_init_state isasat_input_ops.init_state_wl\<close>) simp
      done
  qed

  have from_init_state: \<open>(T, from_init_state Ta)
        \<in> isasat_input_ops.twl_st_heur_post_parsing_wl
          (mset_set (extract_atms_clss y {}))\<close>
    if
      T_Ta: \<open>(T, Ta)
      \<in> isasat_input_ops.twl_st_heur_parsing
          (mset_set (extract_atms_clss y {}))\<close> and
      \<open>\<not> \<not> get_conflict_wl_is_None_heur_init T\<close>
    for T Ta x y Sa b
  proof -
    show ?thesis
      using T_Ta
      unfolding f_def
      by (auto simp: isasat_input_ops.twl_st_heur_parsing_def from_init_state_def
         isasat_input_ops.twl_st_heur_post_parsing_wl_def )
        (metis set_mset_mset)+
  qed
  have finalise_init: \<open>get_conflict_wl y = None \<Longrightarrow> \<A> \<noteq> {#} \<Longrightarrow> size (learned_clss_l (get_clauses_wl y)) = 0 \<Longrightarrow>
    (y', y) \<in> isasat_input_ops.twl_st_heur_post_parsing_wl \<A> \<Longrightarrow>
    finalise_init_code x' y' \<le> \<Down> (isasat_input_ops.twl_st_heur \<A>) (RETURN (finalise_init y))\<close>
    for y x' y'  \<A>
    by (rule isasat_input_ops.finalise_init_finalise_init[THEN fref_to_Down_curry, unfolded comp_def]) auto

  show ?thesis
    supply RETURN_as_SPEC_refine[refine2 del]
    unfolding IsaSAT_heur_alt_def IsaSAT_def uncurry_def
    apply (intro frefI nres_relI bind_refine if_refine)
    apply (refine_vcg
           init
           init_state_wl_heur_init_state_wl[THEN fref_to_Down, unfolded comp_def, OF refl]
           from_init_state
           isasat_input_bounded_nempty.cdcl_twl_stgy_prog_wl_D_heur_cdcl_twl_stgy_prog_wl_D
             [THEN fref_to_Down_explode, unfolded comp_def]
           isasat_input_bounded_nempty_cdcl_twl_stgy_restart_prog_wl_D_heur_break_cdcl_twl_stgy_prog_wl_D')
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    apply (rule IdI)
                 apply (assumption)+
    subgoal by auto
    subgoal by auto
                  apply (assumption)+
    subgoal by auto
    subgoal by (auto simp: empty_init_code_def)
    subgoal premises p
      by (auto simp: empty_init_code_def)
    subgoal by auto
    subgoal premises p
      by (auto simp: empty_conflict_code_def op_arl_empty_def)
    subgoal by auto
    subgoal by auto
    subgoal
      by (auto dest: isasat_input_ops.twl_st_heur_init_vmtf_next_emptyD)
    subgoal
      by (auto dest!: isasat_input_ops.twl_st_heur_init_vmtf_fstD)
       apply (rule finalise_init)
    subgoal
      by (auto simp: get_conflict_wl_is_None_init_def get_conflict_wl_is_None_def
          split: option.splits)
         apply assumption+
    apply (rule from_init_state;assumption)
(*     subgoal for CS CS' b S' S T U' U
      by (rule dom_m_le_uint_max)
    subgoal by fast
    subgoal by fast
    subgoal premises p
      using p(32)
      by (auto simp: extract_model_of_state_stat_def extract_model_of_state_def
          isasat_input_ops.twl_st_heur_def get_conflict_wl_is_None_heur_def
          get_conflict_wl_is_None_heur_init_def extract_state_stat_def rev_map
          get_conflict_wl_is_None_def split: option.splits)
    subgoal by auto
    apply assumption+
    subgoal by fast
    apply assumption+
    subgoal by simp
    subgoal premises p by (simp add: empty_init_code_def)
    subgoal by simp
    subgoal premises p by (simp add: empty_conflict_code_def op_arl_empty_def)
    subgoal by auto
    subgoal by auto
    subgoal
      by (auto simp: isasat_input_ops.get_clauses_wl_from_init_get_clauses_wl_heur_init
        intro: mset_subset_eq_add_left dest: H)
    subgoal
      by (auto dest: isasat_input_ops.twl_st_heur_init_vmtf_next_emptyD)
    subgoal
      by (auto dest!: isasat_input_ops.twl_st_heur_init_vmtf_fstD)
    subgoal
      by (auto simp: isasat_input_ops.twl_st_heur_init_def
        state_wl_l_def from_init_state_def)
    subgoal
      unfolding get_conflict_wl_is_None_init_def get_conflict_wl_is_None by meson
    apply assumption+
    subgoal
      by (rule isasat_input_ops.twl_st_heur_init_wl) *)
    subgoal by auto
    subgoal by auto
    subgoal premises p
      using p(29)
      by (auto simp: extract_model_of_state_stat_def extract_model_of_state_def
          isasat_input_ops.twl_st_heur_def get_conflict_wl_is_None_heur_def
          get_conflict_wl_is_None_heur_init_def extract_state_stat_def rev_map
          isasat_input_ops.option_lookup_clause_rel_def
          get_conflict_wl_is_None_def split: option.splits)
    done
qed

lemma [simp]: \<open>finite (extract_atms_clss CS {})\<close>
  by (auto simp: extract_atms_clss_alt_def)

lemma IsaSAT_code: \<open>(uncurry IsaSAT_code, uncurry (\<lambda>_. SAT'))
    \<in> [\<lambda>(_, x). Multiset.Ball x distinct_mset \<and> (\<forall>C\<in>#x. \<forall>L\<in>#C. nat_of_lit L \<le> uint_max)]\<^sub>a
      opts_assn\<^sup>d *\<^sub>a clauses_l_assn\<^sup>k \<rightarrow> model_assn\<close>
proof -
  define empty_trail where
    \<open>empty_trail = Some ([] :: nat literal list)\<close>
  have 1: \<open>B = C \<Longrightarrow> ((A :: _ nres) \<bind> B) = ((A :: _ nres) \<bind> C)\<close> for A B C
    by auto
  have [simp]: \<open>mset_set (extract_atms_clss CS {}) \<noteq> {#} \<longleftrightarrow> extract_atms_clss CS {} \<noteq> {}\<close> for CS
    using mset_set_empty_iff[of \<open>extract_atms_clss CS {}\<close>]
    by (auto simp: )
  have IsaSAT: \<open>IsaSAT CS = do {
     ASSERT (isasat_input_bounded (mset_set (extract_atms_clss CS {})));
     ASSERT (distinct_mset (mset_set (extract_atms_clss CS {})));
     T \<leftarrow> SAT_wl CS;
     RETURN (if get_conflict_wl T = None then extract_model_of_state T else None)
    }\<close> for CS
    unfolding IsaSAT_def SAT_wl_def Let_def get_conflict_wl_is_None_init_def
     finalise_init_def id_def get_conflict_wl_is_None[symmetric] empty_trail_def
     extract_model_of_state_def
    by (auto cong: bind_cong simp:  intro: bind_cong intro!: 1 ext)

  have 2: \<open>Multiset.Ball y distinct_mset \<Longrightarrow>
       (x, y) \<in> list_mset_rel O \<langle>list_mset_rel\<rangle>mset_rel \<Longrightarrow>
        (\<forall>C\<in>#y. \<forall>L\<in>#C. nat_of_lit L \<le> uint_max) \<Longrightarrow>
       SAT_wl x \<le> \<Down> TWL_to_clauses_state_conv (SAT y)\<close> for x y
    using cdcl_twl_stgy_prog_wl_spec_final2[unfolded fref_def nres_rel_def] by simp
  have SAT': \<open>SAT' CS =
       do {
          ASSERT(True);ASSERT(True);
          U \<leftarrow> SAT CS;
          RETURN(if conflicting U = None then Some (map lit_of (trail U)) else None)
      }\<close> for CS
    unfolding SAT'_def SAT_def empty_trail_def by (auto simp: RES_RETURN_RES)
  have 3:
    \<open>ASSERT (isasat_input_bounded (mset_set (extract_atms_clss x {}))) \<le> \<Down> unit_rel (ASSERT True)\<close>
    if CS_p: \<open>(\<forall>C\<in>#y. \<forall>L\<in>#C. nat_of_lit L \<le> uint_max)\<close> and
       CS: \<open>(x, y) \<in> list_mset_rel O \<langle>list_mset_rel\<rangle>mset_rel\<close>
       for x y
    apply (rule ASSERT_refine)
    unfolding isasat_input_bounded_def
  proof
    fix L
    assume L: \<open>L \<in># isasat_input_ops.\<L>\<^sub>a\<^sub>l\<^sub>l (mset_set (extract_atms_clss x {}))\<close>
    then obtain C where
      L: \<open>C\<in>set x \<and> (L \<in>set C \<or> - L \<in> set C)\<close>
      apply (cases L)
      apply (auto simp: extract_atms_clss_alt_def uint_max_def nat_of_uint32_uint32_of_nat_id
          isasat_input_ops.\<L>\<^sub>a\<^sub>l\<^sub>l_def)+
      apply (metis literal.exhaust_sel)+
      done
    have \<open>\<forall>C\<in>#y. \<forall>L\<in>#C. nat_of_lit L \<le> uint_max\<close>
      using CS_p by auto
    then have \<open>nat_of_lit L \<le> uint_max \<or> nat_of_lit (-L) \<le> uint_max\<close>
      using L CS by (auto simp: list_mset_rel_def br_def mset_rel_def rel2p_def[abs_def] p2rel_def
        rel_mset_def list_all2_op_eq_map_right_iff')
    then show \<open>nat_of_lit L \<le> uint_max\<close>
      using L
      by (cases L) (auto simp: extract_atms_clss_alt_def uint_max_def)
  qed
  have 4: \<open>ASSERT (distinct_mset (mset_set (extract_atms_clss x {}))) \<le> \<Down> unit_rel (ASSERT True)\<close>
    for x
    by (auto simp: distinct_mset_def)
  have IsaSAT_SAT: \<open>(IsaSAT, SAT') \<in>
     [\<lambda>CS. Multiset.Ball CS distinct_mset \<and>
      (\<forall>C\<in>#CS. \<forall>L\<in>#C. nat_of_lit L \<le> uint_max)]\<^sub>f
     list_mset_rel O \<langle>list_mset_rel\<rangle>mset_rel \<rightarrow> \<langle>\<langle>\<langle>Id\<rangle>list_rel\<rangle> option_rel\<rangle>nres_rel\<close>
    unfolding SAT' IsaSAT
    apply (intro frefI nres_relI bind_refine if_refine)
         apply (rule 3; simp; fail)
        apply (rule 4; simp; fail)
     apply (rule 2)
    by (auto simp: TWL_to_clauses_state_conv_def extract_model_of_state_def
        state_wl_l_def twl_st_l_def convert_lits_l_map_lit_of)
  then have IsaSAT_SAT: \<open>(uncurry (\<lambda>_. IsaSAT), uncurry (\<lambda>_. SAT')) \<in>
     [\<lambda>(_, CS). Multiset.Ball CS distinct_mset \<and>
      (\<forall>C\<in>#CS. \<forall>L\<in>#C. nat_of_lit L \<le> uint_max)]\<^sub>f
     Id \<times>\<^sub>r list_mset_rel O \<langle>list_mset_rel\<rangle>mset_rel \<rightarrow> \<langle>\<langle>\<langle>Id\<rangle>list_rel\<rangle> option_rel\<rangle>nres_rel\<close>
    unfolding SAT' IsaSAT
    by (auto simp: fref_def)
  have [simp]: \<open> \<up> (x = map_option rev ac) =  \<up> (ac = map_option rev x)\<close> for x ac
    by (cases ac; cases x) auto
  have H: \<open>hr_comp model_stat_assn
        (Collect (case_prod (\<lambda>(M, stat). (=) (map_option rev M)))) = model_assn\<close>
    by (auto simp: model_assn_def hr_comp_def model_stat_rel_def ex_assn_pair_split eq_commute
        intro!: ext)
  have H: \<open>(uncurry IsaSAT_code, uncurry (\<lambda>_. IsaSAT))
      \<in> [\<lambda>(_, x). Ball (set x) distinct  \<and> (\<forall>C\<in>set x. \<forall>L\<in>set C. nat_of_lit L \<le> uint_max)]\<^sub>a
         opts_assn\<^sup>d *\<^sub>a (list_assn (list_assn unat_lit_assn))\<^sup>k \<rightarrow> model_assn\<close>
    using IsaSAT_code.refine[FCOMP IsaSAT_heur_IsaSAT]
    unfolding list_assn_list_mset_rel_clauses_l_assn H
    by auto
  show ?thesis
    (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
  proof -
    have H: \<open>?c \<in>
       [comp_PRE (Id \<times>\<^sub>f list_mset_rel O \<langle>list_mset_rel\<rangle>mset_rel)
     (\<lambda>(_, CS). Multiset.Ball CS distinct_mset \<and> (\<forall>C\<in>#CS. \<forall>L\<in>#C. nat_of_lit L \<le> uint_max))
     (\<lambda>x y. case y of (uu_, x) \<Rightarrow> Ball (set x) distinct \<and> (\<forall>C\<in>set x. \<forall>L\<in>set C. nat_of_lit L \<le> uint_max))
     (\<lambda>x. nofail
            (uncurry (\<lambda>_. SAT')
              x))]\<^sub>a hrp_comp (opts_assn\<^sup>d *\<^sub>a (list_assn (list_assn unat_lit_assn))\<^sup>k)
                      (Id \<times>\<^sub>f
                       list_mset_rel O
                       \<langle>list_mset_rel\<rangle>mset_rel) \<rightarrow> hr_comp model_assn (\<langle>\<langle>nat_lit_lit_rel\<rangle>list_rel\<rangle>option_rel)\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
      using hfref_compI_PRE[OF H IsaSAT_SAT] .
    have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
      using that by (auto simp: comp_PRE_def list_mset_rel_def br_def
          mset_rel_def p2rel_def rel2p_def[abs_def] rel_mset_def
          list_all2_op_eq_map_right_iff')
    have im: \<open>?im' = ?im\<close>
      unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
        list_assn_list_mset_rel_clauses_l_assn by auto
    have f: \<open>?f' = ?f\<close>
      by auto
    show ?thesis
      apply (rule hfref_weaken_pre[OF ])
       defer
      using H unfolding im f apply assumption
      using pre ..
  qed
qed

text \<open>Final correctness theorem:\<close>
lemmas IsaSAT_code_full_correctness = IsaSAT_code[FCOMP SAT_model_if_satisfiable']

end
