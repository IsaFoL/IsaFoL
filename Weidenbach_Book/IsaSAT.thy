theory IsaSAT
  imports IsaSAT_Restart IsaSAT_Initialisation Version
begin

subsection \<open>Final code generation\<close>
text \<open>
  We now combine all the previous definitions to prove correctness of the complete SAT
  solver:
  \<^enum> We initialise the arena part of the state;
  \<^enum> Then depending on the options and the number of clauses, we either use the
    bounded version or the unbounded version. Once have if decided which one,
    we initiale the watch lists;
  \<^enum> After that, we can run the CDCL part of the SAT solver;
  \<^enum> Finally, we extract the trail from the state.

  Remark that the statistics and the options are unchecked: the number of propagations
  might overflows (but they do not impact the correctness of the whole solver). Similar
  restriction applies on the options: setting the options might not do what you expect to
  happen, but the result will still be correct.
\<close>


subsubsection \<open>Correctness Relation\<close>

text \<open>
  We cannot use \<^term>\<open>cdcl_twl_stgy_restart\<close> since we do not always end in a final state
  for \<^term>\<open>cdcl_twl_stgy\<close>.
\<close>
definition conclusive_TWL_run :: \<open>'v twl_st \<Rightarrow> 'v twl_st nres\<close> where
  \<open>conclusive_TWL_run S =
    SPEC(\<lambda>T. \<exists>n n'. cdcl_twl_stgy_restart_with_leftovers\<^sup>*\<^sup>* (S, n) (T, n') \<and> final_twl_state T)\<close>


text \<open>To get a full CDCL run:
  \<^item> either we fully apply \<^term>\<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<close> (up to restarts)
  \<^item> or we can stop early.
\<close>
definition conclusive_CDCL_run where
  \<open>conclusive_CDCL_run CS T U \<longleftrightarrow>
      (\<exists>n n'. cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart_stgy\<^sup>*\<^sup>* (T, n) (U, n') \<and>
              no_step cdcl\<^sub>W_restart_mset.cdcl\<^sub>W (U)) \<or>
          (CS \<noteq> {#} \<and> conflicting U \<noteq> None \<and> count_decided (trail U) = 0 \<and>
          unsatisfiable (set_mset CS))\<close>

lemma cdcl_twl_stgy_restart_restart_prog_spec: \<open>twl_struct_invs S \<Longrightarrow>
  twl_stgy_invs S \<Longrightarrow>
  clauses_to_update S = {#} \<Longrightarrow>
  get_conflict S = None \<Longrightarrow>
  cdcl_twl_stgy_restart_prog S \<le> conclusive_TWL_run S\<close>
  apply (rule order_trans)
  apply (rule cdcl_twl_stgy_restart_prog_spec; assumption?)
  unfolding conclusive_TWL_run_def twl_restart_def
  by auto

lemma cdcl_twl_stgy_restart_restart_prog_early_spec: \<open>twl_struct_invs S \<Longrightarrow>
  twl_stgy_invs S \<Longrightarrow>
  clauses_to_update S = {#} \<Longrightarrow>
  get_conflict S = None \<Longrightarrow>
  cdcl_twl_stgy_restart_prog_early S \<le> conclusive_TWL_run S\<close>
  apply (rule order_trans)
  apply (rule cdcl_twl_stgy_prog_early_spec; assumption?)
  unfolding conclusive_TWL_run_def twl_restart_def
  by auto


theorem cdcl_twl_stgy_restart_prog_wl_D_spec:
  assumes \<open>literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st S) S\<close>
  shows \<open>cdcl_twl_stgy_restart_prog_wl_D S \<le> \<Down>Id (cdcl_twl_stgy_restart_prog_wl S)\<close>
  apply (rule cdcl_twl_stgy_restart_prog_wl_D_cdcl_twl_stgy_restart_prog_wl[
    THEN fref_to_Down, of S S, THEN order_trans])
    apply fast
  using assms apply (auto intro: conc_fun_R_mono)[]
  apply (rule conc_fun_R_mono)
  apply auto
  done

theorem cdcl_twl_stgy_restart_prog_early_wl_D_spec:
  assumes \<open>literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st S) S\<close>
  shows \<open>cdcl_twl_stgy_restart_prog_early_wl_D S \<le> \<Down>Id (cdcl_twl_stgy_restart_prog_early_wl S)\<close>
  apply (rule cdcl_twl_stgy_restart_prog_early_wl_D_cdcl_twl_stgy_restart_prog_early_wl[
    THEN fref_to_Down, THEN order_trans])
  apply fast
  using assms apply auto[]
  apply (rule conc_fun_R_mono)
  apply auto
  done

lemma distinct_nat_of_uint32[iff]:
  \<open>distinct_mset (nat_of_uint32 `# A) \<longleftrightarrow> distinct_mset A\<close>
  \<open>distinct (map nat_of_uint32 xs) \<longleftrightarrow> distinct xs\<close>
  using distinct_image_mset_inj[of nat_of_uint32]
  by (auto simp: inj_on_def distinct_map)

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

definition init_state_l :: \<open>'v twl_st_l_init\<close> where
  \<open>init_state_l = (([], fmempty, None, {#}, {#}, {#}, {#}), {#})\<close>

definition to_init_state_l :: \<open>nat twl_st_l_init \<Rightarrow> nat twl_st_l_init\<close> where
  \<open>to_init_state_l S = S\<close>

definition init_state0 :: \<open>'v twl_st_init\<close> where
  \<open>init_state0 = (([], {#}, {#}, None, {#}, {#}, {#}, {#}), {#})\<close>

definition to_init_state0 :: \<open>nat twl_st_init \<Rightarrow> nat twl_st_init\<close> where
  \<open>to_init_state0 S = S\<close>

lemma init_dt_pre_init:
  assumes dist: \<open>Multiset.Ball (mset `# mset CS) distinct_mset\<close>
  shows  \<open>init_dt_pre CS (to_init_state_l init_state_l)\<close>
  using dist apply -
  unfolding init_dt_pre_def to_init_state_l_def init_state_l_def
  by (rule exI[of _ \<open>(([], {#}, {#}, None, {#}, {#}, {#}, {#}), {#})\<close>])
    (auto simp: twl_st_l_init_def twl_init_invs)


text \<open>This is the specification of the SAT solver:\<close>
definition SAT :: \<open>nat clauses \<Rightarrow> nat cdcl\<^sub>W_restart_mset nres\<close> where
  \<open>SAT CS = do{
    let T = init_state CS;
    SPEC (conclusive_CDCL_run CS T)
  }\<close>


definition init_dt_spec0 :: \<open>'v clause_l list \<Rightarrow> 'v twl_st_init \<Rightarrow> 'v twl_st_init \<Rightarrow> bool\<close> where
  \<open>init_dt_spec0 CS SOC T' \<longleftrightarrow>
     (
      twl_struct_invs_init T' \<and>
      clauses_to_update_init T' = {#} \<and>
      (\<forall>s\<in>set (get_trail_init T'). \<not>is_decided s) \<and>
      (get_conflict_init T' = None \<longrightarrow>
	 literals_to_update_init T' = uminus `# lit_of `# mset (get_trail_init T')) \<and>
      (mset `# mset CS + clause `# (get_init_clauses_init SOC) + other_clauses_init SOC +
	    get_unit_init_clauses_init SOC =
       clause `# (get_init_clauses_init T') + other_clauses_init T'  +
	    get_unit_init_clauses_init T') \<and>
      get_learned_clauses_init SOC = get_learned_clauses_init T' \<and>
      get_unit_learned_clauses_init T' = get_unit_learned_clauses_init SOC \<and>
      twl_stgy_invs (fst T') \<and>
      (other_clauses_init T' \<noteq> {#} \<longrightarrow> get_conflict_init T' \<noteq> None) \<and>
      ({#} \<in># mset `# mset CS \<longrightarrow> get_conflict_init T' \<noteq> None) \<and>
      (get_conflict_init SOC \<noteq> None \<longrightarrow> get_conflict_init SOC = get_conflict_init T'))\<close>


subsubsection \<open>Refinements of the Whole SAT Solver\<close>

text \<open>
  We do no add the refinement steps in separate files, since the form is very specific
  to the SAT solver we want to generate (and needs to be updated if it changes).
\<close>
definition  SAT0 :: \<open>nat clause_l list \<Rightarrow> nat twl_st nres\<close> where
  \<open>SAT0 CS = do{
    b \<leftarrow> SPEC(\<lambda>_::bool. True);
    if b then do {
        let S = init_state0;
        T \<leftarrow> SPEC (init_dt_spec0 CS (to_init_state0 S));
        let T = fst T;
        if get_conflict T \<noteq> None
        then RETURN T
        else if CS = [] then RETURN (fst init_state0)
        else do {
          ASSERT (extract_atms_clss CS {} \<noteq> {});
	  ASSERT (clauses_to_update T = {#});
          ASSERT(clause `# (get_clauses T) + unit_clss T = mset `# mset CS);
          ASSERT(get_learned_clss T = {#});
          cdcl_twl_stgy_restart_prog T
        }
    }
    else do {
        let S = init_state0;
        T \<leftarrow>  SPEC (init_dt_spec0 CS (to_init_state0 S));
        failed \<leftarrow> SPEC (\<lambda>_ :: bool. True);
        if failed then do {
          T \<leftarrow>  SPEC (init_dt_spec0 CS (to_init_state0 S));
          let T = fst T;
          if get_conflict T \<noteq> None
          then RETURN T
          else if CS = [] then RETURN (fst init_state0)
          else do {
            ASSERT (extract_atms_clss CS {} \<noteq> {});
            ASSERT (clauses_to_update T = {#});
            ASSERT(clause `# (get_clauses T) + unit_clss T = mset `# mset CS);
            ASSERT(get_learned_clss T = {#});
            cdcl_twl_stgy_restart_prog T
        }
        } else do {
          let T = fst T;
          if get_conflict T \<noteq> None
          then RETURN T
          else if CS = [] then RETURN (fst init_state0)
          else do {
            ASSERT (extract_atms_clss CS {} \<noteq> {});
            ASSERT (clauses_to_update T = {#});
            ASSERT(clause `# (get_clauses T) + unit_clss T = mset `# mset CS);
            ASSERT(get_learned_clss T = {#});
            cdcl_twl_stgy_restart_prog_early T
          }
        }
     }
  }\<close>

lemma SAT0_SAT:
  assumes \<open>Multiset.Ball (mset `# mset CS) distinct_mset\<close>
  shows \<open>SAT0 CS \<le> \<Down> {(S, T). T = state\<^sub>W_of S} (SAT (mset `# mset CS))\<close>
proof -
  have conflict_during_init: \<open>RETURN (fst T)
	\<le> \<Down> {(S, T). T = state\<^sub>W_of S}
	   (SPEC (conclusive_CDCL_run (mset `# mset CS)
	       (init_state (mset `# mset CS))))\<close>
    if
      spec: \<open>T \<in> Collect (init_dt_spec0 CS (to_init_state0 init_state0))\<close> and
      confl: \<open>get_conflict (fst T) \<noteq> None\<close>
    for T
  proof -
    let ?CS = \<open>mset `# mset CS\<close>
    have
      struct_invs: \<open>twl_struct_invs_init T\<close> and
      \<open>clauses_to_update_init T = {#}\<close> and
      count_dec: \<open>\<forall>s\<in>set (get_trail_init T). \<not> is_decided s\<close> and
      \<open>get_conflict_init T = None \<longrightarrow>
       literals_to_update_init T =
       uminus `# lit_of `# mset (get_trail_init T)\<close> and
      clss: \<open>mset `# mset CS +
       clause `# get_init_clauses_init (to_init_state0 init_state0) +
       other_clauses_init (to_init_state0 init_state0) +
       get_unit_init_clauses_init (to_init_state0 init_state0) =
       clause `# get_init_clauses_init T + other_clauses_init T +
       get_unit_init_clauses_init T\<close> and
      learned: \<open>get_learned_clauses_init (to_init_state0 init_state0) =
          get_learned_clauses_init T\<close>
        \<open>get_unit_learned_clauses_init T =
          get_unit_learned_clauses_init (to_init_state0 init_state0)\<close> and
      \<open>twl_stgy_invs (fst T)\<close> and
      \<open>other_clauses_init T \<noteq> {#} \<longrightarrow> get_conflict_init T \<noteq> None\<close> and
      \<open>{#} \<in># mset `# mset CS \<longrightarrow> get_conflict_init T \<noteq> None\<close> and
      \<open>get_conflict_init (to_init_state0 init_state0) \<noteq> None \<longrightarrow>
       get_conflict_init (to_init_state0 init_state0) = get_conflict_init T\<close>
      using spec unfolding init_dt_wl_spec_def init_dt_spec0_def
        Set.mem_Collect_eq apply -
      apply normalize_goal+
      by fast+

    have count_dec: \<open>count_decided (get_trail (fst T)) = 0\<close>
      using count_dec unfolding count_decided_0_iff by (auto simp: twl_st_init
        twl_st_wl_init)

    have le: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause (state\<^sub>W_of_init T)\<close> and
      all_struct_invs:
        \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of_init T)\<close>
      using struct_invs unfolding twl_struct_invs_init_def
         cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      by fast+
    have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (state\<^sub>W_of_init T)\<close>
      using struct_invs unfolding twl_struct_invs_init_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      by fast
    have \<open>unsatisfiable (set_mset (mset `# mset (rev CS)))\<close>
      using conflict_of_level_unsatisfiable[OF all_struct_invs] count_dec confl
        learned le clss
      by (auto simp: clauses_def mset_take_mset_drop_mset' twl_st_init twl_st_wl_init
           image_image to_init_state0_def init_state0_def
           cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def ac_simps
	   twl_st_l_init)
    then have unsat[simp]: \<open>unsatisfiable (mset ` set CS)\<close>
      by auto
    then have [simp]: \<open>CS \<noteq> []\<close>
      by (auto simp del: unsat)
    show ?thesis
      unfolding conclusive_CDCL_run_def
      apply (rule RETURN_SPEC_refine)
      apply (rule exI[of _ \<open>state\<^sub>W_of (fst T)\<close>])
      apply (intro conjI)
      subgoal
        by auto
      subgoal
        apply (rule disjI2)
        using struct_invs learned count_dec clss confl
        by (clarsimp simp: twl_st_init twl_st_wl_init twl_st_l_init)
      done
  qed

  have empty_clauses: \<open>RETURN (fst init_state0)
	\<le> \<Down> {(S, T). T = state\<^sub>W_of S}
	   (SPEC
	     (conclusive_CDCL_run (mset `# mset CS)
	       (init_state (mset `# mset CS))))\<close>
    if
      \<open>T \<in> Collect (init_dt_spec0 CS (to_init_state0 init_state0))\<close> and
      \<open>\<not> get_conflict (fst T) \<noteq> None\<close> and
      \<open>CS = []\<close>
    for T
  proof -
    have [dest]: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W ([], {#}, {#}, None) (a, aa, ab, b) \<Longrightarrow> False\<close>
      for a aa ab b
      by (metis cdcl\<^sub>W_restart_mset.cdcl\<^sub>W.cases cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy.conflict'
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy.propagate' cdcl\<^sub>W_restart_mset.other'
	cdcl\<^sub>W_stgy_cdcl\<^sub>W_init_state_empty_no_step init_state.simps)
    show ?thesis
      by (rule RETURN_RES_refine, rule exI[of _ \<open>init_state {#}\<close>])
        (use that in \<open>auto simp: conclusive_CDCL_run_def init_state0_def\<close>)
  qed

  have extract_atms_clss_nempty: \<open>extract_atms_clss CS {} \<noteq> {}\<close>
    if
      \<open>T \<in> Collect (init_dt_spec0 CS (to_init_state0 init_state0))\<close> and
      \<open>\<not> get_conflict (fst T) \<noteq> None\<close> and
      \<open>CS \<noteq> []\<close>
    for T
  proof -
    show ?thesis
      using that
      by (cases T; cases CS)
        (auto simp: init_state0_def to_init_state0_def init_dt_spec0_def
          extract_atms_clss_alt_def)
  qed

  have cdcl_twl_stgy_restart_prog: \<open>cdcl_twl_stgy_restart_prog (fst T)
	\<le> \<Down> {(S, T). T = state\<^sub>W_of S}
	   (SPEC
	     (conclusive_CDCL_run (mset `# mset CS)
	       (init_state (mset `# mset CS))))\<close> (is ?G1) and
      cdcl_twl_stgy_restart_prog_early: \<open>cdcl_twl_stgy_restart_prog_early (fst T)
	\<le> \<Down> {(S, T). T = state\<^sub>W_of S}
	   (SPEC
	     (conclusive_CDCL_run (mset `# mset CS)
	       (init_state (mset `# mset CS))))\<close> (is ?G2)
    if
      spec: \<open>T \<in> Collect (init_dt_spec0 CS (to_init_state0 init_state0))\<close> and
      confl: \<open>\<not> get_conflict (fst T) \<noteq> None\<close> and
      CS_nempty[simp]: \<open>CS \<noteq> []\<close> and
      \<open>extract_atms_clss CS {} \<noteq> {}\<close> and
      \<open>clause `# get_clauses (fst T) + unit_clss (fst T) = mset `# mset CS\<close> and
      \<open>get_learned_clss (fst T) = {#}\<close>
    for T
  proof -
    let ?CS = \<open>mset `# mset CS\<close>
    have
      struct_invs: \<open>twl_struct_invs_init T\<close> and
      clss_to_upd: \<open>clauses_to_update_init T = {#}\<close> and
      count_dec: \<open>\<forall>s\<in>set (get_trail_init T). \<not> is_decided s\<close> and
      \<open>get_conflict_init T = None \<longrightarrow>
       literals_to_update_init T =
       uminus `# lit_of `# mset (get_trail_init T)\<close> and
      clss: \<open>mset `# mset CS +
       clause `# get_init_clauses_init (to_init_state0 init_state0) +
       other_clauses_init (to_init_state0 init_state0) +
       get_unit_init_clauses_init (to_init_state0 init_state0) =
       clause `# get_init_clauses_init T + other_clauses_init T +
       get_unit_init_clauses_init T\<close> and
      learned: \<open>get_learned_clauses_init (to_init_state0 init_state0) =
          get_learned_clauses_init T\<close>
        \<open>get_unit_learned_clauses_init T =
          get_unit_learned_clauses_init (to_init_state0 init_state0)\<close> and
      stgy_invs: \<open>twl_stgy_invs (fst T)\<close> and
      oth: \<open>other_clauses_init T \<noteq> {#} \<longrightarrow> get_conflict_init T \<noteq> None\<close> and
      \<open>{#} \<in># mset `# mset CS \<longrightarrow> get_conflict_init T \<noteq> None\<close> and
      \<open>get_conflict_init (to_init_state0 init_state0) \<noteq> None \<longrightarrow>
       get_conflict_init (to_init_state0 init_state0) = get_conflict_init T\<close>
      using spec unfolding init_dt_wl_spec_def init_dt_spec0_def
        Set.mem_Collect_eq apply -
      apply normalize_goal+
      by fast+
    have struct_invs: \<open>twl_struct_invs (fst T)\<close>
      by (rule twl_struct_invs_init_twl_struct_invs)
        (use struct_invs oth confl in \<open>auto simp: twl_st_init\<close>)
    have clss_to_upd: \<open>clauses_to_update (fst T) = {#}\<close>
      using clss_to_upd by (auto simp: twl_st_init)

    have conclusive_le: \<open>conclusive_TWL_run (fst T)
    \<le> \<Down> {(S, T). T = state\<^sub>W_of S}
       (SPEC
         (conclusive_CDCL_run (mset `# mset CS) (init_state (mset `# mset CS))))\<close>
      unfolding IsaSAT.conclusive_TWL_run_def
    proof (rule RES_refine)
      fix Ta
      assume s: \<open>Ta \<in> {Ta.
             \<exists>n n'.
                cdcl_twl_stgy_restart_with_leftovers\<^sup>*\<^sup>* (fst T, n) (Ta, n') \<and>
                final_twl_state Ta}\<close>
      then obtain n n' where
        twl: \<open>cdcl_twl_stgy_restart_with_leftovers\<^sup>*\<^sup>* (fst T, n) (Ta, n')\<close> and
	final: \<open>final_twl_state Ta\<close>
	by blast
      have stgy_T_Ta: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart_stgy\<^sup>*\<^sup>* (state\<^sub>W_of (fst T), n) (state\<^sub>W_of Ta, n')\<close>
	using rtranclp_cdcl_twl_stgy_restart_with_leftovers_cdcl\<^sub>W_restart_stgy[OF twl] struct_invs
	  stgy_invs by simp

      have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart_stgy\<^sup>*\<^sup>* (state\<^sub>W_of (fst T), n) (state\<^sub>W_of Ta, n')\<close>
	using rtranclp_cdcl_twl_stgy_restart_with_leftovers_cdcl\<^sub>W_restart_stgy[OF twl] struct_invs
	  stgy_invs by simp

      have struct_invs_x: \<open>twl_struct_invs Ta\<close>
	using twl struct_invs rtranclp_cdcl_twl_stgy_restart_with_leftovers_twl_struct_invs[OF twl]
	by simp
      then have all_struct_invs_x: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of Ta)\<close>
	unfolding twl_struct_invs_def
	by blast

      have M_lev: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv ([], mset `# mset CS, {#}, None)\<close>
	by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def)

      have learned': \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause ([], mset `# mset CS, {#}, None)\<close>
	unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_alt_def
	by auto
      have ent: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init ([], mset `# mset CS, {#}, None)\<close>
	 by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def)
      define MW where \<open>MW \<equiv> get_trail_init T\<close>
      have CS_clss: \<open>cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (fst T)) = mset `# mset CS\<close>
        using learned clss oth confl unfolding clauses_def to_init_state0_def init_state0_def
	  cdcl\<^sub>W_restart_mset.clauses_def
	by (cases T) auto
      have n_d: \<open>no_dup MW\<close> and
	propa: \<open>\<And>L mark a b. a @ Propagated L mark # b = MW \<Longrightarrow>
	      b \<Turnstile>as CNot (remove1_mset L mark) \<and> L \<in># mark\<close> and
	clss_in_clss: \<open>set (get_all_mark_of_propagated MW) \<subseteq> set_mset ?CS\<close>
	using struct_invs unfolding twl_struct_invs_def twl_struct_invs_init_def
	    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
	    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def st cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_alt_def
	    clauses_def MW_def clss to_init_state0_def init_state0_def CS_clss[symmetric]
        by ((cases T; auto)+)[3]

      have count_dec': \<open>\<forall>L\<in>set MW. \<not>is_decided L\<close>
	using count_dec unfolding st MW_def twl_st_init by auto
      have st_W: \<open>state\<^sub>W_of (fst T) = (MW, ?CS, {#}, None)\<close>
        using clss st learned confl oth
        by (cases T) (auto simp: state_wl_l_init_def state_wl_l_def twl_st_l_init_def
            mset_take_mset_drop_mset mset_take_mset_drop_mset' clauses_def MW_def
            added_only_watched_def state_wl_l_init'_def
	    to_init_state0_def init_state0_def
           simp del: all_clss_l_ran_m
           simp: all_clss_lf_ran_m[symmetric])

      have 0: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* ([], ?CS, {#}, None)
	 (MW, ?CS, {#}, None)\<close>
	using n_d count_dec' propa clss_in_clss
      proof (induction MW)
	case Nil
	then show ?case by auto
      next
	case (Cons K MW) note IH = this(1) and H = this(2-) and n_d = this(2) and dec = this(3) and
	  propa = this(4) and clss_in_clss = this(5)
	let ?init = \<open>([], mset `# mset CS, {#}, None)\<close>
	let ?int = \<open>(MW, mset `# mset CS, {#}, None)\<close>
	let ?final = \<open>(K # MW, mset `# mset CS, {#}, None)\<close>
	obtain L C where
	  K: \<open>K = Propagated L C\<close>
	  using dec by (cases K) auto
	  term ?init

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
	moreover have \<open>C \<in># cdcl\<^sub>W_restart_mset.clauses (MW, mset `# mset CS, {#}, None)\<close>
	  using clss_in_clss by (auto simp: K clauses_def split: if_splits)
	ultimately have \<open>cdcl\<^sub>W_restart_mset.propagate ?int
	      (Propagated L C # MW, mset `# mset CS, {#}, None)\<close>
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

      with cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_stgy_cdcl\<^sub>W_restart_stgy[OF 0, of n]
      have stgy: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart_stgy\<^sup>*\<^sup>* (([], mset `# mset CS, {#}, None), n)
            (state\<^sub>W_of Ta, n')\<close>
        using stgy_T_Ta unfolding st_W by simp

      have entailed: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of Ta)\<close>
	apply (rule cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_learned_clauses_entailed)
	   apply (rule cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_restart_stgy_cdcl\<^sub>W_restart[OF stgy, unfolded fst_conv])
	  apply (rule learned')
	 apply (rule M_lev)
	apply (rule ent)
	done

      consider
        (ns) \<open>no_step cdcl_twl_stgy Ta\<close> |
        (stop) \<open>get_conflict Ta \<noteq> None\<close> and \<open>count_decided (get_trail Ta) = 0\<close>
        using final unfolding final_twl_state_def by auto
      then show \<open>\<exists>s'\<in>Collect (conclusive_CDCL_run (mset `# mset CS)
               (init_state (mset `# mset CS))).
           (Ta, s') \<in> {(S, T). T = state\<^sub>W_of S}\<close>
      proof cases
        case ns
        from no_step_cdcl_twl_stgy_no_step_cdcl\<^sub>W_stgy[OF this struct_invs_x]
        have \<open>no_step cdcl\<^sub>W_restart_mset.cdcl\<^sub>W (state\<^sub>W_of Ta)\<close>
	   by (blast dest: cdcl\<^sub>W_ex_cdcl\<^sub>W_stgy)
        then show ?thesis
	  apply -
	  apply (rule bexI[of _ \<open>state\<^sub>W_of Ta\<close>])
          using twl stgy s
          unfolding conclusive_CDCL_run_def
          by auto
      next
        case stop
        have \<open>unsatisfiable (set_mset (init_clss (state\<^sub>W_of Ta)))\<close>
          apply (rule conflict_of_level_unsatisfiable)
             apply (rule all_struct_invs_x)
          using entailed stop by (auto simp: twl_st)
        then have \<open>unsatisfiable (mset ` set CS)\<close>
          using cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_restart_init_clss[symmetric, OF
             cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_restart_stgy_cdcl\<^sub>W_restart[OF stgy]]
          by auto

        then show ?thesis
          using stop
          by (auto simp: twl_st_init twl_st conclusive_CDCL_run_def)
      qed
    qed
    show ?G1
      apply (rule cdcl_twl_stgy_restart_restart_prog_spec[THEN order_trans])
          apply (rule struct_invs; fail)
         apply (rule stgy_invs; fail)
        apply (rule clss_to_upd; fail)
       apply (use confl in fast; fail)
      apply (rule conclusive_le)
      done
    show ?G2
      apply (rule cdcl_twl_stgy_restart_restart_prog_early_spec[THEN order_trans])
          apply (rule struct_invs; fail)
         apply (rule stgy_invs; fail)
        apply (rule clss_to_upd; fail)
       apply (use confl in fast; fail)
      apply (rule conclusive_le)
      done
  qed

  show ?thesis
    unfolding SAT0_def SAT_def
    apply (refine_vcg lhs_step_If)
    subgoal for b T
      by (rule conflict_during_init)
    subgoal by (rule empty_clauses)
    subgoal for b T
      by (rule extract_atms_clss_nempty)
    subgoal for b T
      by (cases T)
        (auto simp: init_state0_def to_init_state0_def init_dt_spec0_def
          extract_atms_clss_alt_def)
    subgoal for b T
      by (cases T)
        (auto simp: init_state0_def to_init_state0_def init_dt_spec0_def
          extract_atms_clss_alt_def)
    subgoal for b T
      by (cases T)
        (auto simp: init_state0_def to_init_state0_def init_dt_spec0_def
          extract_atms_clss_alt_def)
    subgoal for b T
      by (rule cdcl_twl_stgy_restart_prog)
    subgoal for b T
      by (rule conflict_during_init)
    subgoal by (rule empty_clauses)
    subgoal for b T
      by (rule extract_atms_clss_nempty)
    subgoal premises p for b _ _ T
      using p(6-)
      by (cases T)
        (auto simp: init_state0_def to_init_state0_def init_dt_spec0_def
          extract_atms_clss_alt_def)
    subgoal premises p for b _ _ T
      using p(6-)
      by (cases T)
        (auto simp: init_state0_def to_init_state0_def init_dt_spec0_def
          extract_atms_clss_alt_def)
    subgoal premises p for b _ _ T
      using p(6-)
      by (cases T)
        (auto simp: init_state0_def to_init_state0_def init_dt_spec0_def
          extract_atms_clss_alt_def)
    subgoal for b T
      by (rule cdcl_twl_stgy_restart_prog)
    subgoal for b T
      by (rule conflict_during_init)
    subgoal by (rule empty_clauses)
    subgoal for b T
      by (rule extract_atms_clss_nempty)
    subgoal for b T
      by (cases T)
        (auto simp: init_state0_def to_init_state0_def init_dt_spec0_def
          extract_atms_clss_alt_def)
    subgoal for b T
      by (cases T)
        (auto simp: init_state0_def to_init_state0_def init_dt_spec0_def
          extract_atms_clss_alt_def)
    subgoal for b T
      by (cases T)
        (auto simp: init_state0_def to_init_state0_def init_dt_spec0_def
          extract_atms_clss_alt_def)
    subgoal for b T
      by (rule cdcl_twl_stgy_restart_prog_early)
    done
qed

definition  SAT_l :: \<open>nat clause_l list \<Rightarrow> nat twl_st_l nres\<close> where
  \<open>SAT_l CS = do{
    b \<leftarrow> SPEC(\<lambda>_::bool. True);
    if b then do {
        let S = init_state_l;
        T \<leftarrow> init_dt CS (to_init_state_l S);
        let T = fst T;
        if get_conflict_l T \<noteq> None
        then RETURN T
        else if CS = [] then RETURN (fst init_state_l)
        else do {
           ASSERT (extract_atms_clss CS {} \<noteq> {});
	   ASSERT (clauses_to_update_l T = {#});
           ASSERT(mset `# ran_mf (get_clauses_l T) + get_unit_clauses_l T = mset `# mset CS);
           ASSERT(learned_clss_l (get_clauses_l T) = {#});
           cdcl_twl_stgy_restart_prog_l T
        }
    }
    else do {
        let S = init_state_l;
        T \<leftarrow> init_dt CS (to_init_state_l S);
        failed \<leftarrow> SPEC (\<lambda>_ :: bool. True);
        if failed then do {
          T \<leftarrow> init_dt CS (to_init_state_l S);
          let T = fst T;
          if get_conflict_l T \<noteq> None
          then RETURN T
          else if CS = [] then RETURN (fst init_state_l)
          else do {
             ASSERT (extract_atms_clss CS {} \<noteq> {});
             ASSERT (clauses_to_update_l T = {#});
             ASSERT(mset `# ran_mf (get_clauses_l T) + get_unit_clauses_l T = mset `# mset CS);
             ASSERT(learned_clss_l (get_clauses_l T) = {#});
             cdcl_twl_stgy_restart_prog_l T
          }
        } else do {
          let T = fst T;
          if get_conflict_l T \<noteq> None
          then RETURN T
          else if CS = [] then RETURN (fst init_state_l)
          else do {
             ASSERT (extract_atms_clss CS {} \<noteq> {});
             ASSERT (clauses_to_update_l T = {#});
             ASSERT(mset `# ran_mf (get_clauses_l T) + get_unit_clauses_l T = mset `# mset CS);
             ASSERT(learned_clss_l (get_clauses_l T) = {#});
             cdcl_twl_stgy_restart_prog_early_l T
          }
       }
     }
  }\<close>

lemma SAT_l_SAT0:
  assumes dist: \<open>Multiset.Ball (mset `# mset CS) distinct_mset\<close>
  shows \<open>SAT_l CS \<le> \<Down> {(T,T'). (T, T') \<in> twl_st_l None} (SAT0 CS)\<close>
proof -
  have inj: \<open>inj (uminus :: _ literal \<Rightarrow> _)\<close>
    by (auto simp: inj_on_def)
  have [simp]: \<open>{#- lit_of x. x \<in># A#} = {#- lit_of x. x \<in># B#} \<longleftrightarrow>
    {#lit_of x. x \<in># A#} = {#lit_of x. x \<in># B#}\<close> for A B :: \<open>(nat literal, nat literal,
             nat) annotated_lit multiset\<close>
    unfolding multiset.map_comp[unfolded comp_def, symmetric]
    apply (subst inj_image_mset_eq_iff[of uminus])
    apply (rule inj)
    by (auto simp: inj_on_def)[]
  have get_unit_twl_st_l: \<open>(s, x) \<in> twl_st_l_init \<Longrightarrow> get_learned_unit_clauses_l_init s = {#} \<Longrightarrow>
      learned_clss_l (get_clauses_l_init s) = {#} \<Longrightarrow>
    {#mset (fst x). x \<in># ran_m (get_clauses_l_init s)#} +
    get_unit_clauses_l_init s =
    clause `# get_init_clauses_init x + get_unit_init_clauses_init x\<close> for s x
    apply (cases s; cases x)
    apply (auto simp: twl_st_l_init_def mset_take_mset_drop_mset')
    by (metis (mono_tags, lifting) add.right_neutral all_clss_l_ran_m)

  have init_dt_pre: \<open>init_dt_pre CS (to_init_state_l init_state_l)\<close>
    by (rule init_dt_pre_init) (use dist in auto)

  have init_dt_spec0: \<open>init_dt CS (to_init_state_l init_state_l)
       \<le> \<Down>{((T),T'). (T, T') \<in> twl_st_l_init \<and> twl_list_invs (fst T) \<and>
             clauses_to_update_l (fst T) = {#}}
           (SPEC (init_dt_spec0 CS (to_init_state0 init_state0)))\<close>
    apply (rule init_dt_full[THEN order_trans])
    subgoal by (rule init_dt_pre)
    subgoal
      apply (rule RES_refine)
      unfolding init_dt_spec_def Set.mem_Collect_eq init_dt_spec0_def
        to_init_state_l_def init_state_l_def
        to_init_state0_def init_state0_def
      apply normalize_goal+
      apply (rule_tac x=x in bexI)
      subgoal for s x by (auto simp: twl_st_l_init)
      subgoal for s x
        unfolding Set.mem_Collect_eq
        by (simp_all add: twl_st_init twl_st_l_init twl_st_l_init_no_decision_iff get_unit_twl_st_l)
      done
    done
  have init_state0: \<open>(fst init_state_l, fst init_state0) \<in> {(T, T'). (T, T') \<in> twl_st_l None}\<close>
    by (auto simp: twl_st_l_def init_state0_def init_state_l_def)
  show ?thesis
    unfolding SAT_l_def SAT0_def
    apply (refine_vcg init_dt_spec0)
    subgoal by auto
    subgoal by (auto simp: twl_st_l_init twl_st_init)
    subgoal by (auto simp: twl_st_l_init_alt_def)
    subgoal by auto
    subgoal by (rule init_state0)
    subgoal for b ba T Ta
      unfolding all_clss_lf_ran_m[symmetric] image_mset_union to_init_state0_def init_state0_def
      by (cases T; cases Ta)
        (auto simp: twl_st_l_init twl_st_init twl_st_l_init_def mset_take_mset_drop_mset'
          init_dt_spec0_def)
    subgoal for b ba T Ta
      unfolding all_clss_lf_ran_m[symmetric] image_mset_union
      by (cases T; cases Ta) (auto simp: twl_st_l_init twl_st_init twl_st_l_init_def mset_take_mset_drop_mset')
    subgoal for b ba T Ta
      by (cases T; cases Ta) (auto simp: twl_st_l_init twl_st_init twl_st_l_init_def mset_take_mset_drop_mset')
    subgoal for b ba T Ta
      by (rule cdcl_twl_stgy_restart_prog_l_cdcl_twl_stgy_restart_prog[THEN fref_to_Down, of _ \<open>fst Ta\<close>,
           THEN order_trans])
        (auto simp: twl_st_l_init_alt_def mset_take_mset_drop_mset' intro!: conc_fun_R_mono)
    subgoal by (auto simp: twl_st_l_init twl_st_init)
    subgoal by (auto simp: twl_st_l_init twl_st_init)
    subgoal by (auto simp: twl_st_l_init_alt_def)
    subgoal by auto
    subgoal by (rule init_state0)
    subgoal for b ba _ _ _ _ T Ta
      unfolding all_clss_lf_ran_m[symmetric] image_mset_union to_init_state0_def init_state0_def
      by (cases T; cases Ta)
        (auto simp: twl_st_l_init twl_st_init twl_st_l_init_def mset_take_mset_drop_mset'
          init_dt_spec0_def)
    subgoal for b ba _ _ _ _ T Ta
      unfolding all_clss_lf_ran_m[symmetric] image_mset_union
      by (cases T; cases Ta) (auto simp: twl_st_l_init twl_st_init twl_st_l_init_def mset_take_mset_drop_mset')
    subgoal for b ba _ _ _ _ T Ta
      by (cases T; cases Ta) (auto simp: twl_st_l_init twl_st_init twl_st_l_init_def mset_take_mset_drop_mset')
    subgoal for b ba _ _ _ _ T Ta
      by (rule cdcl_twl_stgy_restart_prog_l_cdcl_twl_stgy_restart_prog[THEN fref_to_Down, of _ \<open>fst Ta\<close>,
           THEN order_trans])
        (auto simp: twl_st_l_init_alt_def intro!: conc_fun_R_mono)
    subgoal by (auto simp: twl_st_l_init twl_st_init)
    subgoal by (auto simp: twl_st_l_init_alt_def)
    subgoal by auto
    subgoal by (rule init_state0)
    subgoal by auto
    subgoal for b ba T Ta
      unfolding all_clss_lf_ran_m[symmetric] image_mset_union
      by (cases T; cases Ta) (auto simp: twl_st_l_init twl_st_init twl_st_l_init_def mset_take_mset_drop_mset')
    subgoal for b ba T Ta
      by (cases T; cases Ta) (auto simp: twl_st_l_init twl_st_init twl_st_l_init_def mset_take_mset_drop_mset')
    subgoal for b ba T Ta
      by (rule cdcl_twl_stgy_restart_prog_early_l_cdcl_twl_stgy_restart_prog_early[THEN fref_to_Down, of _ \<open>fst Ta\<close>,
           THEN order_trans])
        (auto simp: twl_st_l_init_alt_def intro!: conc_fun_R_mono)
    done
qed

definition SAT_wl :: \<open>nat clause_l list \<Rightarrow> nat twl_st_wl nres\<close> where
  \<open>SAT_wl CS = do{
    ASSERT(isasat_input_bounded (mset_set (extract_atms_clss CS {})));
    ASSERT(distinct_mset_set (mset ` set CS));
    let \<A>\<^sub>i\<^sub>n' = extract_atms_clss CS {};
    b \<leftarrow> SPEC(\<lambda>_::bool. True);
    if b then do {
        let S = init_state_wl;
        T \<leftarrow> init_dt_wl' CS (to_init_state S);
        T \<leftarrow> rewatch_st (from_init_state T);
        if get_conflict_wl T \<noteq> None
        then RETURN T
        else if CS = [] then RETURN (([], fmempty, None, {#}, {#}, {#}, \<lambda>_. undefined))
        else do {
	  ASSERT (extract_atms_clss CS {} \<noteq> {});
	  ASSERT(isasat_input_bounded_nempty (mset_set \<A>\<^sub>i\<^sub>n'));
	  ASSERT(mset `# ran_mf (get_clauses_wl T) + get_unit_clauses_wl T = mset `# mset CS);
	  ASSERT(learned_clss_l (get_clauses_wl T) = {#});
	  cdcl_twl_stgy_restart_prog_wl_D (finalise_init T)
        }
    }
    else do {
        let S = init_state_wl;
        T \<leftarrow> init_dt_wl' CS (to_init_state S);
        let T = from_init_state T;
        failed \<leftarrow> SPEC (\<lambda>_ :: bool. True);
        if failed then do {
          let S = init_state_wl;
          T \<leftarrow> init_dt_wl' CS (to_init_state S);
          T \<leftarrow> rewatch_st (from_init_state T);
          if get_conflict_wl T \<noteq> None
          then RETURN T
          else if CS = [] then RETURN (([], fmempty, None, {#}, {#}, {#}, \<lambda>_. undefined))
          else do {
            ASSERT (extract_atms_clss CS {} \<noteq> {});
            ASSERT(isasat_input_bounded_nempty (mset_set \<A>\<^sub>i\<^sub>n'));
            ASSERT(mset `# ran_mf (get_clauses_wl T) + get_unit_clauses_wl T = mset `# mset CS);
            ASSERT(learned_clss_l (get_clauses_wl T) = {#});
            cdcl_twl_stgy_restart_prog_wl_D (finalise_init T)
          }
        } else do {
          if get_conflict_wl T \<noteq> None
          then RETURN T
          else if CS = [] then RETURN (([], fmempty, None, {#}, {#}, {#}, \<lambda>_. undefined))
          else do {
            ASSERT (extract_atms_clss CS {} \<noteq> {});
            ASSERT(isasat_input_bounded_nempty (mset_set \<A>\<^sub>i\<^sub>n'));
            ASSERT(mset `# ran_mf (get_clauses_wl T) + get_unit_clauses_wl T = mset `# mset CS);
            ASSERT(learned_clss_l (get_clauses_wl T) = {#});
            T \<leftarrow> rewatch_st (finalise_init T);
            cdcl_twl_stgy_restart_prog_early_wl_D T
          }
        }
     }
  }\<close>


lemma SAT_l_alt_def:
  \<open>SAT_l CS = do{
    \<A> \<leftarrow> RETURN (); \<^cancel>\<open>atoms\<close>
    b \<leftarrow> SPEC(\<lambda>_::bool. True);
    if b then do {
        let S = init_state_l;
        \<A> \<leftarrow> RETURN (); \<^cancel>\<open>initialisation\<close>
        T \<leftarrow> init_dt CS (to_init_state_l S);  \<^cancel>\<open>rewatch\<close>
        let T = fst T;
        if get_conflict_l T \<noteq> None
        then RETURN T
        else if CS = [] then RETURN (fst init_state_l)
        else do {
           ASSERT (extract_atms_clss CS {} \<noteq> {});
	   ASSERT (clauses_to_update_l T = {#});
           ASSERT(mset `# ran_mf (get_clauses_l T) + get_unit_clauses_l T = mset `# mset CS);
           ASSERT(learned_clss_l (get_clauses_l T) = {#});
           cdcl_twl_stgy_restart_prog_l T
        }
    }
    else do {
        let S = init_state_l;
        \<A> \<leftarrow> RETURN (); \<^cancel>\<open>initialisation\<close>
        T \<leftarrow> init_dt CS (to_init_state_l S);
        failed \<leftarrow> SPEC (\<lambda>_ :: bool. True);
        if failed then do {
          let S = init_state_l;
          \<A> \<leftarrow> RETURN (); \<^cancel>\<open>initialisation\<close>
          T \<leftarrow> init_dt CS (to_init_state_l S);
          let T = T;
          if get_conflict_l_init T \<noteq> None
          then RETURN (fst T)
          else if CS = [] then RETURN (fst init_state_l)
          else do {
            ASSERT (extract_atms_clss CS {} \<noteq> {});
            ASSERT (clauses_to_update_l (fst T) = {#});
            ASSERT(mset `# ran_mf (get_clauses_l (fst T)) + get_unit_clauses_l (fst T) = mset `# mset CS);
            ASSERT(learned_clss_l (get_clauses_l (fst T)) = {#});
            let T = fst T;
            cdcl_twl_stgy_restart_prog_l T
          }
        } else do {
          let T = T;
          if get_conflict_l_init T \<noteq> None
          then RETURN (fst T)
          else if CS = [] then RETURN (fst init_state_l)
          else do {
            ASSERT (extract_atms_clss CS {} \<noteq> {});
            ASSERT (clauses_to_update_l (fst T) = {#});
            ASSERT(mset `# ran_mf (get_clauses_l (fst T)) + get_unit_clauses_l (fst T) = mset `# mset CS);
            ASSERT(learned_clss_l (get_clauses_l (fst T)) = {#});
            let T = fst T;
            cdcl_twl_stgy_restart_prog_early_l T
          }
        }
     }
  }\<close>
  unfolding SAT_l_def by (auto cong: if_cong Let_def twl_st_l_init)

lemma init_dt_wl_full_init_dt_wl_spec_full:
  assumes \<open>init_dt_wl_pre CS S\<close> and  \<open>init_dt_pre CS S'\<close> and
    \<open>(S, S') \<in> state_wl_l_init\<close> and \<open>\<forall>C\<in>set CS. distinct C\<close>
  shows \<open>init_dt_wl_full CS S \<le> \<Down> {(S, S'). (fst S, fst S') \<in> state_wl_l None} (init_dt CS S')\<close>
proof -
  have init_dt_wl: \<open>init_dt_wl CS S \<le> SPEC (\<lambda>T. RETURN T \<le> \<Down> state_wl_l_init (init_dt CS S') \<and>
     init_dt_wl_spec CS S T)\<close>
    apply (rule SPEC_rule_conjI)
    apply (rule order_trans)
    apply (rule init_dt_wl_init_dt[of S S'])
    subgoal by (rule assms)
    subgoal by (rule assms)
    apply (rule no_fail_spec_le_RETURN_itself)
    subgoal
      apply (rule SPEC_nofail)
      apply (rule order_trans)
      apply (rule ref_two_step')
      apply (rule init_dt_full)
      using assms by (auto simp: conc_fun_RES init_dt_wl_pre_def)
    subgoal
      apply (rule order_trans)
      apply (rule init_dt_wl_init_dt_wl_spec)
      apply (rule assms)
      apply simp
      done
    done

  show ?thesis
    unfolding init_dt_wl_full_def
    apply (rule specify_left)
    apply (rule init_dt_wl)
    subgoal for x
      apply (cases x, cases \<open>fst x\<close>)
      apply (simp only: prod.case fst_conv)
      apply normalize_goal+
      apply (rule specify_left)
      apply (rule_tac M =aa and N=ba and C=c and NE=d and UE=e and Q=f in
	  rewatch_correctness[OF _ init_dt_wl_spec_rewatch_pre])
      subgoal by rule
      apply (assumption)
      apply (auto)[3]
      apply (cases \<open>init_dt CS S'\<close>)
      apply (auto simp: RETURN_RES_refine_iff state_wl_l_def state_wl_l_init_def
        state_wl_l_init'_def)
      done
    done
qed

lemma init_dt_wl_pre:
  assumes dist: \<open>Multiset.Ball (mset `# mset CS) distinct_mset\<close>
  shows \<open>init_dt_wl_pre CS (to_init_state init_state_wl)\<close>
  unfolding init_dt_wl_pre_def to_init_state_def init_state_wl_def
  apply (rule exI[of _ \<open>(([], fmempty, None, {#}, {#}, {#}, {#}), {#})\<close>])
  apply (intro conjI)
   apply (auto simp: init_dt_pre_def state_wl_l_init_def state_wl_l_init'_def)[]
  unfolding init_dt_pre_def
  apply (rule exI[of _ \<open>(([], {#}, {#}, None, {#}, {#}, {#}, {#}), {#})\<close>])
  using dist by (auto simp: init_dt_pre_def state_wl_l_init_def state_wl_l_init'_def
     twl_st_l_init_def twl_init_invs)[]


lemma SAT_wl_SAT_l:
  assumes
    dist: \<open>Multiset.Ball (mset `# mset CS) distinct_mset\<close> and
    bounded: \<open>isasat_input_bounded (mset_set (\<Union>C\<in>set CS. atm_of ` set C))\<close>
  shows \<open>SAT_wl CS \<le> \<Down> {(T,T'). (T, T') \<in> state_wl_l None} (SAT_l CS)\<close>
proof -
  have extract_atms_clss: \<open>(extract_atms_clss CS {}, ()) \<in> {(x, _). x = extract_atms_clss CS {}}\<close>
    by auto
  have init_dt_wl_pre: \<open>init_dt_wl_pre CS (to_init_state init_state_wl)\<close>
    by (rule init_dt_wl_pre) (use dist in auto)

  have init_rel: \<open>(to_init_state init_state_wl, to_init_state_l init_state_l)
    \<in> state_wl_l_init\<close>
    by (auto simp: init_dt_pre_def state_wl_l_init_def state_wl_l_init'_def
       twl_st_l_init_def twl_init_invs to_init_state_def init_state_wl_def
       init_state_l_def to_init_state_l_def)[]

  \<comment> \<open>The following stlightly strange theorem allows to reuse the definition
    and the correctness of @{term init_dt_wl_heur_full}, which was split in the definition
    for purely refinement-related reasons.\<close>
  define init_dt_wl_rel where
    \<open>init_dt_wl_rel S \<equiv> ({(T, T'). RETURN T \<le> init_dt_wl' CS S \<and> T' = ()})\<close> for S
  have init_dt_wl':
    \<open>init_dt_wl' CS S \<le>  SPEC (\<lambda>c. (c, ()) \<in> (init_dt_wl_rel S))\<close>
    if
      \<open>init_dt_wl_pre CS S\<close> and
      \<open>(S, S') \<in> state_wl_l_init\<close> and
      \<open>\<forall>C\<in>set CS. distinct C\<close>
      for S S'
  proof -
    have [simp]: \<open>(U, U') \<in> ({(T, T'). RETURN T \<le> init_dt_wl' CS S \<and> remove_watched T = T'} O
         state_wl_l_init) \<longleftrightarrow> ((U, U') \<in> {(T, T'). remove_watched T = T'} O
         state_wl_l_init \<and> RETURN U \<le> init_dt_wl' CS S)\<close> for S S' U U'
      by auto
    have H: \<open>A \<le> \<Down> ({(S, S'). P S S'}) B \<longleftrightarrow> A \<le> \<Down> ({(S, S'). RETURN S \<le> A \<and> P S S'}) B\<close>
      for A B P R
      by (simp add: pw_conc_inres pw_conc_nofail pw_le_iff p2rel_def)
    have nofail: \<open>nofail (init_dt_wl' CS S)\<close>
      apply (rule SPEC_nofail)
      apply (rule order_trans)
      apply (rule init_dt_wl'_spec[unfolded conc_fun_RES])
      using that by auto
    have H: \<open>A \<le> \<Down> ({(S, S'). P S S'} O R) B \<longleftrightarrow> A \<le> \<Down> ({(S, S'). RETURN S \<le> A \<and> P S S'} O R) B\<close>
      for A B P R
      by (smt Collect_cong H case_prod_cong conc_fun_chain)
    show ?thesis
      unfolding init_dt_wl_rel_def
      using that
      by (auto simp: nofail no_fail_spec_le_RETURN_itself)
  qed

  have rewatch_st: \<open>rewatch_st (from_init_state T) \<le>
   \<Down> ({(S, S'). (S, fst S') \<in> state_wl_l None \<and> correct_watching S \<and>
         literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st (finalise_init S)) (finalise_init S)})
     (init_dt CS (to_init_state_l init_state_l))\<close>
   (is \<open>_ \<le> \<Down> ?rewatch _\<close>)
  if  \<open>(extract_atms_clss CS {}, \<A>)  \<in> {(x, _). x = extract_atms_clss CS {}}\<close> and
      \<open>(T, Ta) \<in> init_dt_wl_rel (to_init_state init_state_wl)\<close>
    for T Ta and \<A> :: unit
  proof -
    have le_wa: \<open>\<Down> {(T, T'). T = append_empty_watched T'} A =
      (do {S \<leftarrow> A; RETURN (append_empty_watched S)})\<close> for A R
      by (cases A)
        (auto simp: conc_fun_RES RES_RETURN_RES image_iff)
    have init': \<open>init_dt_pre CS (to_init_state_l init_state_l)\<close>
      by (rule init_dt_pre_init) (use assms in auto)
    have H: \<open>do {T \<leftarrow> RETURN T; rewatch_st (from_init_state T)} \<le>
        \<Down>{(S', T'). S' = fst T'} (init_dt_wl_full CS (to_init_state init_state_wl))\<close>
      using that unfolding init_dt_wl_full_def init_dt_wl_rel_def init_dt_wl'_def apply -
      apply (rule bind_refine[of _ \<open>{(T', T''). T' = append_empty_watched T''}\<close>])
      apply (subst le_wa)
      apply (auto simp: rewatch_st_def from_init_state_def intro!: bind_refine[of _ Id])
      done
    have [intro]: \<open>correct_watching_init (af, ag, None, ai, aj, {#}, ba) \<Longrightarrow>
       blits_in_\<L>\<^sub>i\<^sub>n (af, ag, ah, ai, aj, ak, ba)\<close> for af ag ah ai aj ak ba
       by (auto simp: correct_watching_init.simps blits_in_\<L>\<^sub>i\<^sub>n_def
         all_blits_are_in_problem_init.simps all_lits_def
	 in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n in_all_lits_of_mm_ain_atms_of_iff
	 atm_of_all_lits_of_mm)

    have \<open>rewatch_st (from_init_state T)
    \<le> \<Down> {(S, S'). (S, fst S') \<in> state_wl_l None}
       (init_dt CS (to_init_state_l init_state_l))\<close>
     apply (rule H[simplified, THEN order_trans])
     apply (rule order_trans)
     apply (rule ref_two_step')
     apply (rule init_dt_wl_full_init_dt_wl_spec_full)
     subgoal by (rule init_dt_wl_pre)
     apply (rule init')
     subgoal by (auto simp: to_init_state_def init_state_wl_def to_init_state_l_def
       init_state_l_def state_wl_l_init_def state_wl_l_init'_def)
     subgoal using assms by auto
     by (auto intro!: conc_fun_R_mono simp: conc_fun_chain)

    moreover have \<open>rewatch_st (from_init_state T) \<le> SPEC (\<lambda>S. correct_watching S \<and>
         literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st (finalise_init S)) (finalise_init S))\<close>
     apply (rule H[simplified, THEN order_trans])
     apply (rule order_trans)
     apply (rule ref_two_step')
     apply (rule Watched_Literals_Watch_List_Initialisation.init_dt_wl_full_init_dt_wl_spec_full)
     subgoal by (rule init_dt_wl_pre)
     using  is_\<L>\<^sub>a\<^sub>l\<^sub>l_all_atms_st_all_lits_st[of ]
     by (auto simp: conc_fun_RES init_dt_wl_spec_full_def correct_watching_init_correct_watching
       finalise_init_def literals_are_\<L>\<^sub>i\<^sub>n_def)

    ultimately show ?thesis
      by (rule add_invar_refineI_P)
  qed
  have cdcl_twl_stgy_restart_prog_wl_D: \<open>cdcl_twl_stgy_restart_prog_wl_D (finalise_init U)
	\<le> \<Down> {(T, T'). (T, T') \<in> state_wl_l None}
	   (cdcl_twl_stgy_restart_prog_l (fst U'))\<close>
    if
      \<open>(extract_atms_clss CS {}, (\<A>::unit)) \<in> {(x, _). x = extract_atms_clss CS {}}\<close> and
      UU': \<open>(U, U') \<in> ?rewatch\<close> and
      \<open>\<not> get_conflict_wl U \<noteq> None\<close> and
      \<open>\<not> get_conflict_l (fst U') \<noteq> None\<close> and
      \<open>CS \<noteq> []\<close> and
      \<open>CS \<noteq> []\<close> and
      \<open>extract_atms_clss CS {} \<noteq> {}\<close> and
      \<open>clauses_to_update_l (fst U') = {#}\<close> and
      \<open>mset `# ran_mf (get_clauses_l (fst U')) + get_unit_clauses_l (fst U') =
       mset `# mset CS\<close> and
      \<open>learned_clss_l (get_clauses_l (fst U')) = {#}\<close> and
      \<open>extract_atms_clss CS {} \<noteq> {}\<close> and
      \<open>isasat_input_bounded_nempty (mset_set (extract_atms_clss CS {}))\<close> and
      \<open>mset `# ran_mf (get_clauses_wl U) + get_unit_clauses_wl U =
       mset `# mset CS\<close> and
      \<open>learned_clss_l (get_clauses_wl U) = {#}\<close>
    for \<A> T Ta U U'
  proof -
    have 1: \<open> {(T, T'). (T, T') \<in> state_wl_l None} = state_wl_l None\<close>
      by auto
    have lits: \<open>literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st (finalise_init U)) (finalise_init U)\<close>
      using UU' by (auto simp: finalise_init_def)
    show ?thesis
      apply (rule cdcl_twl_stgy_restart_prog_wl_D_spec[OF lits, THEN order_trans])
      apply (subst Down_id_eq, subst 1)
      apply (rule cdcl_twl_stgy_restart_prog_wl_spec[unfolded fref_param1, THEN fref_to_Down])
      apply fast
      using UU' by (auto simp: finalise_init_def)
  qed

  have conflict_during_init:
    \<open>(([], fmempty, None, {#}, {#}, {#}, \<lambda>_. undefined), fst init_state_l)
       \<in> {(T, T'). (T, T') \<in> state_wl_l None}\<close>
    by (auto simp: init_state_l_def state_wl_l_def)

  have init_init_dt: \<open>RETURN (from_init_state T)
	\<le> \<Down>  ({(S, S'). S = fst S'} O {(S :: nat twl_st_wl_init_full, S' :: nat twl_st_wl_init).
      remove_watched S =  S'} O state_wl_l_init)
	    (init_dt CS (to_init_state_l init_state_l))\<close>
      (is \<open>_ \<le> \<Down> ?init_dt _ \<close>)
    if
      \<open>(extract_atms_clss CS {}, (\<A>::unit)) \<in> {(x, _). x = extract_atms_clss CS {}}\<close> and
      \<open>(T, Ta) \<in> init_dt_wl_rel (to_init_state init_state_wl)\<close>
    for \<A> T Ta
  proof -
    have 1: \<open>RETURN T \<le> init_dt_wl' CS (to_init_state init_state_wl)\<close>
      using that by (auto simp: init_dt_wl_rel_def from_init_state_def)
    have 2: \<open>RETURN (from_init_state T) \<le> \<Down> {(S, S'). S = fst S'} (RETURN T)\<close>
      by (auto simp: RETURN_refine from_init_state_def)
    have 2: \<open>RETURN (from_init_state T) \<le> \<Down> {(S, S'). S = fst S'} (init_dt_wl' CS (to_init_state init_state_wl))\<close>
      apply (rule 2[THEN order_trans])
      apply (rule ref_two_step')
      apply (rule 1)
      done
    show ?thesis
      apply (rule order_trans)
      apply (rule 2)
      unfolding conc_fun_chain[symmetric]
      apply (rule ref_two_step')
      unfolding conc_fun_chain
      apply (rule init_dt_wl'_init_dt)
      apply (rule init_dt_wl_pre)
      subgoal by (auto simp: to_init_state_def init_state_wl_def to_init_state_l_def
       init_state_l_def state_wl_l_init_def state_wl_l_init'_def)
      subgoal using assms by auto
      done
  qed

  have rewatch_st_fst: \<open>rewatch_st (finalise_init (from_init_state T))
	\<le> SPEC (\<lambda>c. (c, fst Ta) \<in> {(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S})\<close>
      (is \<open>_ \<le> SPEC ?rewatch\<close>)
    if

      \<open>(extract_atms_clss CS {}, \<A>) \<in> {(x, _). x = extract_atms_clss CS {}}\<close> and
      T: \<open>(T, \<A>') \<in> init_dt_wl_rel (to_init_state init_state_wl)\<close> and
      T_Ta: \<open>(from_init_state T, Ta)
       \<in> {(S, S'). S = fst S'} O
	 {(S, S'). remove_watched S = S'} O state_wl_l_init\<close> and
      \<open>\<not> get_conflict_wl (from_init_state T) \<noteq> None\<close> and
      \<open>\<not> get_conflict_l_init Ta \<noteq> None\<close>
    for \<A> b ba T \<A>' Ta bb bc
  proof -
    have 1: \<open>RETURN T \<le> init_dt_wl' CS (to_init_state init_state_wl)\<close>
      using T unfolding init_dt_wl_rel_def by auto
    have 2: \<open>RETURN T \<le> \<Down> {(S, S'). remove_watched S = S'}
     (SPEC (init_dt_wl_spec CS (to_init_state init_state_wl)))\<close>
      using order_trans[OF 1 init_dt_wl'_spec[OF init_dt_wl_pre]] .

    have empty_watched: \<open>get_watched_wl (finalise_init (from_init_state T)) = (\<lambda>_. [])\<close>
      using 1 2 init_dt_wl'_spec[OF init_dt_wl_pre]
      by (cases T; cases \<open>init_dt_wl CS (init_state_wl, {#})\<close>)
       (auto simp: init_dt_wl_spec_def RETURN_RES_refine_iff
        finalise_init_def from_init_state_def state_wl_l_init_def
	state_wl_l_init'_def to_init_state_def to_init_state_l_def
       init_state_l_def init_dt_wl'_def RES_RETURN_RES)

    have 1: \<open>length (aa  \<propto> x) \<ge> 2\<close> \<open>distinct (aa  \<propto> x)\<close>
      if
        struct: \<open>twl_struct_invs_init
          ((af,
          {#TWL_Clause (mset (watched_l (fst x))) (mset (unwatched_l (fst x)))
          . x \<in># init_clss_l aa#},
          {#}, y, ac, {#}, {#}, ae),
         OC)\<close> and
	x: \<open>x \<in># dom_m aa\<close> and
	learned: \<open>learned_clss_l aa = {#}\<close>
	for af aa y ac ae x OC
    proof -
      have irred: \<open>irred aa x\<close>
        using that by (cases \<open>fmlookup aa x\<close>) (auto simp: ran_m_def dest!: multi_member_split
	  split: if_splits)
      have \<open>Multiset.Ball
	({#TWL_Clause (mset (watched_l (fst x))) (mset (unwatched_l (fst x)))
	 . x \<in># init_clss_l aa#} +
	 {#})
	struct_wf_twl_cls\<close>
	using struct unfolding twl_struct_invs_init_def fst_conv twl_st_inv.simps
	by fast
      then show \<open>length (aa  \<propto> x) \<ge> 2\<close> \<open>distinct (aa  \<propto> x)\<close>
        using x learned in_ran_mf_clause_inI[OF x, of True] irred
	by (auto simp: mset_take_mset_drop_mset' dest!: multi_member_split[of x]
	  split: if_splits)
    qed
    have min_len: \<open> x \<in># dom_m (get_clauses_wl (finalise_init (from_init_state T))) \<Longrightarrow>
      distinct (get_clauses_wl (finalise_init (from_init_state T)) \<propto> x) \<and>
      2 \<le> length (get_clauses_wl (finalise_init (from_init_state T)) \<propto> x)\<close>
      for x
      using 2
      by (cases T)
       (auto simp: init_dt_wl_spec_def RETURN_RES_refine_iff
        finalise_init_def from_init_state_def state_wl_l_init_def
	state_wl_l_init'_def to_init_state_def to_init_state_l_def
       init_state_l_def init_dt_wl'_def RES_RETURN_RES
       init_dt_spec_def init_state_wl_def twl_st_l_init_def
       intro: 1)

    show ?thesis
      apply (rule rewatch_st_correctness[THEN order_trans])
      subgoal by (rule empty_watched)
      subgoal by (rule min_len)
      subgoal using T_Ta by (auto simp: finalise_init_def
         state_wl_l_init_def state_wl_l_init'_def state_wl_l_def
	 correct_watching_init_correct_watching
	 correct_watching_init_blits_in_\<L>\<^sub>i\<^sub>n)
      done
  qed

  have cdcl_twl_stgy_restart_prog_wl_D2: \<open>cdcl_twl_stgy_restart_prog_wl_D U'
	\<le> \<Down> {(T, T'). (T, T') \<in> state_wl_l None}
	   (cdcl_twl_stgy_restart_prog_l (fst T'))\<close> (is ?A) and
     cdcl_twl_stgy_restart_prog_early_wl_D2: \<open>cdcl_twl_stgy_restart_prog_early_wl_D U'
      \<le> \<Down> {(T, T'). (T, T') \<in> state_wl_l None}
         (cdcl_twl_stgy_restart_prog_early_l (fst T'))\<close> (is ?B)

    if
      U': \<open>(U', fst T') \<in> {(S, T). (S, T) \<in> state_wl_l None \<and> correct_watching S \<and> blits_in_\<L>\<^sub>i\<^sub>n S}\<close>
      for \<A> b b' T \<A>' T' c c' U'
  proof -
    have 1: \<open> {(T, T'). (T, T') \<in> state_wl_l None} = state_wl_l None\<close>
      by auto
    have lits: \<open>literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st (U')) (U')\<close>
      apply (rule literals_are_\<L>\<^sub>i\<^sub>n_all_atms_st)
      using U' by (auto simp: finalise_init_def correct_watching.simps)
    show ?A
      apply (rule cdcl_twl_stgy_restart_prog_wl_D_spec[OF lits, THEN order_trans])
      apply (subst Down_id_eq, subst 1)
      apply (rule cdcl_twl_stgy_restart_prog_wl_spec[unfolded fref_param1, THEN fref_to_Down])
      apply fast
      using U' by (auto simp: finalise_init_def)
    show ?B
      apply (rule cdcl_twl_stgy_restart_prog_early_wl_D_spec[OF lits, THEN order_trans])
      apply (subst Down_id_eq, subst 1)
      apply (rule cdcl_twl_stgy_restart_prog_early_wl_spec[unfolded fref_param1, THEN fref_to_Down])
      apply fast
      using U' by (auto simp: finalise_init_def)
  qed
  have all_le: \<open>\<forall>C\<in>set CS. \<forall>L\<in>set C. nat_of_lit L \<le> uint_max\<close>
  proof (intro ballI)
    fix C L
    assume \<open>C \<in> set CS\<close> and \<open>L \<in> set C\<close>
    then have \<open>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (mset_set (\<Union>C\<in>set CS. atm_of ` set C))\<close>
      by (auto simp: in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n)
    then show \<open>nat_of_lit L \<le> uint_max\<close>
      using assms by auto
  qed
  have [simp]: \<open>(Tc, fst Td) \<in> state_wl_l None \<Longrightarrow>
       get_conflict_l_init Td = get_conflict_wl Tc\<close> for Tc Td
   by (cases Tc; cases Td; auto simp: state_wl_l_def)
  show ?thesis
    unfolding SAT_wl_def SAT_l_alt_def
    apply (refine_vcg extract_atms_clss init_dt_wl' init_rel)
    subgoal using assms unfolding extract_atms_clss_alt_def by auto
    subgoal using assms unfolding distinct_mset_set_def by auto
    subgoal by auto
    subgoal by (rule init_dt_wl_pre)
    subgoal using dist by auto
    apply (rule rewatch_st; assumption)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (rule conflict_during_init)
    subgoal using bounded by (auto simp: isasat_input_bounded_nempty_def extract_atms_clss_alt_def
      simp del: isasat_input_bounded_def)
    subgoal by auto
    subgoal by auto
    subgoal for \<A> b ba T Ta U U'
      by (rule cdcl_twl_stgy_restart_prog_wl_D)
    subgoal by (rule init_dt_wl_pre)
    subgoal using dist by auto
    apply (rule init_init_dt; assumption)
    subgoal by auto
    subgoal by (rule init_dt_wl_pre)
    subgoal using dist by auto
    apply (rule rewatch_st; assumption)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (rule conflict_during_init)
    subgoal using bounded by (auto simp: isasat_input_bounded_nempty_def extract_atms_clss_alt_def
      simp del: isasat_input_bounded_def)
    subgoal by auto
    subgoal by auto
    subgoal for \<A> b ba T Ta U U'
      unfolding twl_st_l_init[symmetric]
      by (rule cdcl_twl_stgy_restart_prog_wl_D)
    subgoal by (auto simp: from_init_state_def state_wl_l_init_def state_wl_l_init'_def)
    subgoal for \<A> b ba T Ta U U'
      by (cases U'; cases U)
        (auto simp: from_init_state_def state_wl_l_init_def state_wl_l_init'_def
           state_wl_l_def)
    subgoal by (auto simp: from_init_state_def state_wl_l_init_def state_wl_l_init'_def)
    subgoal by (rule conflict_during_init)

    subgoal using bounded by (auto simp: isasat_input_bounded_nempty_def extract_atms_clss_alt_def
      simp del: isasat_input_bounded_def)
    subgoal for \<A> b ba U \<A>' T' bb bc
      by (cases U; cases T')
        (auto simp: state_wl_l_init_def state_wl_l_init'_def)
    subgoal for \<A> b ba T \<A>' T' bb bc
      by (auto simp: state_wl_l_init_def state_wl_l_init'_def)
    apply (rule rewatch_st_fst; assumption)
    subgoal by (rule cdcl_twl_stgy_restart_prog_early_wl_D2)
    done
qed

definition extract_model_of_state where
  \<open>extract_model_of_state U = Some (map lit_of (get_trail_wl U))\<close>

definition extract_model_of_state_heur where
  \<open>extract_model_of_state_heur U = Some (fst (get_trail_wl_heur U))\<close>

definition extract_stats where
  [simp]: \<open>extract_stats U = None\<close>

definition extract_stats_init where
  [simp]: \<open>extract_stats_init = None\<close>

definition IsaSAT :: \<open>nat clause_l list \<Rightarrow> nat literal list option nres\<close> where
  \<open>IsaSAT CS = do{
    S \<leftarrow> SAT_wl CS;
    RETURN (if get_conflict_wl S = None then extract_model_of_state S else extract_stats S)
  }\<close>


lemma IsaSAT_alt_def:
  \<open>IsaSAT CS = do{
    ASSERT(isasat_input_bounded (mset_set (extract_atms_clss CS {})));
    ASSERT(distinct_mset_set (mset ` set CS));
    let \<A>\<^sub>i\<^sub>n' = extract_atms_clss CS {};
    _ \<leftarrow> RETURN ();
    b \<leftarrow> SPEC(\<lambda>_::bool. True);
    if b then do {
        let S = init_state_wl;
        T \<leftarrow> init_dt_wl' CS (to_init_state S);
        T \<leftarrow> rewatch_st (from_init_state T);
        if get_conflict_wl T \<noteq> None
        then RETURN (extract_stats T)
        else if CS = [] then RETURN (Some [])
        else do {
           ASSERT (extract_atms_clss CS {} \<noteq> {});
           ASSERT(isasat_input_bounded_nempty (mset_set \<A>\<^sub>i\<^sub>n'));
           ASSERT(mset `# ran_mf (get_clauses_wl T) + get_unit_clauses_wl T = mset `# mset CS);
           ASSERT(learned_clss_l (get_clauses_wl T) = {#});
	   T \<leftarrow> RETURN (finalise_init T);
           S \<leftarrow> cdcl_twl_stgy_restart_prog_wl_D (T);
           RETURN (if get_conflict_wl S = None then extract_model_of_state S else extract_stats S)
        }
    }
    else do {
        let S = init_state_wl;
        T \<leftarrow> init_dt_wl' CS (to_init_state S);
        failed \<leftarrow> SPEC (\<lambda>_ :: bool. True);
        if failed then do {
          let S = init_state_wl;
          T \<leftarrow> init_dt_wl' CS (to_init_state S);
          T \<leftarrow> rewatch_st (from_init_state T);
          if get_conflict_wl T \<noteq> None
          then RETURN (extract_stats T)
          else if CS = [] then RETURN (Some [])
          else do {
            ASSERT (extract_atms_clss CS {} \<noteq> {});
            ASSERT(isasat_input_bounded_nempty (mset_set \<A>\<^sub>i\<^sub>n'));
            ASSERT(mset `# ran_mf (get_clauses_wl T) + get_unit_clauses_wl T = mset `# mset CS);
            ASSERT(learned_clss_l (get_clauses_wl T) = {#});
            let T = finalise_init T;
            S \<leftarrow> cdcl_twl_stgy_restart_prog_wl_D T;
            RETURN (if get_conflict_wl S = None then extract_model_of_state S else extract_stats S)
          }
        } else do {
          let T = from_init_state T;
          if get_conflict_wl T \<noteq> None
          then RETURN (extract_stats T)
          else if CS = [] then RETURN (Some [])
          else do {
            ASSERT (extract_atms_clss CS {} \<noteq> {});
            ASSERT(isasat_input_bounded_nempty (mset_set \<A>\<^sub>i\<^sub>n'));
            ASSERT(mset `# ran_mf (get_clauses_wl T) + get_unit_clauses_wl T = mset `# mset CS);
            ASSERT(learned_clss_l (get_clauses_wl T) = {#});
            T \<leftarrow> rewatch_st T;
	    T \<leftarrow> RETURN (finalise_init T);
            S \<leftarrow> cdcl_twl_stgy_restart_prog_early_wl_D T;
            RETURN (if get_conflict_wl S = None then extract_model_of_state S else extract_stats S)
          }
        }
     }
  }\<close>  (is \<open>?A = ?B\<close>) for CS opts
proof -
  have H: \<open>A = B \<Longrightarrow> A \<le> \<Down> Id B\<close> for A B
    by auto
  have 1: \<open>?A \<le> \<Down> Id ?B\<close>
    unfolding IsaSAT_def SAT_wl_def nres_bind_let_law If_bind_distrib nres_monad_laws
      Let_def finalise_init_def
    apply (refine_vcg)
    subgoal by auto
    apply (rule H; solves auto)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: extract_model_of_state_def)
    subgoal by auto
    subgoal by auto
    apply (rule H; solves auto)
    subgoal by auto
    subgoal by auto
    apply (rule H; solves auto)
    subgoal by auto

    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: extract_model_of_state_def)
    subgoal by auto
    subgoal by auto
    apply (rule H; solves auto)
    subgoal by (auto simp: extract_model_of_state_def)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: extract_model_of_state_def)
    subgoal by auto
    subgoal by auto
    apply (rule H; solves auto)
    apply (rule H; solves auto)
    subgoal by auto
    done

  have 2: \<open>?B \<le> \<Down> Id ?A\<close>
    unfolding IsaSAT_def SAT_wl_def nres_bind_let_law If_bind_distrib nres_monad_laws
      Let_def finalise_init_def
    apply (refine_vcg)
    subgoal by auto
    apply (rule H; solves auto)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: extract_model_of_state_def)
    subgoal by auto
    subgoal by auto
    apply (rule H; solves auto)
    subgoal by auto
    subgoal by auto
    apply (rule H; solves auto)
    subgoal by auto

    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: extract_model_of_state_def)
    subgoal by auto
    subgoal by auto
    apply (rule H; solves auto)
    subgoal by (auto simp: extract_model_of_state_def)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: extract_model_of_state_def)
    subgoal by auto
    subgoal by auto
    apply (rule H; solves auto)
    apply (rule H; solves auto)
    subgoal by auto
    done

  show ?thesis
    using 1 2 by simp
qed

definition extract_model_of_state_stat :: \<open>twl_st_wl_heur \<Rightarrow> nat literal list option \<times> stats\<close> where
  \<open>extract_model_of_state_stat U =
     (Some (fst (get_trail_wl_heur U)),
       (\<lambda>(M, _,  _, _, _ ,_ ,_ ,_, _, _, _, stat, _, _). stat) U)\<close>

definition extract_state_stat :: \<open>twl_st_wl_heur \<Rightarrow> nat literal list option \<times> stats\<close> where
  \<open>extract_state_stat U =
     (None,
       (\<lambda>(M, _, _, _, _ ,_ ,_ ,_, _, _, _, stat, _, _). stat) U)\<close>

definition empty_conflict :: \<open>nat literal list option\<close> where
  \<open>empty_conflict = Some []\<close>

definition empty_conflict_code :: \<open>(_ list option \<times> stats) nres\<close> where
  \<open>empty_conflict_code = do{
     let M0 = [];
     let M1 = Some M0;
     RETURN (M1, (zero_uint64, zero_uint64, zero_uint64, zero_uint64, zero_uint64, zero_uint64, zero_uint64,
        zero_uint64))}\<close>

definition empty_init_code :: \<open>_ list option \<times> stats\<close> where
  \<open>empty_init_code = (None, (zero_uint64, zero_uint64, zero_uint64, zero_uint64,
    zero_uint64, zero_uint64, zero_uint64, zero_uint64))\<close>


definition convert_state where
  \<open>convert_state _ S = S\<close>

definition IsaSAT_use_fast_mode where
  \<open>IsaSAT_use_fast_mode = True\<close>


definition isasat_fast_init :: \<open>twl_st_wl_heur_init \<Rightarrow> bool\<close> where
  \<open>isasat_fast_init S \<longleftrightarrow> (length (get_clauses_wl_heur_init S) \<le> uint64_max - (uint32_max div 2 + 6))\<close>

definition IsaSAT_heur :: \<open>opts \<Rightarrow> nat clause_l list \<Rightarrow> (nat literal list option \<times> stats) nres\<close> where
  \<open>IsaSAT_heur opts CS = do{
    ASSERT(isasat_input_bounded (mset_set (extract_atms_clss CS {})));
    ASSERT(\<forall>C\<in>set CS. \<forall>L\<in>set C. nat_of_lit L \<le> uint_max);
    let \<A>\<^sub>i\<^sub>n' = mset_set (extract_atms_clss CS {});
    ASSERT(isasat_input_bounded \<A>\<^sub>i\<^sub>n');
    ASSERT(distinct_mset \<A>\<^sub>i\<^sub>n');
    let \<A>\<^sub>i\<^sub>n'' = virtual_copy \<A>\<^sub>i\<^sub>n';
    let b = opts_unbounded_mode opts;
    if b
    then do {
        S \<leftarrow> init_state_wl_heur \<A>\<^sub>i\<^sub>n';
        (T::twl_st_wl_heur_init) \<leftarrow>  init_dt_wl_heur True CS S;
	      T \<leftarrow> isasat_init_fast_slow T;
	      T \<leftarrow> rewatch_heur_st T;
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
           U \<leftarrow> cdcl_twl_stgy_restart_prog_wl_heur T;
           RETURN (if get_conflict_wl_is_None_heur U then extract_model_of_state_stat U
             else extract_state_stat U)
         }
    }
    else do {
        S \<leftarrow> init_state_wl_heur \<A>\<^sub>i\<^sub>n';
        (T::twl_st_wl_heur_init) \<leftarrow> init_dt_wl_heur False CS S;
        let failed = is_failed_heur_init T \<or> \<not>isasat_fast_init T;
        if failed then do {
           S \<leftarrow> init_state_wl_heur \<A>\<^sub>i\<^sub>n';
          (T::twl_st_wl_heur_init) \<leftarrow> init_dt_wl_heur True CS S;
          let T = convert_state \<A>\<^sub>i\<^sub>n'' T;
          T \<leftarrow> rewatch_heur_st T;
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
           U \<leftarrow> cdcl_twl_stgy_restart_prog_wl_heur T;
           RETURN (if get_conflict_wl_is_None_heur U then extract_model_of_state_stat U
             else extract_state_stat U)
         }
        }
        else do {
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
             ASSERT(rewatch_heur_st_fast_pre T);
             T \<leftarrow> rewatch_heur_st_fast T;
             ASSERT(isasat_fast_init T);
             T \<leftarrow> finalise_init_code opts (T::twl_st_wl_heur_init);
             ASSERT(isasat_fast T);
             U \<leftarrow> cdcl_twl_stgy_restart_prog_early_wl_heur T;
             RETURN (if get_conflict_wl_is_None_heur U then extract_model_of_state_stat U
               else extract_state_stat U)
           }
        }
      }
    }\<close>

lemma fref_to_Down_unRET_uncurry0_SPEC:
  assumes \<open>(\<lambda>_. (f), \<lambda>_. (RETURN g)) \<in> [P]\<^sub>f unit_rel \<rightarrow> \<langle>B\<rangle>nres_rel\<close> and \<open>P ()\<close>
  shows \<open>f \<le> SPEC (\<lambda>c. (c, g) \<in> B)\<close>
proof -
  have [simp]: \<open>RES (B\<inverse> `` {g}) = SPEC (\<lambda>c. (c, g) \<in> B)\<close>
    by auto
  show ?thesis
    using assms
    unfolding fref_def uncurry_def nres_rel_def RETURN_def
    by (auto simp: conc_fun_RES Image_iff)
qed

lemma fref_to_Down_unRET_SPEC:
  assumes \<open>(f, RETURN o g) \<in> [P]\<^sub>f A \<rightarrow> \<langle>B\<rangle>nres_rel\<close> and
    \<open>P y\<close> and
    \<open>(x, y) \<in> A\<close>
  shows \<open>f x \<le> SPEC (\<lambda>c. (c, g y) \<in> B)\<close>
proof -
  have [simp]: \<open>RES (B\<inverse> `` {g}) = SPEC (\<lambda>c. (c, g) \<in> B)\<close> for g
    by auto
  show ?thesis
    using assms
    unfolding fref_def uncurry_def nres_rel_def RETURN_def
    by (auto simp: conc_fun_RES Image_iff)
qed

lemma fref_to_Down_unRET_curry_SPEC:
  assumes \<open>(uncurry f, uncurry (RETURN oo g)) \<in> [P]\<^sub>f A \<rightarrow> \<langle>B\<rangle>nres_rel\<close> and
    \<open>P (x, y)\<close> and
    \<open>((x', y'), (x, y)) \<in> A\<close>
  shows \<open>f x' y' \<le> SPEC (\<lambda>c. (c, g x y) \<in> B)\<close>
proof -
  have [simp]: \<open>RES (B\<inverse> `` {g}) = SPEC (\<lambda>c. (c, g) \<in> B)\<close> for g
    by auto
  show ?thesis
    using assms
    unfolding fref_def uncurry_def nres_rel_def RETURN_def
    by (auto simp: conc_fun_RES Image_iff)
qed

lemma all_lits_of_mm_empty_iff: \<open>all_lits_of_mm A = {#} \<longleftrightarrow> (\<forall>C \<in># A. C = {#})\<close>
  apply (induction A)
  subgoal by auto
  subgoal by (auto simp: all_lits_of_mm_add_mset)
  done

lemma all_lits_of_mm_extract_atms_clss:
  \<open>L \<in># (all_lits_of_mm (mset `# mset CS)) \<longleftrightarrow> atm_of L \<in> extract_atms_clss CS {}\<close>
  by (induction CS)
    (auto simp: extract_atms_clss_alt_def all_lits_of_mm_add_mset
    in_all_lits_of_m_ain_atms_of_iff)

 
lemma IsaSAT_heur_alt_def:
  \<open>IsaSAT_heur opts CS = do{
    ASSERT(isasat_input_bounded (mset_set (extract_atms_clss CS {})));
    ASSERT(\<forall>C\<in>set CS. \<forall>L\<in>set C. nat_of_lit L \<le> uint_max);
    let \<A>\<^sub>i\<^sub>n' = mset_set (extract_atms_clss CS {});
    ASSERT(isasat_input_bounded \<A>\<^sub>i\<^sub>n');
    ASSERT(distinct_mset \<A>\<^sub>i\<^sub>n');
    let \<A>\<^sub>i\<^sub>n'' = virtual_copy \<A>\<^sub>i\<^sub>n';
    let b = opts_unbounded_mode opts;
    if b
    then do {
        S \<leftarrow> init_state_wl_heur \<A>\<^sub>i\<^sub>n';
        (T::twl_st_wl_heur_init) \<leftarrow>  init_dt_wl_heur True CS S;
        T \<leftarrow> rewatch_heur_st T;
        let T = convert_state \<A>\<^sub>i\<^sub>n'' T;
        if \<not>get_conflict_wl_is_None_heur_init T
        then RETURN (empty_init_code)
        else if CS = [] then empty_conflict_code
        else do {
           ASSERT(\<A>\<^sub>i\<^sub>n'' \<noteq> {#});
           ASSERT(isasat_input_bounded_nempty \<A>\<^sub>i\<^sub>n'');
           ASSERT((\<lambda>(M', N', D', Q', W', ((ns, m, fst_As, lst_As, next_search), to_remove), \<phi>, clvls). fst_As \<noteq> None \<and>
             lst_As \<noteq> None) T);
           T \<leftarrow> finalise_init_code opts (T::twl_st_wl_heur_init);
           U \<leftarrow> cdcl_twl_stgy_restart_prog_wl_heur T;
           RETURN (if get_conflict_wl_is_None_heur U then extract_model_of_state_stat U
             else extract_state_stat U)
         }
    }
    else do {
        S \<leftarrow> init_state_wl_heur \<A>\<^sub>i\<^sub>n';
        (T::twl_st_wl_heur_init) \<leftarrow> init_dt_wl_heur False CS S;
        failed \<leftarrow> RETURN (is_failed_heur_init T \<or> \<not>isasat_fast_init T);
        if failed then do {
           S \<leftarrow> init_state_wl_heur \<A>\<^sub>i\<^sub>n';
          (T::twl_st_wl_heur_init) \<leftarrow> init_dt_wl_heur True CS S;
          T \<leftarrow> rewatch_heur_st T;
          let T = convert_state \<A>\<^sub>i\<^sub>n'' T;
          if \<not>get_conflict_wl_is_None_heur_init T
          then RETURN (empty_init_code)
          else if CS = [] then empty_conflict_code
          else do {
           ASSERT(\<A>\<^sub>i\<^sub>n'' \<noteq> {#});
           ASSERT(isasat_input_bounded_nempty \<A>\<^sub>i\<^sub>n'');
           ASSERT((\<lambda>(M', N', D', Q', W', ((ns, m, fst_As, lst_As, next_search), to_remove), \<phi>, clvls). fst_As \<noteq> None \<and>
             lst_As \<noteq> None) T);
           T \<leftarrow> finalise_init_code opts (T::twl_st_wl_heur_init);
           U \<leftarrow> cdcl_twl_stgy_restart_prog_wl_heur T;
           RETURN (if get_conflict_wl_is_None_heur U then extract_model_of_state_stat U
             else extract_state_stat U)
         }
        }
        else do {
          let T = convert_state \<A>\<^sub>i\<^sub>n'' T;
          if \<not>get_conflict_wl_is_None_heur_init T
          then RETURN (empty_init_code)
          else if CS = [] then empty_conflict_code
          else do {
             ASSERT(\<A>\<^sub>i\<^sub>n'' \<noteq> {#});
             ASSERT(isasat_input_bounded_nempty \<A>\<^sub>i\<^sub>n'');
             ASSERT((\<lambda>(M', N', D', Q', W', ((ns, m, fst_As, lst_As, next_search), to_remove), \<phi>, clvls). fst_As \<noteq> None \<and>
               lst_As \<noteq> None) T);
             ASSERT(rewatch_heur_st_fast_pre T);
             T \<leftarrow> rewatch_heur_st_fast T;
             ASSERT(isasat_fast_init T);
             T \<leftarrow> finalise_init_code opts (T::twl_st_wl_heur_init);
             ASSERT(isasat_fast T);
             U \<leftarrow> cdcl_twl_stgy_restart_prog_early_wl_heur T;
             RETURN (if get_conflict_wl_is_None_heur U then extract_model_of_state_stat U
               else extract_state_stat U)
           }
        }
      }
    }\<close>
  by (auto simp: IsaSAT_heur_def isasat_init_fast_slow_alt_def convert_state_def isasat_information_banner_def cong: if_cong)


lemma rewatch_heur_st_rewatch_st:
  assumes
    UV: \<open>(U, V)
     \<in> twl_st_heur_parsing_no_WL (mset_set (extract_atms_clss CS {})) True O
       {(S, T). S = remove_watched T \<and> get_watched_wl (fst T) = (\<lambda>_. [])}\<close>
  shows \<open>rewatch_heur_st U \<le>
    \<Down>({(S,T). (S, T) \<in> twl_st_heur_parsing (mset_set (extract_atms_clss CS {})) True \<and>
         get_clauses_wl_heur_init S = get_clauses_wl_heur_init U \<and>
	 get_conflict_wl_heur_init S = get_conflict_wl_heur_init U \<and>
         get_clauses_wl (fst T) = get_clauses_wl (fst V) \<and>
	 get_conflict_wl (fst T) = get_conflict_wl (fst V) \<and>
	 get_unit_clauses_wl (fst T) = get_unit_clauses_wl (fst V)} O {(S, T). S = (T, {#})})
           (rewatch_st (from_init_state V))\<close>
proof -
  let ?\<A> = \<open>(mset_set (extract_atms_clss CS {}))\<close>
  obtain M' arena D' j W' vm \<phi> clvls cach lbd vdom M N D NE UE Q W OC failed where
    U: \<open>U = ((M', arena, D', j, W', vm, \<phi>, clvls, cach, lbd, vdom, failed))\<close> and
    V: \<open>V = ((M, N, D, NE, UE, Q, W), OC)\<close>
    by (cases U; cases V) auto
  have valid: \<open>valid_arena arena N (set vdom)\<close> and
    dist: \<open>distinct vdom\<close> and
    vdom_N: \<open>mset vdom = dom_m N\<close> and
    watched: \<open>(W', W) \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 ?\<A>)\<close> and
    lall: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_mm ?\<A> (mset `# ran_mf N)\<close> and
    vdom: \<open>vdom_m ?\<A> W N \<subseteq> set_mset (dom_m N)\<close>
    using UV by (auto simp: twl_st_heur_parsing_no_WL_def U V distinct_mset_dom
      empty_watched_def vdom_m_def literals_are_in_\<L>\<^sub>i\<^sub>n_mm_def
      all_lits_of_mm_union
      simp flip: distinct_mset_mset_distinct)

  show ?thesis
    using UV
    unfolding rewatch_heur_st_def rewatch_st_def
    apply (simp only: prod.simps from_init_state_def fst_conv nres_monad1 U V)
    apply refine_vcg
    apply (rule rewatch_heur_rewatch[OF valid _ dist _ watched lall])
    subgoal by simp
    subgoal using vdom_N[symmetric] by simp
    subgoal by (auto simp: vdom_m_def)
    subgoal by (auto simp: U V twl_st_heur_parsing_def Collect_eq_comp'
      twl_st_heur_parsing_no_WL_def)
    done
qed

lemma rewatch_heur_st_rewatch_st2:
  assumes
    T: \<open>(U, V)
     \<in> twl_st_heur_parsing_no_WL (mset_set (extract_atms_clss CS {})) True O
       {(S, T). S = remove_watched T \<and> get_watched_wl (fst T) = (\<lambda>_. [])}\<close>
  shows \<open>rewatch_heur_st_fast
          (convert_state (virtual_copy (mset_set (extract_atms_clss CS {}))) U)
         \<le> \<Down> ({(S,T). (S, T) \<in> twl_st_heur_parsing (mset_set (extract_atms_clss CS {})) True \<and>
         get_clauses_wl_heur_init S = get_clauses_wl_heur_init U \<and>
	 get_conflict_wl_heur_init S = get_conflict_wl_heur_init U \<and>
         get_clauses_wl (fst T) = get_clauses_wl (fst V) \<and>
	 get_conflict_wl (fst T) = get_conflict_wl (fst V) \<and>
	 get_unit_clauses_wl (fst T) = get_unit_clauses_wl (fst V)} O {(S, T). S = (T, {#})})
            (rewatch_st (from_init_state V))\<close>
proof -
  have
    UV: \<open>(U, V)
     \<in> twl_st_heur_parsing_no_WL (mset_set (extract_atms_clss CS {})) True O
       {(S, T). S = remove_watched T \<and> get_watched_wl (fst T) = (\<lambda>_. [])}\<close>
    using T by (auto simp: twl_st_heur_parsing_no_WL_def)
  then show ?thesis
    unfolding convert_state_def finalise_init_def id_def rewatch_heur_st_fast_def
    by (rule rewatch_heur_st_rewatch_st[of U V, THEN order_trans])
      (auto intro!: conc_fun_R_mono simp: Collect_eq_comp'
        twl_st_heur_parsing_def)
qed


lemma rewatch_heur_st_rewatch_st3:
  assumes
    T: \<open>(U, V)
     \<in> twl_st_heur_parsing_no_WL (mset_set (extract_atms_clss CS {})) False O
       {(S, T). S = remove_watched T \<and> get_watched_wl (fst T) = (\<lambda>_. [])}\<close> and
     failed: \<open>\<not>is_failed_heur_init U\<close>
  shows \<open>rewatch_heur_st_fast
          (convert_state (virtual_copy (mset_set (extract_atms_clss CS {}))) U)
         \<le> \<Down> ({(S,T). (S, T) \<in> twl_st_heur_parsing (mset_set (extract_atms_clss CS {})) True \<and>
         get_clauses_wl_heur_init S = get_clauses_wl_heur_init U \<and>
	 get_conflict_wl_heur_init S = get_conflict_wl_heur_init U \<and>
         get_clauses_wl (fst T) = get_clauses_wl (fst V) \<and>
	 get_conflict_wl (fst T) = get_conflict_wl (fst V) \<and>
	 get_unit_clauses_wl (fst T) = get_unit_clauses_wl (fst V)} O {(S, T). S = (T, {#})})
            (rewatch_st (from_init_state V))\<close>
proof -
  have
    UV: \<open>(U, V)
     \<in> twl_st_heur_parsing_no_WL (mset_set (extract_atms_clss CS {})) True O
       {(S, T). S = remove_watched T \<and> get_watched_wl (fst T) = (\<lambda>_. [])}\<close>
    using T failed by (fastforce simp: twl_st_heur_parsing_no_WL_def)
  then show ?thesis
    unfolding convert_state_def finalise_init_def id_def rewatch_heur_st_fast_def
    by (rule rewatch_heur_st_rewatch_st[of U V, THEN order_trans])
      (auto intro!: conc_fun_R_mono simp: Collect_eq_comp'
        twl_st_heur_parsing_def)
qed

lemma IsaSAT_heur_IsaSAT:
  \<open>IsaSAT_heur b CS \<le> \<Down>{((M, stats), M'). M = map_option rev M'} (IsaSAT CS)\<close>
proof -
  have init_dt_wl_heur: \<open>init_dt_wl_heur True CS S \<le>
       \<Down>(twl_st_heur_parsing_no_WL \<A> True O {(S, T). S = remove_watched T \<and>
           get_watched_wl (fst T) = (\<lambda>_. [])})
        (init_dt_wl' CS T)\<close>
    if
      \<open>case (CS, T) of
       (CS, S) \<Rightarrow>
	 (\<forall>C\<in>set CS. literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (mset C)) \<and>
	 distinct_mset_set (mset ` set CS)\<close> and
      \<open>((CS, S), CS, T) \<in> \<langle>Id\<rangle>list_rel \<times>\<^sub>f twl_st_heur_parsing_no_WL \<A> True\<close>
  for \<A> CS T S
  proof -
    show ?thesis
      apply (rule init_dt_wl_heur_init_dt_wl[THEN fref_to_Down_curry, of \<A> CS T CS S,
        THEN order_trans])
      apply (rule that(1))
      apply (rule that(2))
      apply (cases \<open>init_dt_wl CS T\<close>)
      apply (force simp: init_dt_wl'_def RES_RETURN_RES conc_fun_RES
        Image_iff)+
      done
  qed
  have init_dt_wl_heur_b: \<open>init_dt_wl_heur False CS S \<le>
       \<Down>(twl_st_heur_parsing_no_WL \<A> False O {(S, T). S = remove_watched T \<and>
           get_watched_wl (fst T) = (\<lambda>_. [])})
        (init_dt_wl' CS T)\<close>
    if
      \<open>case (CS, T) of
       (CS, S) \<Rightarrow>
	 (\<forall>C\<in>set CS. literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (mset C)) \<and>
	 distinct_mset_set (mset ` set CS)\<close> and
      \<open>((CS, S), CS, T) \<in> \<langle>Id\<rangle>list_rel \<times>\<^sub>f twl_st_heur_parsing_no_WL \<A> True\<close>
  for \<A> CS T S
  proof -
    show ?thesis
      apply (rule init_dt_wl_heur_init_dt_wl[THEN fref_to_Down_curry, of \<A> CS T CS S,
        THEN order_trans])
      apply (rule that(1))
      using that(2) apply (force simp: twl_st_heur_parsing_no_WL_def)
      apply (cases \<open>init_dt_wl CS T\<close>)
      apply (force simp: init_dt_wl'_def RES_RETURN_RES conc_fun_RES
        Image_iff)+
      done
  qed
  have virtual_copy: \<open>(virtual_copy \<A>, ()) \<in> {(\<B>, c). c = () \<and> \<B> = \<A>}\<close> for \<B> \<A>
    by (auto simp: virtual_copy_def)
  have input_le: \<open>\<forall>C\<in>set CS. \<forall>L\<in>set C. nat_of_lit L \<le> uint_max\<close>
    if \<open>isasat_input_bounded (mset_set (extract_atms_clss CS {}))\<close>
  proof (intro ballI)
    fix C L
    assume \<open>C \<in> set CS\<close> and \<open>L \<in> set C\<close>
    then have \<open>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (mset_set (extract_atms_clss CS {}))\<close>
      by (auto simp: extract_atms_clss_alt_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n)
    then show \<open>nat_of_lit L \<le> uint_max\<close>
      using that by auto
  qed
  have lits_C: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset_set (extract_atms_clss CS {})) (mset C)\<close>
    if \<open>C \<in> set CS\<close> for C CS
    using that
    by (force simp: literals_are_in_\<L>\<^sub>i\<^sub>n_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n
     in_all_lits_of_m_ain_atms_of_iff extract_atms_clss_alt_def
     atm_of_eq_atm_of)
  have init_state_wl_heur: \<open>isasat_input_bounded \<A> \<Longrightarrow>
      init_state_wl_heur \<A> \<le> SPEC (\<lambda>c. (c, init_state_wl) \<in>
        {(S, S'). (S, S') \<in> twl_st_heur_parsing_no_WL_wl \<A> True})\<close> for \<A>
    apply (rule init_state_wl_heur_init_state_wl[THEN fref_to_Down_unRET_uncurry0_SPEC,
      of \<A>, THEN order_trans])
    apply (auto)
    done

  have get_conflict_wl_is_None_heur_init: \<open> (Tb, Tc)
    \<in> ({(S,T). (S, T) \<in> twl_st_heur_parsing (mset_set (extract_atms_clss CS {})) True \<and>
         get_clauses_wl_heur_init S = get_clauses_wl_heur_init U \<and>
	 get_conflict_wl_heur_init S = get_conflict_wl_heur_init U \<and>
         get_clauses_wl (fst T) = get_clauses_wl (fst V) \<and>
	 get_conflict_wl (fst T) = get_conflict_wl (fst V) \<and>
	 get_unit_clauses_wl (fst T) = get_unit_clauses_wl (fst V)} O {(S, T). S = (T, {#})}) \<Longrightarrow>
    (\<not> get_conflict_wl_is_None_heur_init Tb) = (get_conflict_wl Tc \<noteq> None)\<close> for Tb Tc U V
    by (cases V) (auto simp: twl_st_heur_parsing_def Collect_eq_comp'
      get_conflict_wl_is_None_heur_init_def
      option_lookup_clause_rel_def)
  have get_conflict_wl_is_None_heur_init3: \<open>(T, Ta)
    \<in> twl_st_heur_parsing_no_WL (mset_set (extract_atms_clss CS {})) False O
      {(S, T). S = remove_watched T \<and> get_watched_wl (fst T) = (\<lambda>_. [])}  \<Longrightarrow>
      (failed, faileda)
       \<in> {(b, b').  b = b' \<and> b = (is_failed_heur_init T \<or> \<not> isasat_fast_init T)} \<Longrightarrow> \<not>failed \<Longrightarrow> 
    (\<not> get_conflict_wl_is_None_heur_init T) = (get_conflict_wl (fst Ta) \<noteq> None)\<close> for T Ta failed faileda
    by (cases T; cases Ta) (auto simp: twl_st_heur_parsing_no_WL_def
      get_conflict_wl_is_None_heur_init_def
      option_lookup_clause_rel_def)
  have finalise_init_nempty: \<open>x1i \<noteq> None\<close> \<open>x1j \<noteq> None\<close>
    if
      T: \<open>(Tb, Tc)
       \<in> ({(S,T). (S, T) \<in> twl_st_heur_parsing (mset_set (extract_atms_clss CS {})) True \<and>
         get_clauses_wl_heur_init S = get_clauses_wl_heur_init U \<and>
	 get_conflict_wl_heur_init S = get_conflict_wl_heur_init U \<and>
         get_clauses_wl (fst T) = get_clauses_wl (fst V) \<and>
	 get_conflict_wl (fst T) = get_conflict_wl (fst V) \<and>
	 get_unit_clauses_wl (fst T) = get_unit_clauses_wl (fst V)} O {(S, T). S = (T, {#})})\<close> and
      nempty: \<open>extract_atms_clss CS {} \<noteq> {}\<close> and
      st:
        \<open>x2g = (x1j, x2h)\<close>
	\<open>x2f = (x1i, x2g)\<close>
	\<open>x2e = (x1h, x2f)\<close>
	\<open>x1f = (x1g, x2e)\<close>
	\<open>x1e = (x1f, x2i)\<close>
	\<open>x2j = (x1k, x2k)\<close>
	\<open>x2d = (x1e, x2j)\<close>
	\<open>x2c = (x1d, x2d)\<close>
	\<open>x2b = (x1c, x2c)\<close>
	\<open>x2a = (x1b, x2b)\<close>
	\<open>x2 = (x1a, x2a)\<close> and
      conv: \<open>convert_state (virtual_copy (mset_set (extract_atms_clss CS {}))) Tb =
       (x1, x2)\<close>
    for ba S T Ta Tb Tc uu x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x1f
      x1g x2e x1h x2f x1i x2g x1j x2h x2i x2j x1k x2k U V
  proof -
    show \<open>x1i \<noteq> None\<close>
      using T conv nempty
      unfolding st
      by (cases x1i)
       (auto simp: convert_state_def twl_st_heur_parsing_def
        isa_vmtf_init_def vmtf_init_def mset_set_empty_iff)
    show \<open>x1j \<noteq> None\<close>
      using T conv nempty
      unfolding st
      by (cases x1i)
       (auto simp: convert_state_def twl_st_heur_parsing_def
        isa_vmtf_init_def vmtf_init_def mset_set_empty_iff)
  qed

  have banner: \<open>isasat_information_banner
     (convert_state (virtual_copy (mset_set (extract_atms_clss CS {}))) Tb)
    \<le> SPEC (\<lambda>c. (c, ()) \<in> {(_, _). True})\<close> for Tb
    by (auto simp: isasat_information_banner_def)

  have finalise_init_code: \<open>finalise_init_code b
	 (convert_state (virtual_copy (mset_set (extract_atms_clss CS {}))) Tb)
	\<le> SPEC (\<lambda>c. (c, finalise_init Tc) \<in> twl_st_heur)\<close> (is ?A) and
    finalise_init_code3: \<open>finalise_init_code b  Tb
	\<le> SPEC (\<lambda>c. (c, finalise_init Tc) \<in> twl_st_heur)\<close> (is ?B)
    if
      T: \<open>(Tb, Tc)
       \<in> ({(S,T). (S, T) \<in> twl_st_heur_parsing (mset_set (extract_atms_clss CS {})) True \<and>
         get_clauses_wl_heur_init S = get_clauses_wl_heur_init U \<and>
	 get_conflict_wl_heur_init S = get_conflict_wl_heur_init U \<and>
         get_clauses_wl (fst T) = get_clauses_wl (fst V) \<and>
	 get_conflict_wl (fst T) = get_conflict_wl (fst V) \<and>
	 get_unit_clauses_wl (fst T) = get_unit_clauses_wl (fst V)} O {(S, T). S = (T, {#})})\<close> and
      confl: \<open>\<not> get_conflict_wl Tc \<noteq> None\<close> and
      nempty: \<open>extract_atms_clss CS {} \<noteq> {}\<close> and
      clss_CS: \<open>mset `# ran_mf (get_clauses_wl Tc) + get_unit_clauses_wl Tc =
       mset `# mset CS\<close> and
      learned: \<open>learned_clss_l (get_clauses_wl Tc) = {#}\<close>
    for ba S T Ta Tb Tc u v U V
  proof -
    have 1: \<open>get_conflict_wl Tc = None\<close>
      using confl by auto
    have 2: \<open>all_atms (get_clauses_wl Tc) (get_unit_clauses_wl Tc) \<noteq> {#}\<close>
      using clss_CS nempty
      by (auto simp flip: all_atms_def[symmetric] simp: all_lits_def
        isasat_input_bounded_nempty_def extract_atms_clss_alt_def
	all_lits_of_mm_empty_iff)
    have 3: \<open>set_mset (all_atms_st Tc) = set_mset (mset_set (extract_atms_clss CS {}))\<close>
      using clss_CS nempty
      by (auto simp flip: all_atms_def[symmetric] simp: all_lits_def
        isasat_input_bounded_nempty_def
  	atm_of_all_lits_of_mm extract_atms_clss_alt_def atms_of_ms_def)
    have H: \<open>A = B \<Longrightarrow> x \<in> A \<Longrightarrow> x \<in> B\<close> for A B x
      by auto
    have H': \<open>A = B \<Longrightarrow> A x \<Longrightarrow> B x\<close> for A B x
      by auto

    note cong =  trail_pol_cong
      option_lookup_clause_rel_cong isa_vmtf_init_cong
       vdom_m_cong[THEN H] isasat_input_nempty_cong[THEN iffD1]
      isasat_input_bounded_cong[THEN iffD1]
       cach_refinement_empty_cong[THEN H']
       phase_saving_cong[THEN H']
       \<L>\<^sub>a\<^sub>l\<^sub>l_cong[THEN H]
       D\<^sub>0_cong[THEN H]

    have 4: \<open>(convert_state (mset_set (extract_atms_clss CS {})) Tb, Tc)
    \<in> twl_st_heur_post_parsing_wl True\<close>
      using T nempty
      by (auto simp: twl_st_heur_parsing_def twl_st_heur_post_parsing_wl_def
        convert_state_def eq_commute[of \<open>mset _\<close> \<open>dom_m _\<close>]
	vdom_m_cong[OF 3[symmetric]] \<L>\<^sub>a\<^sub>l\<^sub>l_cong[OF 3[symmetric]]
	dest!: cong[OF 3[symmetric]])
    show ?A
     by (rule finalise_init_finalise_init[THEN fref_to_Down_unRET_curry_SPEC, of b])
      (use 1 2 learned 4 in auto)
    then show ?B unfolding convert_state_def by auto
  qed

  have get_conflict_wl_is_None_heur_init2: \<open>(U, V)
    \<in> twl_st_heur_parsing_no_WL (mset_set (extract_atms_clss CS {})) True O
      {(S, T). S = remove_watched T \<and> get_watched_wl (fst T) = (\<lambda>_. [])} \<Longrightarrow>
    (\<not> get_conflict_wl_is_None_heur_init
        (convert_state (virtual_copy (mset_set (extract_atms_clss CS {}))) U)) =
    (get_conflict_wl (from_init_state V) \<noteq> None)\<close> for U V
    by (auto simp: twl_st_heur_parsing_def Collect_eq_comp'
      get_conflict_wl_is_None_heur_init_def twl_st_heur_parsing_no_WL_def
      option_lookup_clause_rel_def convert_state_def from_init_state_def)

  have finalise_init2:  \<open>x1i \<noteq> None\<close> \<open>x1j \<noteq> None\<close>
    if
      T: \<open>(T, Ta)
       \<in> twl_st_heur_parsing_no_WL (mset_set (extract_atms_clss CS {})) b O
	 {(S, T). S = remove_watched T \<and> get_watched_wl (fst T) = (\<lambda>_. [])}\<close> and
      nempty: \<open>extract_atms_clss CS {} \<noteq> {}\<close> and
      st:
        \<open>x2g = (x1j, x2h)\<close>
	\<open>x2f = (x1i, x2g)\<close>
	\<open>x2e = (x1h, x2f)\<close>
	\<open>x1f = (x1g, x2e)\<close>
	\<open>x1e = (x1f, x2i)\<close>
	\<open>x2j = (x1k, x2k)\<close>
	\<open>x2d = (x1e, x2j)\<close>
	\<open>x2c = (x1d, x2d)\<close>
	\<open>x2b = (x1c, x2c)\<close>
	\<open>x2a = (x1b, x2b)\<close>
	\<open>x2 = (x1a, x2a)\<close> and
      conv: \<open>convert_state (virtual_copy (mset_set (extract_atms_clss CS {}))) T =
       (x1, x2)\<close>
     for uu ba S T Ta baa uua uub x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x1f
       x1g x2e x1h x2f x1i x2g x1j x2h x2i x2j x1k x2k b
  proof -
      show \<open>x1i \<noteq> None\<close>
      using T conv nempty
      unfolding st
      by (cases x1i)
       (auto simp: convert_state_def twl_st_heur_parsing_def
         twl_st_heur_parsing_no_WL_def
        isa_vmtf_init_def vmtf_init_def mset_set_empty_iff)
    show \<open>x1j \<noteq> None\<close>
      using T conv nempty
      unfolding st
      by (cases x1i)
       (auto simp: convert_state_def twl_st_heur_parsing_def
         twl_st_heur_parsing_no_WL_def
        isa_vmtf_init_def vmtf_init_def mset_set_empty_iff)
  qed

  have rewatch_heur_st_fast_pre: \<open>rewatch_heur_st_fast_pre
	 (convert_state (virtual_copy (mset_set (extract_atms_clss CS {}))) T)\<close>
    if
      T: \<open>(T, Ta)
       \<in> twl_st_heur_parsing_no_WL (mset_set (extract_atms_clss CS {})) True O
	 {(S, T). S = remove_watched T \<and> get_watched_wl (fst T) = (\<lambda>_. [])}\<close> and
      length_le: \<open>\<not>\<not>isasat_fast_init (convert_state (virtual_copy (mset_set (extract_atms_clss CS {}))) T)\<close>
    for uu ba S T Ta baa uua uub
  proof -
    have \<open>valid_arena (get_clauses_wl_heur_init T) (get_clauses_wl (fst Ta))
      (set (get_vdom_heur_init T))\<close>
      using T by (auto simp: twl_st_heur_parsing_no_WL_def)
    then show ?thesis
      using length_le unfolding rewatch_heur_st_fast_pre_def convert_state_def
        isasat_fast_init_def uint64_max_def uint32_max_def
      by (auto dest: valid_arena_in_vdom_le_arena)
  qed
  have rewatch_heur_st_fast_pre2: \<open>rewatch_heur_st_fast_pre
	 (convert_state (virtual_copy (mset_set (extract_atms_clss CS {}))) T)\<close>
    if
      T: \<open>(T, Ta)
       \<in> twl_st_heur_parsing_no_WL (mset_set (extract_atms_clss CS {})) False O
	 {(S, T). S = remove_watched T \<and> get_watched_wl (fst T) = (\<lambda>_. [])}\<close> and
      length_le: \<open>\<not>\<not>isasat_fast_init (convert_state (virtual_copy (mset_set (extract_atms_clss CS {}))) T)\<close> and
      failed: \<open>\<not>is_failed_heur_init T\<close>
    for uu ba S T Ta baa uua uub
  proof -
    have 
      Ta: \<open>(T, Ta)
     \<in> twl_st_heur_parsing_no_WL (mset_set (extract_atms_clss CS {})) True O
       {(S, T). S = remove_watched T \<and> get_watched_wl (fst T) = (\<lambda>_. [])}\<close>
       using failed T by (cases T; cases Ta) (fastforce simp: twl_st_heur_parsing_no_WL_def)
    from rewatch_heur_st_fast_pre[OF this length_le]
    show ?thesis .
  qed
  have finalise_init_code2: \<open>finalise_init_code b Tb
	\<le> SPEC (\<lambda>c. (c, finalise_init Tc) \<in>  {(S', T').
             (S', T') \<in> twl_st_heur \<and>
             get_clauses_wl_heur_init Tb = get_clauses_wl_heur S'})\<close>
  if
    Ta: \<open>(T, Ta)
     \<in> twl_st_heur_parsing_no_WL (mset_set (extract_atms_clss CS {})) False O
       {(S, T). S = remove_watched T \<and> get_watched_wl (fst T) = (\<lambda>_. [])}\<close> and
    confl: \<open>\<not> get_conflict_wl (from_init_state Ta) \<noteq> None\<close> and
    \<open>CS \<noteq> []\<close> and
    nempty: \<open>extract_atms_clss CS {} \<noteq> {}\<close> and
    \<open>isasat_input_bounded_nempty (mset_set (extract_atms_clss CS {}))\<close> and
    clss_CS: \<open>mset `# ran_mf (get_clauses_wl (from_init_state Ta)) +
     get_unit_clauses_wl (from_init_state Ta) =
     mset `# mset CS\<close> and
    learned: \<open>learned_clss_l (get_clauses_wl (from_init_state Ta)) = {#}\<close> and
    \<open>virtual_copy (mset_set (extract_atms_clss CS {})) \<noteq> {#}\<close> and
    \<open>isasat_input_bounded_nempty
      (virtual_copy (mset_set (extract_atms_clss CS {})))\<close> and
    \<open>case convert_state (virtual_copy (mset_set (extract_atms_clss CS {}))) T of
     (M', N', D', Q', W', xa, xb) \<Rightarrow>
       (case xa of
        (x, xa) \<Rightarrow>
          (case x of
           (ns, m, fst_As, lst_As, next_search) \<Rightarrow>
             \<lambda>to_remove (\<phi>, clvls). fst_As \<noteq> None \<and> lst_As \<noteq> None)
           xa)
        xb\<close> and
    T: \<open>(Tb, Tc)
     \<in> {(S, Ta'). (S, Ta')
               \<in> twl_st_heur_parsing (mset_set (extract_atms_clss CS {})) True \<and>
               get_clauses_wl_heur_init S = get_clauses_wl_heur_init T \<and>
               get_conflict_wl_heur_init S = get_conflict_wl_heur_init T \<and>
              get_clauses_wl (fst Ta') = get_clauses_wl (fst Ta) \<and>
               get_conflict_wl (fst Ta') = get_conflict_wl (fst Ta) \<and>
               get_unit_clauses_wl (fst Ta') = get_unit_clauses_wl (fst Ta)} O
       {(S, T). S = (T, {#})}\<close> and
    failed: \<open>\<not>is_failed_heur_init T\<close>
    for uu ba S T Ta baa uua uub V W b Tb Tc
  proof -
    have 
    Ta: \<open>(T, Ta)
     \<in> twl_st_heur_parsing_no_WL (mset_set (extract_atms_clss CS {})) True O
       {(S, T). S = remove_watched T \<and> get_watched_wl (fst T) = (\<lambda>_. [])}\<close>
       using failed Ta by (cases T; cases Ta) (fastforce simp: twl_st_heur_parsing_no_WL_def)

    have 1: \<open>get_conflict_wl Tc = None\<close>
      using confl T by (auto simp: from_init_state_def)
    have 2: \<open>all_atms (get_clauses_wl Tc) (get_unit_clauses_wl Tc) \<noteq> {#}\<close>
      using clss_CS[THEN arg_cong, of set_mset] clss_CS nempty T Ta
      by (auto 5 5 simp flip: all_atms_def[symmetric] simp: all_lits_def
        isasat_input_bounded_nempty_def extract_atms_clss_alt_def
	all_lits_of_mm_empty_iff from_init_state_def)
    have 3: \<open>set_mset (all_atms_st Tc) = set_mset (all_atms_st (fst Ta))\<close>
      using T by auto
    have 3: \<open>set_mset (all_atms_st Tc) = set_mset (mset_set (extract_atms_clss CS {}))\<close>
      using clss_CS[THEN arg_cong, of set_mset, simplified] nempty T Ta
      unfolding 3
      by (auto simp flip: all_atms_def[symmetric] simp: all_lits_def
        isasat_input_bounded_nempty_def from_init_state_def
  	atm_of_all_lits_of_mm extract_atms_clss_alt_def atms_of_ms_def)

    have H: \<open>A = B \<Longrightarrow> x \<in> A \<Longrightarrow> x \<in> B\<close> for A B x
      by auto
    have H': \<open>A = B \<Longrightarrow> A x \<Longrightarrow> B x\<close> for A B x
      by auto

    note cong =  trail_pol_cong
      option_lookup_clause_rel_cong isa_vmtf_init_cong
       vdom_m_cong[THEN H] isasat_input_nempty_cong[THEN iffD1]
      isasat_input_bounded_cong[THEN iffD1]
       cach_refinement_empty_cong[THEN H']
       phase_saving_cong[THEN H']
       \<L>\<^sub>a\<^sub>l\<^sub>l_cong[THEN H]
       D\<^sub>0_cong[THEN H]

    have 4: \<open>(convert_state (mset_set (extract_atms_clss CS {})) Tb, Tc)
    \<in> twl_st_heur_post_parsing_wl True\<close>
      using T  nempty
      by (auto simp: twl_st_heur_parsing_def twl_st_heur_post_parsing_wl_def
        convert_state_def eq_commute[of \<open>mset _\<close> \<open>dom_m _\<close>]
	vdom_m_cong[OF 3[symmetric]] \<L>\<^sub>a\<^sub>l\<^sub>l_cong[OF 3[symmetric]]
	dest!: cong[OF 3[symmetric]])

    show ?thesis
      apply (rule finalise_init_finalise_init_full[unfolded conc_fun_RETURN,
        THEN order_trans])
      by (use 1 2 learned 4 T in \<open>auto simp: from_init_state_def convert_state_def\<close>)
  qed
  have isasat_fast: \<open>isasat_fast Td\<close>
   if
     fast: \<open>\<not> \<not> isasat_fast_init
	   (convert_state (virtual_copy (mset_set (extract_atms_clss CS {})))
	     T)\<close> and
     Tb: \<open>(Tb, Tc)
      \<in> {(S, Tb).
	 (S, Tb) \<in> twl_st_heur_parsing (mset_set (extract_atms_clss CS {})) True \<and>
	 get_clauses_wl_heur_init S = get_clauses_wl_heur_init T \<and>
	 get_conflict_wl_heur_init S = get_conflict_wl_heur_init T \<and>
	 get_clauses_wl (fst Tb) = get_clauses_wl (fst Ta) \<and>
	 get_conflict_wl (fst Tb) = get_conflict_wl (fst Ta) \<and>
	 get_unit_clauses_wl (fst Tb) = get_unit_clauses_wl (fst Ta)} O
	{(S, T). S = (T, {#})}\<close> and
     Td: \<open>(Td, Te)
      \<in> {(S', T').
	 (S', T') \<in> twl_st_heur \<and>
	 get_clauses_wl_heur_init Tb = get_clauses_wl_heur S'}\<close>
    for uu ba S T Ta baa uua uub Tb Tc Td Te
  proof -
     show ?thesis
       using fast Td Tb
       by (auto simp: convert_state_def isasat_fast_init_def isasat_fast_def)
  qed
  define init_succesfull where \<open>init_succesfull T = RETURN (is_failed_heur_init T \<or> \<not>isasat_fast_init T)\<close> for T
  define init_succesfull2 where \<open>init_succesfull2 = SPEC (\<lambda>_ :: bool. True)\<close>
  have [refine]: \<open>init_succesfull T \<le> \<Down> {(b, b'). (b = b') \<and> (b \<longleftrightarrow> is_failed_heur_init T \<or> \<not>isasat_fast_init T)}
      init_succesfull2\<close> for T
   by (auto simp: init_succesfull_def init_succesfull2_def intro!: RETURN_RES_refine)
  show ?thesis
    supply [[goals_limit=1]]
    unfolding IsaSAT_heur_alt_def IsaSAT_alt_def init_succesfull_def[symmetric]
    apply (rewrite at \<open>do {_ \<leftarrow> init_dt_wl' _ _; _ \<leftarrow> (\<hole> :: bool nres); If _ _ _ }\<close> init_succesfull2_def[symmetric])
    apply (refine_vcg virtual_copy init_state_wl_heur banner
      cdcl_twl_stgy_restart_prog_wl_heur_cdcl_twl_stgy_restart_prog_wl_D[THEN fref_to_Down])
    subgoal by (rule input_le)
    subgoal by (rule distinct_mset_mset_set)
    subgoal by auto
    subgoal by auto
    apply (rule init_dt_wl_heur[of \<open>mset_set (extract_atms_clss CS {})\<close>])
    subgoal by (auto simp: lits_C)
    subgoal by (auto simp: twl_st_heur_parsing_no_WL_wl_def
       twl_st_heur_parsing_no_WL_def to_init_state_def
       init_state_wl_def init_state_wl_heur_def
       inres_def RES_RES_RETURN_RES
       RES_RETURN_RES)
    apply (rule rewatch_heur_st_rewatch_st; assumption)
    subgoal unfolding convert_state_def by (rule get_conflict_wl_is_None_heur_init)
    subgoal by (simp add: empty_init_code_def)
    subgoal by simp
    subgoal by (simp add: empty_conflict_code_def)
    subgoal by (simp add: mset_set_empty_iff extract_atms_clss_alt_def)
    subgoal by simp
    subgoal by (rule finalise_init_nempty)
    subgoal by (rule finalise_init_nempty)
    apply (rule finalise_init_code; assumption)
    subgoal by fast
    subgoal by fast
    subgoal premises p for _ ba S T Ta Tb Tc u v
      using p(27)
      by (auto simp: twl_st_heur_def get_conflict_wl_is_None_heur_def
        extract_stats_def extract_state_stat_def
	option_lookup_clause_rel_def trail_pol_def
	extract_model_of_state_def rev_map
	extract_model_of_state_stat_def
	dest!: ann_lits_split_reasons_map_lit_of)


    apply (rule init_dt_wl_heur_b[of \<open>mset_set (extract_atms_clss CS {})\<close>])
    subgoal by (auto simp: lits_C)
    subgoal by (auto simp: twl_st_heur_parsing_no_WL_wl_def
       twl_st_heur_parsing_no_WL_def to_init_state_def
       init_state_wl_def init_state_wl_heur_def
       inres_def RES_RES_RETURN_RES
       RES_RETURN_RES)
    subgoal by fast
    apply (rule init_dt_wl_heur[of \<open>mset_set (extract_atms_clss CS {})\<close>])
    subgoal by (auto simp: lits_C)
    subgoal by (auto simp: twl_st_heur_parsing_no_WL_wl_def
       twl_st_heur_parsing_no_WL_def to_init_state_def
       init_state_wl_def init_state_wl_heur_def
       inres_def RES_RES_RETURN_RES
       RES_RETURN_RES)
    apply (rule rewatch_heur_st_rewatch_st; assumption)
    subgoal unfolding convert_state_def by (rule get_conflict_wl_is_None_heur_init)
    subgoal by (simp add: empty_init_code_def)
    subgoal by simp
    subgoal by (simp add: empty_conflict_code_def)
    subgoal by (simp add: mset_set_empty_iff extract_atms_clss_alt_def)
    subgoal by simp
    subgoal by (rule finalise_init_nempty)
    subgoal by (rule finalise_init_nempty)
    apply (rule finalise_init_code; assumption)
    subgoal by fast
    subgoal by fast
    subgoal premises p for _ ba S T Ta Tb Tc u v
      using p(34)
      by (auto simp: twl_st_heur_def get_conflict_wl_is_None_heur_def
        extract_stats_def extract_state_stat_def
	option_lookup_clause_rel_def trail_pol_def
	extract_model_of_state_def rev_map
	extract_model_of_state_stat_def
	dest!: ann_lits_split_reasons_map_lit_of)
    subgoal unfolding from_init_state_def convert_state_def by (rule get_conflict_wl_is_None_heur_init3)
    subgoal by (simp add: empty_init_code_def)
    subgoal by simp
    subgoal by (simp add: empty_conflict_code_def)
    subgoal by (simp add: mset_set_empty_iff extract_atms_clss_alt_def)
    subgoal by (simp add: mset_set_empty_iff extract_atms_clss_alt_def)
    subgoal by (rule finalise_init2)
    subgoal by (rule finalise_init2)
    subgoal for uu ba S T Ta baa uua
      by (rule rewatch_heur_st_fast_pre2; assumption?) (simp_all add: convert_state_def)
    apply (rule rewatch_heur_st_rewatch_st3; assumption?)
    subgoal by auto
    subgoal by (clarsimp simp add: isasat_fast_init_def convert_state_def)
    apply (rule finalise_init_code2; assumption?)
    subgoal by clarsimp
    subgoal by (clarsimp simp add: isasat_fast_def isasat_fast_init_def convert_state_def)
    apply (rule_tac r1 = \<open>length (get_clauses_wl_heur Td)\<close> in cdcl_twl_stgy_restart_prog_early_wl_heur_cdcl_twl_stgy_restart_prog_early_wl_D[
      THEN fref_to_Down])
    subgoal by (auto simp: isasat_fast_def)
    subgoal by fast
    subgoal by fast
    subgoal premises p for _ ba S T Ta Tb Tc u v
      using p(33)
      by (auto simp: twl_st_heur_def get_conflict_wl_is_None_heur_def
        extract_stats_def extract_state_stat_def
	option_lookup_clause_rel_def trail_pol_def
	extract_model_of_state_def rev_map
	extract_model_of_state_stat_def
	dest!: ann_lits_split_reasons_map_lit_of)
    done
qed

lemma isasat_fast_init_alt_def:
  \<open>RETURN o isasat_fast_init = (\<lambda>(M, N, _). RETURN (length N \<le> 18446744071562067962))\<close>
  by (auto simp: isasat_fast_init_def uint64_max_def uint32_max_def intro!: ext)

definition  model_stat_rel where
  \<open>model_stat_rel = {((M', s), M). map_option rev M = M'}\<close>


lemma nat_of_uint32_max:
  \<open>max (nat_of_uint32 a) (nat_of_uint32 b) = nat_of_uint32 (max a b)\<close> for a b
  by (auto simp: max_def nat_of_uint32_le_iff)

lemma max_0L_uint32[simp]: \<open>max (0::uint32) a = a\<close>
  by (metis max.cobounded2 max_def uint32_less_than_0)


definition length_get_clauses_wl_heur_init where
  \<open>length_get_clauses_wl_heur_init S = length (get_clauses_wl_heur_init S)\<close>

lemma length_get_clauses_wl_heur_init_alt_def:
  \<open>RETURN o length_get_clauses_wl_heur_init = (\<lambda>(_, N,_). RETURN (length N))\<close>
  unfolding length_get_clauses_wl_heur_init_def
  by auto

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
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_alt_def cdcl\<^sub>W_restart_mset.no_smaller_propa_def
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

definition SAT_l' where
  \<open>SAT_l' CS = do{
    S \<leftarrow> SAT_l CS;
    RETURN (if get_conflict_l S = None then Some (map lit_of (get_trail_l S)) else None)
  }\<close>


definition SAT0' where
  \<open>SAT0' CS = do{
    S \<leftarrow> SAT0 CS;
    RETURN (if get_conflict S = None then Some (map lit_of (get_trail S)) else None)
  }\<close>


lemma twl_st_l_map_lit_of[twl_st_l, simp]:
  \<open>(S, T) \<in> twl_st_l b \<Longrightarrow> map lit_of (get_trail_l S) = map lit_of (get_trail T)\<close>
  by (auto simp: twl_st_l_def convert_lits_l_map_lit_of)


lemma ISASAT_SAT_l':
  assumes \<open>Multiset.Ball (mset `# mset CS) distinct_mset\<close> and
    \<open>isasat_input_bounded (mset_set (\<Union>C\<in>set CS. atm_of ` set C))\<close>
  shows \<open>IsaSAT CS \<le> \<Down> Id (SAT_l' CS)\<close>
  unfolding IsaSAT_def SAT_l'_def
  apply refine_vcg
  apply (rule SAT_wl_SAT_l)
  subgoal using assms by auto
  subgoal using assms by auto
  subgoal by (auto simp: extract_model_of_state_def)
  done

lemma SAT_l'_SAT0':
  assumes \<open>Multiset.Ball (mset `# mset CS) distinct_mset\<close>
  shows \<open>SAT_l' CS \<le> \<Down> Id (SAT0' CS)\<close>
  unfolding SAT_l'_def SAT0'_def
  apply refine_vcg
  apply (rule SAT_l_SAT0)
  subgoal using assms by auto
  subgoal by (auto simp: extract_model_of_state_def)
  done

lemma SAT0'_SAT':
  assumes \<open>Multiset.Ball (mset `# mset CS) distinct_mset\<close>
  shows \<open>SAT0' CS \<le> \<Down> Id (SAT' (mset `# mset CS))\<close>
  unfolding SAT'_def SAT0'_def
  apply refine_vcg
  apply (rule SAT0_SAT)
  subgoal using assms by auto
  subgoal by (auto simp: extract_model_of_state_def twl_st_l twl_st)
  done


lemma IsaSAT_heur_model_if_sat:
  assumes \<open>\<forall>C \<in># mset `# mset CS. distinct_mset C\<close> and
    \<open>isasat_input_bounded (mset_set (\<Union>C\<in>set CS. atm_of ` set C))\<close>
  shows \<open>IsaSAT_heur opts CS \<le> \<Down> model_stat_rel (model_if_satisfiable (mset `# mset CS))\<close>
  apply (rule IsaSAT_heur_IsaSAT[THEN order_trans])
  apply (rule order_trans)
  apply (rule ref_two_step')
  apply (rule ISASAT_SAT_l')
  subgoal using assms by auto
  subgoal using assms by auto

  unfolding conc_fun_chain
  apply (rule order_trans)
  apply (rule ref_two_step')
  apply (rule SAT_l'_SAT0')
  subgoal using assms by auto

  unfolding conc_fun_chain
  apply (rule order_trans)
  apply (rule ref_two_step')
  apply (rule SAT0'_SAT')
  subgoal using assms by auto

  unfolding conc_fun_chain
  apply (rule order_trans)
  apply (rule ref_two_step')
  apply (rule SAT_model_if_satisfiable[THEN fref_to_Down, of \<open>mset `# mset CS\<close>])
  subgoal using assms by auto
  subgoal using assms by auto

  unfolding conc_fun_chain
  apply (rule conc_fun_R_mono)
  apply (auto simp: model_stat_rel_def)
  done

lemma IsaSAT_heur_model_if_sat': \<open>(uncurry IsaSAT_heur, uncurry (\<lambda>_. model_if_satisfiable)) \<in>
   [\<lambda>(_, CS). (\<forall>C \<in># CS. distinct_mset C) \<and>
     (\<forall>C\<in>#CS. \<forall>L\<in>#C. nat_of_lit L \<le> uint_max)]\<^sub>f
     Id \<times>\<^sub>r list_mset_rel O \<langle>list_mset_rel\<rangle>mset_rel \<rightarrow> \<langle>model_stat_rel\<rangle>nres_rel\<close>
proof -
  have H: \<open>isasat_input_bounded (mset_set (\<Union>C\<in>set CS. atm_of ` set C))\<close>
    if CS_p: \<open>\<forall>C\<in>#CS'. \<forall>L\<in>#C. nat_of_lit L \<le> uint_max\<close> and
      \<open>(CS, CS') \<in> list_mset_rel O \<langle>list_mset_rel\<rangle>mset_rel\<close>
    for CS CS'
    unfolding isasat_input_bounded_def
  proof
    fix L
    assume L: \<open>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (mset_set (\<Union>C\<in>set CS. atm_of ` set C))\<close>
    then obtain C where
      L: \<open>C\<in>set CS \<and> (L \<in>set C \<or> - L \<in> set C)\<close>
      apply (cases L)
      apply (auto simp: extract_atms_clss_alt_def uint_max_def nat_of_uint32_uint32_of_nat_id
          \<L>\<^sub>a\<^sub>l\<^sub>l_def)+
      apply (metis literal.exhaust_sel)+
      done
    have \<open>nat_of_lit L \<le> uint_max \<or> nat_of_lit (-L) \<le> uint_max\<close>
      using L CS_p that by (auto simp: list_mset_rel_def mset_rel_def br_def
      br_def mset_rel_def p2rel_def rel_mset_def
        rel2p_def[abs_def] list_all2_op_eq_map_right_iff')
    then show \<open>nat_of_lit L \<le> uint_max\<close>
      using L
      by (cases L) (auto simp: extract_atms_clss_alt_def uint_max_def)
  qed
  show ?thesis
    apply (intro frefI nres_relI)
    unfolding uncurry_def
    apply clarify
    subgoal for o1 o2 o3 CS o1' o2' o3' CS'
    apply (rule IsaSAT_heur_model_if_sat[THEN order_trans, of CS _ \<open>(o1, o2, o3)\<close>])
    subgoal by (auto simp: list_mset_rel_def mset_rel_def br_def
      br_def mset_rel_def p2rel_def rel_mset_def
        rel2p_def[abs_def] list_all2_op_eq_map_right_iff')
    subgoal by (rule H) auto
    apply (auto simp: list_mset_rel_def mset_rel_def br_def
      br_def mset_rel_def p2rel_def rel_mset_def
        rel2p_def[abs_def] list_all2_op_eq_map_right_iff')
    done
    done
qed

definition IsaSAT_bounded_heur :: \<open>opts \<Rightarrow> nat clause_l list \<Rightarrow> (bool \<times> (nat literal list option \<times> stats)) nres\<close> where
  \<open>IsaSAT_bounded_heur opts CS = do{
    ASSERT(isasat_input_bounded (mset_set (extract_atms_clss CS {})));
    ASSERT(\<forall>C\<in>set CS. \<forall>L\<in>set C. nat_of_lit L \<le> uint_max);
    let \<A>\<^sub>i\<^sub>n' = mset_set (extract_atms_clss CS {});
    ASSERT(isasat_input_bounded \<A>\<^sub>i\<^sub>n');
    ASSERT(distinct_mset \<A>\<^sub>i\<^sub>n');
    let \<A>\<^sub>i\<^sub>n'' = virtual_copy \<A>\<^sub>i\<^sub>n';
    let b = opts_unbounded_mode opts;
    S \<leftarrow> init_state_wl_heur \<A>\<^sub>i\<^sub>n';
    (T::twl_st_wl_heur_init) \<leftarrow> init_dt_wl_heur False CS S;
    let T = convert_state \<A>\<^sub>i\<^sub>n'' T;
    if \<not>get_conflict_wl_is_None_heur_init T
    then RETURN (True, empty_init_code)
    else if CS = [] then do {stat \<leftarrow> empty_conflict_code; RETURN (True, stat)}
    else
    if isasat_fast_init T \<and> \<not>is_failed_heur_init T
    then do {
      ASSERT(\<A>\<^sub>i\<^sub>n'' \<noteq> {#});
      ASSERT(isasat_input_bounded_nempty \<A>\<^sub>i\<^sub>n'');
      _ \<leftarrow> isasat_information_banner T;
      ASSERT((\<lambda>(M', N', D', Q', W', ((ns, m, fst_As, lst_As, next_search), to_remove), \<phi>, clvls). fst_As \<noteq> None \<and>
        lst_As \<noteq> None) T);
      ASSERT(rewatch_heur_st_fast_pre T);
      T \<leftarrow> rewatch_heur_st_fast T;
      ASSERT(isasat_fast_init T);
      T \<leftarrow> finalise_init_code opts (T::twl_st_wl_heur_init);
      ASSERT(isasat_fast T);
      (b, U) \<leftarrow> cdcl_twl_stgy_restart_prog_bounded_wl_heur T;
      RETURN (b, if get_conflict_wl_is_None_heur U then extract_model_of_state_stat U
        else extract_state_stat U)
    } else RETURN (False, empty_init_code)
  }\<close>

end
