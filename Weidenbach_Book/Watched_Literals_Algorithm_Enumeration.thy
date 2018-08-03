theory Watched_Literals_Algorithm_Enumeration
  imports Watched_Literals.Watched_Literals_Algorithm Watched_Literals_Transition_System_Enumeration
begin

definition cdcl_twl_enum_inv :: \<open>'v twl_st \<Rightarrow> bool\<close> where
  \<open>cdcl_twl_enum_inv S \<longleftrightarrow> twl_struct_invs S \<and> twl_stgy_invs S \<and> final_twl_state S \<and>
         cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S)\<close>

definition mod_restriction :: \<open>'v clauses \<Rightarrow> 'v clauses \<Rightarrow> bool\<close> where
\<open>mod_restriction N N' \<longleftrightarrow>
       (\<forall>M. M \<Turnstile>sm N \<longrightarrow> M \<Turnstile>sm N') \<and>
       (\<forall>M. total_over_m M (set_mset N') \<longrightarrow> consistent_interp M \<longrightarrow> M \<Turnstile>sm N' \<longrightarrow> M \<Turnstile>sm N)\<close>

lemma mod_restriction_satisfiable_iff:
  \<open>mod_restriction N N' \<Longrightarrow> satisfiable (set_mset N) \<longleftrightarrow> satisfiable (set_mset N')\<close>
  apply (auto simp: mod_restriction_def satisfiable_carac[symmetric])
  by (meson satisfiable_carac satisfiable_def true_clss_set_mset)

definition enum_mod_restriction_st_clss :: \<open>('v twl_st \<times> ('v literal list option \<times> 'v clauses)) set\<close> where
  \<open>enum_mod_restriction_st_clss = {(S, (M, N)). mod_restriction (get_all_init_clss S) N \<and>
      twl_struct_invs S \<and> twl_stgy_invs S \<and>
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S) \<and>
      atms_of_mm (get_all_init_clss S) = atms_of_mm N}\<close>


definition enum_model_st_direct :: \<open>('v twl_st \<times> ('v literal list option \<times> 'v clauses)) set\<close> where
  \<open>enum_model_st_direct = {(S, (M, N)).
         mod_restriction (get_all_init_clss S) N \<and>
         (get_conflict S = None \<longrightarrow> M \<noteq> None \<and> lit_of `# mset (get_trail S) = mset (the M)) \<and>
         (get_conflict S \<noteq> None \<longrightarrow> M = None) \<and>
         atms_of_mm (get_all_init_clss S) = atms_of_mm N \<and>
         (get_conflict S = None \<longrightarrow> next_model (map lit_of (get_trail S)) N) \<and>
         cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S) \<and>
         cdcl_twl_enum_inv S}\<close>

definition enum_model_st :: \<open>((bool \<times> 'v twl_st) \<times> ('v literal list option \<times> 'v clauses)) set\<close> where
  \<open>enum_model_st = {((b, S), (M, N)).
         mod_restriction (get_all_init_clss S) N \<and>
         (b \<longrightarrow> get_conflict S = None \<and> M \<noteq> None \<and> lits_of_l (get_trail S) = set (the M)) \<and>
         (get_conflict S \<noteq> None \<longrightarrow> \<not>b \<and> M = None)}\<close>


fun add_to_init_cls :: \<open>'v twl_cls \<Rightarrow> 'v twl_st \<Rightarrow> 'v twl_st\<close> where
  \<open>add_to_init_cls C (M, N, U, D, NE, UE, WS, Q) = (M, add_mset C N, U, D, NE, UE, WS, Q)\<close>

lemma cdcl_twl_stgy_final_twl_stateE:
  assumes
    \<open>cdcl_twl_stgy\<^sup>*\<^sup>* S T\<close> and
    final: \<open>final_twl_state T\<close> and
    \<open>twl_struct_invs S\<close> and
    \<open>twl_stgy_invs S\<close> and
    ent: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S)\<close> and
    Hunsat: \<open>get_conflict T \<noteq> None \<Longrightarrow> unsatisfiable (set_mset (get_all_init_clss S)) \<Longrightarrow> P\<close> and
    Hsat: \<open>get_conflict T = None \<Longrightarrow> consistent_interp (lits_of_l (get_trail T)) \<Longrightarrow>
       no_dup (get_trail T) \<Longrightarrow> atm_of ` (lits_of_l (get_trail T)) \<subseteq> atms_of_mm (get_all_init_clss T) \<Longrightarrow>
      get_trail T \<Turnstile>asm get_all_init_clss S \<Longrightarrow> satisfiable (set_mset (get_all_init_clss S)) \<Longrightarrow> P\<close>
  shows P
proof -
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (state\<^sub>W_of S) (state\<^sub>W_of T)\<close>
    by (simp add: assms(1) assms(3) rtranclp_cdcl_twl_stgy_cdcl\<^sub>W_stgy)
  have all_struct_T: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of T)\<close>
    using assms(1) assms(3) rtranclp_cdcl_twl_stgy_twl_struct_invs twl_struct_invs_def by blast
  then have
    M_lev: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (state\<^sub>W_of T)\<close> and
    alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of T)\<close>
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def by fast+

  have ent': \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of T)\<close>
    by (meson \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (state\<^sub>W_of S) (state\<^sub>W_of T)\<close> assms(3)
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
        cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_learned_clauses_entailed
        cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W_restart ent twl_struct_invs_def)
  have [simp]: \<open>get_all_init_clss T = get_all_init_clss S\<close>
    by (metis assms(1) rtranclp_cdcl_twl_stgy_all_learned_diff_learned)
  have stgy_T: \<open>twl_stgy_invs T\<close>
    using assms(1) assms(3) assms(4) rtranclp_cdcl_twl_stgy_twl_stgy_invs by blast
  consider
    (confl) \<open>count_decided (get_trail T) = 0\<close> and \<open>get_conflict T \<noteq> None\<close> |
    (sat) \<open>no_step cdcl_twl_stgy T\<close> and \<open>get_conflict T = None\<close>  |
    (unsat) \<open>no_step cdcl_twl_stgy T\<close> and \<open>get_conflict T \<noteq> None\<close>
    using final unfolding final_twl_state_def
    by fast
  then show ?thesis
  proof cases
    case confl
    then show ?thesis
      using conflict_of_level_unsatisfiable[OF all_struct_T] ent'
      by (auto simp: twl_st intro!: Hunsat)
  next
    case sat
    have \<open>no_step cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (state\<^sub>W_of T)\<close>
      using assms(1) assms(3) no_step_cdcl_twl_stgy_no_step_cdcl\<^sub>W_stgy
        rtranclp_cdcl_twl_stgy_twl_struct_invs sat(1) by blast
    from cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_final_state_conclusive2[OF this]
    have \<open>get_trail T \<Turnstile>asm cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of T)\<close>
      using sat all_struct_T
      unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      by (auto simp: twl_st)
    then have tr_T: \<open>get_trail T \<Turnstile>asm get_all_init_clss T\<close>
      by (cases T) (auto simp: clauses_def)
    show ?thesis
      apply (rule Hsat)
      subgoal using sat by auto
      subgoal using M_lev unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
        by (auto simp: twl_st)
      subgoal
        using tr_T M_lev unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (auto simp: twl_st)
      subgoal using alien unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def by (auto simp: twl_st)
      subgoal using tr_T by auto
      subgoal using tr_T M_lev unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
        by (auto simp: satisfiable_carac[symmetric] twl_st true_annots_true_cls)
      done
  next
    case unsat
    have \<open>no_step cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (state\<^sub>W_of T)\<close>
      using assms(1) assms(3) no_step_cdcl_twl_stgy_no_step_cdcl\<^sub>W_stgy
        rtranclp_cdcl_twl_stgy_twl_struct_invs unsat(1) by blast
    from cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_final_state_conclusive2[OF this]
    have unsat': \<open>unsatisfiable (set_mset (cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of T)))\<close>
      using unsat all_struct_T stgy_T
      unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def twl_stgy_invs_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant_def
      by (auto simp: twl_st)
    have unsat': \<open>unsatisfiable (set_mset (get_all_init_clss T))\<close>
    proof (rule ccontr)
      assume \<open>\<not> ?thesis\<close>
      then obtain I where
        cons: \<open>consistent_interp I\<close> and
        I: \<open>I \<Turnstile>sm get_all_init_clss T\<close> and
        tot: \<open>total_over_m I (set_mset (get_all_init_clss T))\<close>
        unfolding satisfiable_def by blast
      have [simp]: \<open>cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of T) = get_all_init_clss T + get_all_learned_clss T\<close>
        by (cases T) (auto simp: clauses_def)
      moreover have \<open>total_over_m I (set_mset (cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of T)))\<close>
        using alien tot unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def
        by (auto simp: cdcl\<^sub>W_restart_mset_state total_over_m_alt_def twl_st)
      ultimately have \<open>I \<Turnstile>sm cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of T)\<close>
        using ent' I cons unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def
          true_clss_clss_def total_over_m_def
        by (auto simp: clauses_def cdcl\<^sub>W_restart_mset_state satisfiable_carac[symmetric] twl_st)
      then show False
        using unsat' cons I by auto
    qed
    show ?thesis
      apply (rule Hunsat)
      subgoal using unsat by auto
      subgoal using unsat' by auto
      done
  qed
qed


context
  fixes P :: \<open>'v literal set \<Rightarrow> bool\<close>
begin

fun negate_model_and_add :: \<open>'v literal list option \<times> 'v clauses \<Rightarrow> _ \<times> 'v clauses\<close> where
  \<open>negate_model_and_add (Some M, N) =
     (if P (set M) then (Some M, N)
     else (None, add_mset (uminus `# mset M) N))\<close> |
  \<open>negate_model_and_add (None, N) = (None, N)\<close>

text \<open>
  The code below is a little tricky to get right (in a way that can be easily refined later).

  There are three cases:
    \<^enum> the considered clauses are not satisfiable. Then we can conclude that there is no model.
    \<^enum> the considered clauses are satisfiable and there is at least one decision. Then, we can simply
      apply \<^term>\<open>negate_model_and_add_twl\<close>.
    \<^enum> the considered clauses are satisfiable and there are no decisions. Then we cannot apply
      \<^term>\<open>negate_model_and_add_twl\<close>, because that would produce the empty clause that cannot
      be part of our state (because of our invariants). Therefore, as we know that the model is
      the last possible model, we break out of the loop and handle test if the model is acceptable
      outside of the loop.
\<close>

definition cdcl_twl_enum :: \<open>'v twl_st \<Rightarrow> bool nres\<close> where
  \<open>cdcl_twl_enum S = do {
     S \<leftarrow> conclusive_TWL_run S;
     S \<leftarrow> WHILE\<^sub>T\<^bsup>cdcl_twl_enum_inv\<^esup>
       (\<lambda>S. get_conflict S = None \<and> count_decided(get_trail S) > 0 \<and> \<not>P (lits_of_l (get_trail S)))
       (\<lambda>S. do {
             S \<leftarrow> SPEC (negate_model_and_add_twl S);
             conclusive_TWL_run S
           })
       S;
     if get_conflict S = None
     then RETURN (if count_decided(get_trail S) = 0 then P (lits_of_l (get_trail S)) else True)
     else RETURN (False)
    }\<close>

definition next_model_filtered_nres where
  \<open>next_model_filtered_nres N =
    SPEC (\<lambda>b. \<exists>M. full (next_model_filtered P) N M \<and> b = (fst M \<noteq> None))\<close>

lemma mod_restriction_next_modelD:
  \<open>mod_restriction N N' \<Longrightarrow> atms_of_mm N \<subseteq> atms_of_mm N' \<Longrightarrow> next_model M N \<Longrightarrow> next_model M N'\<close>
  by (auto simp: mod_restriction_def next_model.simps)

definition enum_mod_restriction_st_clss_after :: \<open>('v twl_st \<times> ('v literal list option \<times> 'v clauses)) set\<close> where
  \<open>enum_mod_restriction_st_clss_after = {(S, (M, N)).
      (get_conflict S = None \<longrightarrow> count_decided (get_trail S) = 0 \<longrightarrow>
          mod_restriction (add_mset {#} (get_all_init_clss S))
           (add_mset (uminus `# lit_of `# mset (get_trail S)) N)) \<and>
      (mod_restriction (get_all_init_clss S) N) \<and>
      twl_struct_invs S \<and> twl_stgy_invs S \<and>
      (get_conflict S = None \<longrightarrow> M \<noteq> None \<longrightarrow> P (set(the M)) \<and> lit_of `# mset (get_trail S) = mset (the M)) \<and>
      (get_conflict S \<noteq> None \<longrightarrow> M = None) \<and>
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S) \<and>
      atms_of_mm (get_all_init_clss S) = atms_of_mm N}\<close>

lemma atms_of_uminus_lit_of[simp]: \<open>atms_of {#- lit_of x. x \<in># A#} = atms_of (lit_of `# A)\<close>
  by (auto simp: atms_of_def image_image)

lemma lit_of_mset_eq_mset_setD[dest]:
  \<open>lit_of `# mset M = mset aa  \<Longrightarrow> set aa = lit_of ` set M\<close>
  by (metis set_image_mset set_mset_mset)

lemma mod_restriction_add_twice[simp]:
  \<open>mod_restriction A (add_mset C (add_mset C N)) \<longleftrightarrow> mod_restriction A (add_mset C N)\<close>
  by (auto simp: mod_restriction_def)

lemma
  assumes
    confl: \<open>get_conflict W = None\<close> and
    count_dec: \<open>count_decided (get_trail W) = 0\<close> and
    enum_inv: \<open>cdcl_twl_enum_inv W\<close> and
    mod_rest_U: \<open>mod_restriction (get_all_init_clss W) N\<close> and
    atms_U_U': \<open>atms_of_mm (get_all_init_clss W) = atms_of_mm N\<close>
  shows
    final_level0_add_empty_clause:
      \<open>mod_restriction (add_mset {#} (get_all_init_clss W))
        (add_mset {#- lit_of x. x \<in># mset (get_trail W)#} N)\<close>  (is ?A) and
    final_level0_add_empty_clause_unsat:
      \<open>unsatisfiable (set_mset (add_mset {#- lit_of x. x \<in># mset (get_trail W)#} N))\<close>  (is ?B)
proof -
  have [simp]: \<open>DECO_clause (get_trail W) = {#}\<close> and
    [simp]: \<open>{unmark L |L. is_decided L \<and> L \<in> set (trail (state\<^sub>W_of W))} = {}\<close>
    using count_dec by (auto simp: count_decided_0_iff DECO_clause_def
        filter_mset_empty_conv twl_st)
  have struct_W: \<open>twl_struct_invs W\<close> and
    ent_W: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of W)\<close>
    using enum_inv
    unfolding cdcl_twl_enum_inv_def by blast+
  have \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of W)\<close>  and
    decomp: \<open>all_decomposition_implies_m (cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of W))
                  (get_all_ann_decomposition (trail (state\<^sub>W_of W)))\<close>
    using struct_W unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast+
  have alien_W: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of W)\<close>
    using struct_W
    unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast
  have 1: \<open>set_mset (cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of W))\<Turnstile>ps
                 unmark_l (trail (state\<^sub>W_of W))\<close>
    using all_decomposition_implies_propagated_lits_are_implied[OF decomp]
    by simp
  then have 2: \<open>set_mset (get_all_init_clss W) \<Turnstile>ps
                    unmark_l (trail (state\<^sub>W_of W))\<close>
    using ent_W unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def
      cdcl\<^sub>W_restart_mset.clauses_def
    by (fastforce simp: clauses_def twl_st dest: true_clss_clss_generalise_true_clss_clss)

  have H: False
    if M_tr_W:  \<open>M \<Turnstile> {#- lit_of x. x \<in># mset (get_trail W)#}\<close> and
      M_U': \<open>M \<Turnstile>m N\<close> and
      tot: \<open>total_over_m M (set_mset N)\<close> and
      cons: \<open>consistent_interp M\<close>
    for M
  proof -
    have \<open>M \<Turnstile>sm get_all_init_clss W\<close>
      using mod_rest_U M_U' cons
      unfolding mod_restriction_def (* TODO proof*)
      apply auto
      using tot apply blast+
      done
    moreover have \<open>total_over_m M (set_mset (get_all_init_clss W) \<union>
                  unmark_l (trail (state\<^sub>W_of W)))\<close>
      using alien_W atms_U_U' tot
      unfolding total_over_m_alt_def total_over_set_alt_def
        cdcl\<^sub>W_restart_mset.no_strange_atm_def
      by (auto 5 5 dest: atms_of_DECO_clauseD simp: lits_of_def twl_st)
    ultimately have \<open>M \<Turnstile>s unmark_l (trail (state\<^sub>W_of W))\<close>
      using 2 cons unfolding true_clss_clss_def
      by auto
    then show False
      using cons M_tr_W
      by (auto simp: true_clss_def twl_st true_cls_def consistent_interp_def)
  qed
  then show ?A
    unfolding mod_restriction_def
    by auto
  from mod_restriction_satisfiable_iff[OF this]
  show ?B
    by (auto simp: satisfiable_def)
qed


lemma cdcl_twl_enum_next_model_filtered_nres:
  \<open>(cdcl_twl_enum, next_model_filtered_nres) \<in>
    [\<lambda>(M, N). M = None]\<^sub>f enum_mod_restriction_st_clss \<rightarrow> \<langle>bool_rel\<rangle>nres_rel\<close>
proof -
  define model_if_exists where
    \<open>model_if_exists S \<equiv> \<lambda>M.
      (if \<exists>M. next_model M (snd S)
       then (fst M \<noteq> None \<and> next_model (the (fst M)) (snd S) \<and> snd M = snd S)
       else (fst M = None \<and> M = S))\<close>
  for S :: \<open>_ \<times> 'v clauses\<close>

  have \<open>full (next_model_filtered P) S U \<longleftrightarrow>
         (\<exists>T. model_if_exists S T \<and> full (next_model_filtered P) (None, snd T) U)\<close>
    (is \<open>?A \<longleftrightarrow> ?B\<close>)
    if \<open>fst S = None\<close>
    for S U
  proof
    assume ?A
    then consider
      (nss) \<open>no_step (next_model_filtered P) S\<close> |
      (s1) T where \<open>(next_model_filtered P) S T\<close> and \<open>full (next_model_filtered P) T U\<close>
      unfolding full_def
      by (metis converse_rtranclpE)
    then show ?B
    proof cases
      case nss
      then have SU: \<open>S = U\<close>
        using \<open>?A\<close>
        apply (subst (asm) no_step_full_iff_eq)
         apply assumption by simp
      have \<open>model_if_exists S S\<close> and \<open>fst S = None\<close>
        using nss no_step_next_model_filtered_next_model_iff[of \<open>(_, snd S)\<close>] that
        unfolding model_if_exists_def
        by (cases S; auto; fail)+
      moreover {
        have \<open>no_step (next_model_filtered P) (None, snd S)\<close>
          using nss
          apply (subst no_step_next_model_filtered_next_model_iff)
          subgoal using that by (cases S) auto
          apply (subst (asm) no_step_next_model_filtered_next_model_iff)
          subgoal using that by (cases S) auto
          unfolding Ex_next_model_iff_statisfiable
          apply (rule unsatisfiable_mono)
           defer
           apply assumption
          by (cases S; cases \<open>fst S\<close>) (auto intro: unsatisfiable_mono)
        then have \<open>full (next_model_filtered P) (None, snd S) U\<close>
          apply (subst no_step_full_iff_eq)
           apply assumption
          using SU \<open>fst S = None\<close>
          by (cases S) auto
      }
      ultimately show ?B
        by fast
    next
      case (s1 T)
      obtain M where
        M: \<open>next_model M (snd S)\<close> and
        T: \<open>T = (if P (set M) then (Some M, snd S)
            else (None, add_mset (image_mset uminus (mset M)) (snd S)))\<close>
        using s1
        unfolding model_if_exists_def
        apply (cases T)
        apply (auto simp: next_model_filtered.simps)
        done
      let ?T = \<open>((Some M, snd S))\<close>
      have nm: \<open>model_if_exists S ?T\<close>
        using M T that unfolding model_if_exists_def
        by (cases S) auto
      moreover have \<open>full (next_model_filtered P) (negate_model_and_add ?T) U\<close>
        using s1(2) T
        by (auto split: if_splits)
      moreover have \<open>next_model_filtered P (None, snd ?T) (negate_model_and_add (Some M, snd S))\<close>
        using nm that by (cases S) (auto simp: next_model_filtered.simps model_if_exists_def
            split: if_splits)
      ultimately show ?B
      proof -
        have "(None, snd (Some M, snd S)) = S"
          by (metis (no_types) sndI surjective_pairing that) (* 40 ms *)
        then have "full (next_model_filtered P) (None, snd (Some M, snd S)) U"
          by (metis \<open>full (next_model_filtered P) S U\<close>) (* failed *)
        then show ?thesis
          using \<open>model_if_exists S (Some M, snd S)\<close> by blast (* 0.5 ms *)
      qed
    qed
  next
    assume ?B
    then show ?A
      apply (auto simp: model_if_exists_def full1_is_full full_fullI split: if_splits)
      by (metis prod.exhaust_sel that)
  qed
  note H = this
  have next_model_filtered_nres_alt_def: \<open>next_model_filtered_nres S  = do {
         S \<leftarrow> SPEC (model_if_exists S);
         T \<leftarrow> SPEC (\<lambda>T. full (next_model_filtered P) (None, snd S) T);
         RETURN (fst T \<noteq> None)
       }\<close> if \<open>fst S = None\<close> for S
    using that
    unfolding next_model_filtered_nres_def RES_RES_RETURN_RES RES_RETURN_RES
     H[OF that]
    by blast+
  have conclusive_run: \<open>conclusive_TWL_run S
      \<le> \<Down> {(S, T). (S, T) \<in> enum_model_st_direct \<and> final_twl_state S \<and>
           (get_conflict S = None \<longrightarrow> next_model (map lit_of (get_trail S)) (snd T)) \<and>
           (get_conflict S \<noteq> None \<longrightarrow> unsatisfiable (set_mset (snd T)))}
          (SPEC (model_if_exists MN))\<close>
       (is \<open>_ \<le> \<Down> ?spec_twl _\<close>)
    if
      S_MN: \<open>(S, MN) \<in> enum_mod_restriction_st_clss\<close> and
      M: \<open>case MN of (M, N) \<Rightarrow> M = None\<close>
    for S MN
  proof -
    have H: \<open>\<exists>s'\<in>Collect (model_if_exists MN). (s, s') \<in> enum_model_st_direct \<and> final_twl_state s \<and>
       (get_conflict s = None \<longrightarrow> next_model (map lit_of (get_trail s)) (snd s')) \<and>
       (get_conflict s \<noteq> None \<longrightarrow> unsatisfiable (set_mset (snd s')))\<close>
      if
        star: \<open>cdcl_twl_stgy\<^sup>*\<^sup>* S s\<close> and
        final: \<open>final_twl_state s\<close>
      for s :: \<open>'v twl_st\<close>
    proof -
      obtain N where
        [simp]: \<open>MN = (None, N)\<close>
        using M by auto
      have [simp]: \<open>get_all_init_clss s = get_all_init_clss S\<close>
        by (metis rtranclp_cdcl_twl_stgy_all_learned_diff_learned that(1))

      have struct_S: \<open>twl_struct_invs S\<close>
        using S_MN unfolding enum_mod_restriction_st_clss_def by blast
      moreover have stgy_S: \<open>twl_stgy_invs S\<close>
        using S_MN unfolding enum_mod_restriction_st_clss_def by blast
      moreover have ent: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S)\<close>
        using S_MN unfolding enum_mod_restriction_st_clss_def by blast
      then have ent_s: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of s)\<close>
        using rtranclp_cdcl_twl_stgy_cdcl\<^sub>W_learned_clauses_entailed_by_init star struct_S by blast
      then have enum_inv: \<open>cdcl_twl_enum_inv s\<close>
        using star S_MN final unfolding enum_mod_restriction_st_clss_def cdcl_twl_enum_inv_def
        by (auto intro: rtranclp_cdcl_twl_stgy_twl_struct_invs
            rtranclp_cdcl_twl_stgy_twl_stgy_invs)
      show ?thesis
        using struct_S stgy_S ent
      proof (rule cdcl_twl_stgy_final_twl_stateE[OF star final])
        assume
          confl: \<open>get_conflict s \<noteq> None\<close> and
          unsat: \<open>unsatisfiable (set_mset (get_all_init_clss S))\<close>
        let ?s = \<open>(None, snd MN)\<close>
        have s: \<open>(s, ?s) \<in> enum_model_st_direct\<close>
          using S_MN confl unsat enum_inv ent star unfolding enum_model_st_def
          by (auto simp: enum_model_st_direct_def enum_mod_restriction_st_clss_def
              intro: rtranclp_cdcl_twl_stgy_cdcl\<^sub>W_learned_clauses_entailed_by_init)
        moreover have \<open>model_if_exists MN ?s\<close>
          using unsat S_MN unsat_no_step_next_model_filtered[of N P] Ex_next_model_iff_statisfiable[of N]
          unfolding model_if_exists_def
          by (auto simp: enum_mod_restriction_st_clss_def
                mod_restriction_satisfiable_iff)
        moreover have \<open>unsatisfiable (set_mset N)\<close>
          using unsat
          using s unfolding enum_model_st_direct_def
          by (auto simp: mod_restriction_satisfiable_iff)
        ultimately show ?thesis
          apply -
          by (rule bexI[of _ \<open>?s\<close>]) (use confl final in auto)
      next
        let ?s = \<open>(Some (map lit_of (get_trail s)), N)\<close>
        assume
          confl: \<open>get_conflict s = None\<close> and
          cons: \<open>consistent_interp (lits_of_l (get_trail s))\<close> and
          ent: \<open>get_trail s \<Turnstile>asm get_all_init_clss S\<close> and
          sat: \<open>satisfiable (set_mset (get_all_init_clss S))\<close> and
          n_d: \<open>no_dup (get_trail s)\<close> and
          alien: \<open>atm_of ` (lits_of_l (get_trail s)) \<subseteq> atms_of_mm (get_all_init_clss s)\<close>
        moreover have nm: \<open>next_model (map lit_of (get_trail s)) N\<close>
          \<open>next_model (map lit_of (get_trail s)) (get_all_init_clss s)\<close>
          using ent cons n_d S_MN alien
          by (auto simp: next_model.simps true_annots_true_cls lits_of_def
              no_dup_map_lit_of enum_mod_restriction_st_clss_def mod_restriction_def)
        ultimately have s: \<open>(s, ?s) \<in> enum_model_st_direct\<close>
          using S_MN enum_inv star ent unfolding enum_model_st_direct_def
          by (auto simp: mod_restriction_satisfiable_iff next_model.simps
              enum_mod_restriction_st_clss_def lits_of_def
              rtranclp_cdcl_twl_stgy_cdcl\<^sub>W_learned_clauses_entailed_by_init)
        moreover have \<open>model_if_exists (None, N) (Some (map lit_of (get_trail s)), N)\<close>
            using nm by (auto simp: model_if_exists_def
                enum_mod_restriction_st_clss_def
                mod_restriction_satisfiable_iff)
        moreover have \<open>satisfiable (set_mset N)\<close>
          using sat
          using s unfolding enum_model_st_direct_def
          by (auto simp: Ex_next_model_iff_statisfiable[symmetric])
        ultimately show ?thesis
          using nm
          apply -
          by (rule bexI[of _ \<open>(Some (map lit_of (get_trail s)), snd MN)\<close>])
            (use final confl in auto)
      qed
    qed
    show ?thesis
      unfolding conclusive_TWL_run_def (* enum_model_st_direct_def *) (* final_twl_state_def *)
      apply (rule RES_refine)
      unfolding mem_Collect_eq prod.simps
      apply (rule H)
      apply fast+
      done
  qed
  have loop: \<open>WHILE\<^sub>T\<^bsup>cdcl_twl_enum_inv\<^esup>
       (\<lambda>S. get_conflict S = None \<and> count_decided (get_trail S) > 0 \<and>
             \<not>P (lits_of_l (get_trail S)))
       (\<lambda>S. SPEC (negate_model_and_add_twl S) \<bind>
             conclusive_TWL_run) T
      \<le> SPEC
          (\<lambda>y. \<exists>x. (y, x) \<in> {(y, x).
                       (( (get_conflict y \<noteq> None \<and> fst x = None) \<or>
                          (fst x \<noteq> None \<and> P (lits_of_l (get_trail y))) \<and>
                         (y, x) \<in> enum_mod_restriction_st_clss_after) \<or>
                       (get_conflict y = None \<and> count_decided (get_trail y) = 0 \<and>
                          \<not>P (lits_of_l (get_trail y)) \<and> fst x = None \<and>
                          (y, (None, remove1_mset (uminus `# lit_of `# mset (get_trail y)) (snd x)))
                            \<in> enum_mod_restriction_st_clss_after))
                    } \<and>
                  full (next_model_filtered P) (None, snd M) x)\<close>
       (is \<open>WHILE\<^sub>T\<^bsup>_ \<^esup> ?Cond _ _ \<le> SPEC ?Spec\<close>
       is \<open>_ \<le> SPEC (\<lambda>y. \<exists>x. (y, x) \<in> ?Res \<and> ?Full x)\<close>)
    if
      MN: \<open>case MN of (M, N) \<Rightarrow> M = None\<close> and
      S: \<open>(S, MN) \<in> enum_mod_restriction_st_clss\<close> and
      T: \<open>(T, M) \<in> ?spec_twl\<close> and
      M: \<open>M \<in> Collect (model_if_exists MN)\<close>
    for S T :: \<open>'v twl_st\<close> and MN M
  proof -
    define R where
       \<open>R = {(T :: 'v twl_st, S :: 'v twl_st).
               get_conflict S = None \<and> \<not>P (lits_of_l (get_trail S)) \<and> get_conflict T = None \<and>
                \<not>P (lits_of_l (get_trail T)) \<and>
               (get_all_init_clss T, get_all_init_clss S) \<in> measure (\<lambda>N. card (all_models N))} \<union>
            {(T :: 'v twl_st, S :: 'v twl_st).
               get_conflict S = None \<and> \<not>P (lits_of_l (get_trail S)) \<and>
               (get_conflict T \<noteq> None \<or> P (lits_of_l (get_trail T)))}\<close>

    have wf: \<open>wf R\<close>
      unfolding R_def
      apply (subst Un_commute)
      apply (rule wf_Un)
      subgoal
        by (rule wf_no_loop)
         auto
      subgoal
        by (rule wf_if_measure_in_wf[of \<open>measure (\<lambda>N. card (all_models N))\<close> _ \<open>get_all_init_clss\<close>])
          auto
      subgoal
        by auto
      done
    define I where \<open>I s = (\<exists>x. (s, x) \<in> enum_mod_restriction_st_clss_after \<and>
           (next_model_filtered P)\<^sup>*\<^sup>* (None, snd M) (negate_model_and_add x)  \<and>
           (next_model_filtered P)\<^sup>*\<^sup>* (None, snd M) (None, snd (negate_model_and_add x)) \<and>
           (get_conflict s = None \<longrightarrow> next_model (map lit_of (get_trail s)) (snd x)) \<and>
           (get_conflict s \<noteq> None \<longrightarrow> unsatisfiable (set_mset (snd x))) \<and>
           final_twl_state s)\<close> for s
    let ?Q = \<open>\<lambda>U V s'. cdcl_twl_enum_inv s' \<and> final_twl_state s' \<and> cdcl_twl_stgy\<^sup>*\<^sup>* V s' \<and> (s', U) \<in> R\<close>
    have
      conc_run: \<open>conclusive_TWL_run V \<le> SPEC (?Q U V)\<close>
         (is ?conc_run is \<open>_ \<le> SPEC ?Q\<close>) and
      inv_I: \<open>?Q U V W \<Longrightarrow> I W\<close> (is \<open>_ \<Longrightarrow> ?I\<close>)
      if
        U: \<open>cdcl_twl_enum_inv U\<close> and
        confl: \<open>?Cond U\<close> and
        neg: \<open>negate_model_and_add_twl U V\<close> and
        I_U: \<open>I U\<close>
      for U V W
    proof -
      {
        have \<open>clauses_to_update V = {#}\<close>
          using neg by (auto simp: negate_model_and_add_twl.simps)
        have
          ent_V: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of V)\<close> and
          struct_U: \<open>twl_struct_invs U\<close> and
          ent_U: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of U)\<close>
          using U unfolding cdcl_twl_enum_inv_def
          using neg negate_model_and_add_twl_cdcl\<^sub>W_learned_clauses_entailed_by_init by blast+
        have invs_V: \<open>twl_struct_invs V\<close> \<open>twl_stgy_invs V\<close>
          using U neg unfolding cdcl_twl_enum_inv_def
          using negate_model_and_add_twl_twl_struct_invs negate_model_and_add_twl_twl_stgy_invs
          by blast+
        have [simp]: \<open>get_all_init_clss V = add_mset (DECO_clause (get_trail U))(get_all_init_clss U)\<close>
          using neg by (auto simp: negate_model_and_add_twl.simps)

        have next_mod_U: \<open>next_model (map lit_of (get_trail U)) (get_all_init_clss U)\<close>
          if None: \<open>get_conflict U = None\<close>
        proof (rule cdcl_twl_stgy_final_twl_stateE[of U U])
          show \<open>cdcl_twl_stgy\<^sup>*\<^sup>* U U\<close>
            by simp
          show \<open>final_twl_state U\<close> \<open>twl_struct_invs U\<close> \<open>twl_stgy_invs U\<close>
            \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of U)\<close>
            using U unfolding cdcl_twl_enum_inv_def by blast+
          show ?thesis
            if \<open>get_conflict U \<noteq> None\<close>
            using that None by blast
          show ?thesis
            if
              \<open>get_conflict U = None\<close> and
              \<open>consistent_interp (lits_of_l (get_trail U))\<close> and
              \<open>no_dup (get_trail U)\<close> and
              incl: \<open>atm_of ` lits_of_l (get_trail U) \<subseteq> atms_of_mm (get_all_init_clss U)\<close> and
              \<open>get_trail U \<Turnstile>asm get_all_init_clss U\<close> and
              \<open>satisfiable (set_mset (get_all_init_clss U))\<close>
            using that that(5) unfolding next_model.simps
            by (auto simp: lits_of_def true_annots_true_cls no_dup_map_lit_of)
        qed
        have \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of U)\<close>  and
          decomp: \<open>all_decomposition_implies_m (cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of U))
             (get_all_ann_decomposition (trail (state\<^sub>W_of U)))\<close>
          using struct_U unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
          by fast+

        have \<open>all_models (add_mset ((uminus o lit_of) `# mset (get_trail U)) (get_all_init_clss U)) \<supseteq>
            all_models (add_mset (DECO_clause (get_trail U)) (get_all_init_clss U))\<close>
          if None: \<open>get_conflict U = None\<close>
        proof (rule cdcl_twl_stgy_final_twl_stateE[of U U])
          show \<open>cdcl_twl_stgy\<^sup>*\<^sup>* U U\<close>
            by simp
          show \<open>final_twl_state U\<close> \<open>twl_struct_invs U\<close> \<open>twl_stgy_invs U\<close>
            \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of U)\<close>
            using U unfolding cdcl_twl_enum_inv_def by blast+
          show ?thesis
            if \<open>get_conflict U \<noteq> None\<close>
            using that None by blast
          show ?thesis
            if
              \<open>get_conflict U = None\<close> and
              \<open>consistent_interp (lits_of_l (get_trail U))\<close> and
              \<open>no_dup (get_trail U)\<close> and
              incl: \<open>atm_of ` lits_of_l (get_trail U) \<subseteq> atms_of_mm (get_all_init_clss U)\<close> and
              \<open>get_trail U \<Turnstile>asm get_all_init_clss U\<close> and
              \<open>satisfiable (set_mset (get_all_init_clss U))\<close>
          proof -
            have 1: \<open>I \<Turnstile> {#- lit_of x. x \<in># mset (get_trail U)#}\<close>
              if
                I_U: \<open>I \<Turnstile> DECO_clause (get_trail U)\<close>
              for I
              by (rule true_cls_mono_set_mset[OF _ I_U]) (auto simp: DECO_clause_def)
            have \<open>atms_of (DECO_clause (get_trail U)) \<union> atms_of_mm (get_all_init_clss U) =
               atms_of_mm (get_all_init_clss U)\<close>
              using incl by (auto simp: DECO_clause_def lits_of_def atms_of_def)
            then show ?thesis
              by (auto simp: all_models_def 1)
          qed
        qed
        from card_mono[OF _ this]
        have card_decr: \<open>card (all_models (add_mset (DECO_clause (get_trail U)) (get_all_init_clss U))) <
           card (all_models (get_all_init_clss U))\<close>
          if \<open>get_conflict U = None\<close>
          using next_model_decreasing[OF next_mod_U] that by (auto simp: finite_all_models)

        {
          fix WW
          assume star: \<open>cdcl_twl_stgy\<^sup>*\<^sup>* V WW\<close> and final: \<open>final_twl_state WW\<close>
          have ent_W: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of WW)\<close>
            using U ent_V neg invs_V rtranclp_cdcl_twl_stgy_cdcl\<^sub>W_learned_clauses_entailed_by_init
              star
            unfolding cdcl_twl_enum_inv_def by blast
          then have H1: \<open>cdcl_twl_enum_inv WW\<close>
            using star final invs_V unfolding cdcl_twl_enum_inv_def
            using rtranclp_cdcl_twl_stgy_twl_stgy_invs rtranclp_cdcl_twl_stgy_twl_struct_invs by blast
          have init_clss_WW_V[simp]: \<open>get_all_init_clss WW = get_all_init_clss V\<close>
            by (metis rtranclp_cdcl_twl_stgy_all_learned_diff_learned star)

          have next_mod: \<open>next_model (map lit_of (get_trail WW)) (get_all_init_clss WW)\<close>
            if None: \<open>get_conflict WW = None\<close>
            using invs_V ent_V
          proof (rule cdcl_twl_stgy_final_twl_stateE[OF star final])
            show ?thesis
              if \<open>get_conflict WW \<noteq> None\<close>
              using that None by blast
            show ?thesis
              if
                \<open>get_conflict WW = None\<close> and
                \<open>consistent_interp (lits_of_l (get_trail WW))\<close> and
                \<open>no_dup (get_trail WW)\<close> and
                \<open>atm_of ` lits_of_l (get_trail WW) \<subseteq> atms_of_mm (get_all_init_clss WW)\<close> and
                \<open>get_trail WW \<Turnstile>asm get_all_init_clss V\<close> and
                \<open>satisfiable (set_mset (get_all_init_clss V))\<close>
              using that that(5) unfolding next_model.simps
              by (auto simp: lits_of_def true_annots_true_cls no_dup_map_lit_of)
          qed
          have not_none_unsat: \<open>unsatisfiable (set_mset (get_all_init_clss V))\<close>
            if None: \<open>get_conflict WW \<noteq> None\<close>
            using invs_V ent_V
          proof (rule cdcl_twl_stgy_final_twl_stateE[OF star final])
            show ?thesis
              if \<open>unsatisfiable (set_mset (get_all_init_clss V))\<close>
              using that None by blast
            show ?thesis
              if
                \<open>get_conflict WW = None\<close>
              using that None unfolding next_model.simps
              by (auto simp: lits_of_def true_annots_true_cls no_dup_map_lit_of)
          qed
          have H2: \<open>(WW, U) \<in> R\<close>
            using confl card_decr unfolding R_def by (auto)
          note H1 H2 next_mod init_clss_WW_V not_none_unsat
        } note H = this(1,2) and next_mod = this(3) and init_clss_WW_V = this(4) and
          not_none_unsat = this(5)

       {
         assume \<open>?Q W\<close>
         then have
           twl_enum: \<open>cdcl_twl_enum_inv W\<close> and
           final: \<open>final_twl_state W\<close> and
           st: \<open>cdcl_twl_stgy\<^sup>*\<^sup>* V W\<close> and
           W_U: \<open>(W, U) \<in> R\<close>
           by blast+
         obtain U' where
           U_U': \<open>(U, U') \<in> enum_mod_restriction_st_clss_after\<close> and
           st_M_U': \<open>(next_model_filtered P)\<^sup>*\<^sup>* (None, snd M) (negate_model_and_add U')\<close>
           using I_U unfolding I_def by blast

         have 1: \<open>{unmark L |L. is_decided L \<and> L \<in> set (trail (state\<^sub>W_of U))} =
                    CNot (DECO_clause (get_trail U))\<close>
           by (force simp: DECO_clause_def twl_st CNot_def)
         have ent3_gnerealise: \<open>A \<union> B \<union> C \<Turnstile>ps D \<Longrightarrow> A \<Turnstile>ps B \<Longrightarrow> A \<union> C \<Turnstile>ps D\<close> for A B C D
           by (metis Un_absorb inf_sup_aci(5) true_clss_clss_def
               true_clss_clss_generalise_true_clss_clss)

         have \<open>set_mset (cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of U)) \<union>
                CNot (DECO_clause (get_trail U)) \<Turnstile>ps unmark_l (trail (state\<^sub>W_of U))\<close>
           using all_decomposition_implies_propagated_lits_are_implied[OF decomp]
           unfolding 1 .
         then have 2: \<open>set_mset (get_all_init_clss U) \<union> CNot (DECO_clause (get_trail U)) \<Turnstile>ps
              unmark_l (trail (state\<^sub>W_of U))\<close>
           using ent_U unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def
             cdcl\<^sub>W_restart_mset.clauses_def
           by (auto simp: clauses_def twl_st intro: ent3_gnerealise)
         have [simp]: \<open>unmark_l (get_trail U) = CNot {#- lit_of x. x \<in># mset (get_trail U)#}\<close>
           by (force simp: CNot_def)
         have mod_U: \<open>mod_restriction (get_all_init_clss U) (snd U')\<close> and
           atms_U_U': \<open>atms_of_mm (get_all_init_clss U) = atms_of_mm (snd U')\<close>
           using U_U' confl unfolding enum_mod_restriction_st_clss_after_def by (cases U'; auto; fail)+
         have alien_U: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of U)\<close>
           using \<open>twl_struct_invs U\<close>
           unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
           by fast
         have mod_restriction_H: \<open>M \<Turnstile> DECO_clause (get_trail U)\<close>
           if
             total: \<open>total_over_m M (set_mset (snd U'))\<close> and
             consistent: \<open>consistent_interp M\<close> and
             M_tr: \<open>M \<Turnstile> {#- lit_of x. x \<in># mset (get_trail U)#}\<close> and
             M_U': \<open>M \<Turnstile>m snd U'\<close>
           for M
         proof (rule ccontr)
           assume \<open>\<not>?thesis\<close>
           moreover have tot_tr: \<open>total_over_m M {DECO_clause (get_trail U)}\<close>
             using alien_U total atms_U_U' unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def
             apply (auto simp: twl_st image_iff total_over_m_alt_def lits_of_def
                 dest!: atms_of_DECO_clauseD(1))
             apply (metis atms_of_s_def contra_subsetD image_iff in_atms_of_s_decomp)+
             done
           ultimately have \<open>M \<Turnstile>s CNot (DECO_clause (get_trail U))\<close>
             by (simp add: total_not_true_cls_true_clss_CNot)
           moreover have \<open>M \<Turnstile>sm get_all_init_clss U\<close>
             using mod_U total consistent M_U' unfolding mod_restriction_def
             by blast
           moreover have \<open>total_over_m M (set_mset (get_all_init_clss U))\<close>
             using total atms_U_U' by (simp add: total_over_m_def)
           moreover have \<open>total_over_m M (unmark_l (trail (state\<^sub>W_of U)))\<close>
             using alien_U tot_tr total atms_U_U' unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def
             apply (auto simp: total_over_m_alt_def
                  twl_st dest: atms_of_DECO_clauseD)
             by (metis atms_of_uminus_lit_atm_of_lit_of atms_of_uminus_lit_of lits_of_def
                 set_mset_mset subsetCE total total_over_m_def total_over_set_def)
           ultimately have \<open>M \<Turnstile>s unmark_l (trail (state\<^sub>W_of U))\<close>
             using 2 total consistent tot_tr unfolding true_clss_clss_def
             by auto
           then show False
             using M_tr tot_tr consistent
             by (auto simp: true_clss_def twl_st true_cls_def consistent_interp_def)
         qed
         have \<open>mod_restriction (get_all_init_clss U) (snd U')\<close>
           using U_U' confl unfolding enum_mod_restriction_st_clss_after_def
           by auto
         moreover have \<open>M \<Turnstile> {#- lit_of x. x \<in># mset (get_trail U)#}\<close>
           if \<open>M \<Turnstile> DECO_clause (get_trail U)\<close> for M
           by (rule true_cls_mono_set_mset[OF _ that]) (auto simp: DECO_clause_def)
         ultimately have mod_rest_U:
           \<open>mod_restriction (add_mset (DECO_clause (get_trail U)) (get_all_init_clss U))
              (add_mset {#- lit_of x. x \<in># mset (get_trail U)#} (snd U'))\<close>
           using 2
           by (auto simp: mod_restriction_def twl_st mod_restriction_H)
         have \<open>(next_model_filtered P) (negate_model_and_add U')
               ((negate_model_and_add (Some (map lit_of (get_trail U)), snd U')))\<close>
           using confl U_U'
           apply (cases U'; cases \<open>fst U'\<close>)
           apply (auto simp: enum_mod_restriction_st_clss_after_def lits_of_def
               eq_commute[of _ \<open>mset _\<close>] next_model_filtered.simps
               intro!: exI[of _ \<open>map lit_of (get_trail U)\<close>]
               dest: mset_eq_setD)
            defer
            apply (metis list.set_map mset_eq_setD mset_map)
           using next_mod_U by (auto dest: mod_restriction_next_modelD)
         then have \<open>(next_model_filtered P)\<^sup>*\<^sup>* (None, snd M)
               ((negate_model_and_add (Some (map lit_of (get_trail U)), snd U')))\<close>
           using st_M_U' by simp
         moreover {
            have \<open>mod_restriction (add_mset {#} (get_all_init_clss W))
                 (add_mset {#- lit_of x. x \<in># mset (get_trail W)#}
                     (add_mset {#- lit_of x. x \<in># mset (get_trail U)#} (snd U')))\<close>
              if
                confl: \<open>get_conflict W = None\<close> and
                count_dec: \<open>count_decided (get_trail W) = 0\<close>
              apply (rule final_level0_add_empty_clause[OF that])
              using \<open>cdcl_twl_enum_inv W \<and> final_twl_state W \<and> cdcl_twl_stgy\<^sup>*\<^sup>* V W \<and>
                 (W, U) \<in> R\<close> mod_rest_U init_clss_WW_V[OF st final] U_U' atms_U_U' alien_U
              unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def
              by (auto dest: atms_of_DECO_clauseD(2) simp: twl_st lits_of_def)
               (auto simp: image_image atms_of_def)
           then have W: \<open>(W, (negate_model_and_add (Some (map lit_of (get_trail U)), snd U')))
                \<in> enum_mod_restriction_st_clss_after\<close>
             using confl init_clss_WW_V[OF st final] twl_enum alien_U atms_U_U' confl
             apply (auto simp: enum_mod_restriction_st_clss_after_def lits_of_def
                 cdcl_twl_enum_inv_def mod_rest_U
                 dest: atms_of_DECO_clauseD)
             defer
             apply (smt U atms_of_def cdcl_twl_enum_inv_def cdcl_twl_stgy_final_twl_stateE contra_subsetD
                 lits_of_def rtranclp.intros(1) set_image_mset set_mset_mset)
             done
          } note W = this
         moreover have \<open>get_conflict W = None \<Longrightarrow> 0 < count_decided (get_trail W) \<Longrightarrow>
             next_model (map lit_of (get_trail W))
              (add_mset {#- lit_of x. x \<in># mset (get_trail U)#} (snd U'))\<close>
           using W next_mod[OF st] final confl unfolding enum_mod_restriction_st_clss_after_def
           by (auto simp: mod_restriction_def next_model.simps lits_of_def)
         moreover have \<open>get_conflict W = None \<Longrightarrow> count_decided (get_trail W) = 0 \<Longrightarrow>
             next_model (map lit_of (get_trail W))
              (add_mset {#- lit_of x. x \<in># mset (get_trail U)#} (snd U'))\<close>
           using W next_mod[OF st] final confl unfolding enum_mod_restriction_st_clss_after_def
           apply (subst (asm)(2) mod_restriction_def)
           by (auto simp: mod_restriction_def next_model.simps lits_of_def)
         moreover have \<open>get_conflict W \<noteq> None \<Longrightarrow>
             unsatisfiable (set_mset (add_mset {#- lit_of x. x \<in># mset (get_trail U)#} (snd U')))\<close>
           using W not_none_unsat[OF st] final confl mod_rest_U unfolding enum_mod_restriction_st_clss_after_def
           by (auto simp: lits_of_def dest: mod_restriction_satisfiable_iff
                split: if_splits)
         ultimately have ?I
           using final next_mod[OF st]
           unfolding I_def
           apply -
           apply (rule exI[of _ \<open>(negate_model_and_add (Some (map lit_of (get_trail U)), snd U'))\<close>])
           using confl
           by (auto simp: lits_of_def)
        } note I = this
        note H and I
      } note H = this(1,2) and I = this(3)
      then show ?conc_run
        by (auto simp add: conclusive_TWL_run_def)


      show ?I if \<open>?Q W\<close>
        using I that
        by (auto simp: I_def)
    qed
    have neg_neg[simp]: \<open>negate_model_and_add (negate_model_and_add M) = negate_model_and_add M\<close>
      by (cases M; cases \<open>fst M\<close>; auto)
    have [simp]: \<open>(T, a, b) \<in> enum_model_st_direct \<Longrightarrow> (T, None, b) \<in> enum_mod_restriction_st_clss_after\<close>
      for a b
      unfolding enum_model_st_direct_def enum_mod_restriction_st_clss_after_def
        cdcl_twl_enum_inv_def
      by (auto intro!: final_level0_add_empty_clause simp: cdcl_twl_enum_inv_def)
    have I_T: \<open>I T\<close>
      unfolding I_def
      apply (rule exI[of _ \<open>(None, snd M)\<close>])
      unfolding neg_neg
      apply (intro conjI)
      subgoal
        using T by (cases M) auto
      subgoal by (auto simp: enum_mod_restriction_st_clss_after_def cdcl_twl_enum_inv_def
          enum_model_st_def enum_model_st_direct_def)
      subgoal by (auto simp: enum_mod_restriction_st_clss_after_def cdcl_twl_enum_inv_def
          enum_model_st_def enum_model_st_direct_def)
      subgoal using T by (auto simp: enum_mod_restriction_st_clss_after_def cdcl_twl_enum_inv_def
          enum_model_st_def enum_model_st_direct_def)
      subgoal using T by (auto simp: enum_mod_restriction_st_clss_after_def cdcl_twl_enum_inv_def
          enum_model_st_def enum_model_st_direct_def)
      subgoal using T by (auto simp: enum_mod_restriction_st_clss_after_def cdcl_twl_enum_inv_def
          enum_model_st_def enum_model_st_direct_def)
      done
    have final: \<open>?Spec s\<close>
      if
        I: \<open>I s\<close> and
        cond: \<open>\<not> (?Cond s)\<close> and
        enum: \<open>cdcl_twl_enum_inv s\<close>
      for s
    proof -
      obtain x where
         sx: \<open>(s, x) \<in> enum_mod_restriction_st_clss_after\<close> and
         st': \<open>(next_model_filtered P)\<^sup>*\<^sup>* (None, snd M) (None, snd (negate_model_and_add x))\<close> and
         st: \<open>(next_model_filtered P)\<^sup>*\<^sup>* (None, snd M) (negate_model_and_add x)\<close> and
         final: \<open>final_twl_state s\<close> and
         nm: \<open>get_conflict s = None \<Longrightarrow> next_model (map lit_of (get_trail s)) (snd x)\<close> and
         unsat: \<open>get_conflict s \<noteq> None \<Longrightarrow> unsatisfiable (set_mset (snd x))\<close>
        using I unfolding I_def by meson
      let ?x = \<open>if get_conflict s = None
          then (Some (map lit_of (get_trail s)), snd x)
          else (None, snd x)\<close>
      let ?y = \<open>negate_model_and_add ?x\<close>
      have step: \<open>(next_model_filtered P) (None, snd (negate_model_and_add x)) ?y\<close>
        if \<open>get_conflict s = None\<close> and \<open>P (lits_of_l (get_trail s))\<close>
        using cond that sx final nm unfolding enum_mod_restriction_st_clss_after_def
          enum_model_st_def
        by (cases x; cases \<open>fst x\<close>)
          (auto simp: next_model_filtered.simps lits_of_def
            conclusive_TWL_run_def conc_fun_RES
            intro!: exI[of _ \<open>map lit_of (get_trail s)\<close>])
      moreover have step: \<open>(next_model_filtered P)\<^sup>*\<^sup>* (negate_model_and_add x) ?y\<close>
        if \<open>get_conflict s \<noteq> None\<close>
        using cond that sx unfolding enum_mod_restriction_st_clss_after_def
            enum_model_st_def
        by (cases x; cases \<open>fst x\<close>)
          (auto simp: next_model_filtered.simps lits_of_def)
      moreover have step: \<open>(next_model_filtered P) (negate_model_and_add x) ?y \<or>
         (negate_model_and_add x) = ?y\<close>
        if \<open>get_conflict s = None\<close> and \<open>\<not>P (lits_of_l (get_trail s))\<close>
        using cond that sx nm unfolding enum_mod_restriction_st_clss_after_def
          enum_model_st_def
        apply (cases x; cases \<open>fst x\<close>)
        by (auto simp: next_model_filtered.simps lits_of_def
            conclusive_TWL_run_def conc_fun_RES
            intro!: exI[of _ \<open>map lit_of (get_trail s)\<close>])
      ultimately have st: \<open>(next_model_filtered P)\<^sup>*\<^sup>* (None, snd M) ?y\<close>
        using st st' by force
      have 1: \<open>(s,  ?x) \<in> enum_mod_restriction_st_clss_after\<close>
        if \<open>count_decided (get_trail s) \<noteq> 0 \<or> get_conflict s \<noteq> None \<or> P (lit_of ` set (get_trail s))\<close>
        using sx cond nm that unfolding enum_mod_restriction_st_clss_after_def
            enum_model_st_def
        by (cases x; cases \<open>fst x\<close>) (auto simp: lits_of_def)
      have unsat': \<open>unsatisfiable (set_mset (add_mset {#- lit_of x. x \<in># mset (get_trail s)#} (snd x)))\<close>
        if \<open>get_conflict s = None\<close> and \<open>count_decided (get_trail s) = 0\<close> and
           \<open>\<not>P (lit_of ` set (get_trail s))\<close>
        apply (rule final_level0_add_empty_clause_unsat)
        using cond that sx nm enum unfolding enum_mod_restriction_st_clss_after_def
          enum_model_st_def apply -
        by (cases x; cases \<open>fst x\<close>)
          (force simp: next_model_filtered.simps lits_of_def)+
      have \<open>no_step (next_model_filtered P) ?y\<close>
        apply (rule unsat_no_step_next_model_filtered')
        apply (cases x; cases \<open>fst x\<close>)
        using cond unsat nm unsat' that
        by (auto simp: lits_of_def)
      then have 2: \<open>full (next_model_filtered P) (None, snd M) ?y\<close>
        using st that unfolding full_def by blast
      have "1b": \<open>count_decided (get_trail s) = 0 \<Longrightarrow>
    \<not> P (lit_of ` set (get_trail s)) \<Longrightarrow>
    get_conflict s = None \<Longrightarrow>
    (s, None, snd x) \<in> enum_mod_restriction_st_clss_after\<close>
        using that cond unsat nm unsat' sx
        unfolding enum_mod_restriction_st_clss_after_def
        by (cases x; cases \<open>fst x\<close>) auto
      show ?thesis
        apply (rule exI[of _ \<open>?y\<close>])
        using 1 "1b" 2 cond by (auto simp: lits_of_def)
    qed
    show ?thesis
      apply (refine_vcg WHILEIT_rule_stronger_inv[where R=\<open>R\<close> and I' = I] conc_run)
      subgoal by (rule wf)
      subgoal
        using T S unfolding enum_model_st_direct_def enum_mod_restriction_st_clss_def
          cdcl_twl_enum_inv_def
        by auto
      subgoal by (rule I_T)
      apply assumption
      subgoal by fast
      subgoal by fast
      subgoal by fast
      subgoal by fast
      subgoal by fast
      subgoal by fast
      subgoal for U V W by (rule inv_I)
      subgoal by fast
      subgoal by (rule final)
      done
  qed
  have H1: \<open>(if count_decided (get_trail Sb) = 0 then P (lits_of_l (get_trail Sb)) else True,
            fst x' \<noteq> None) \<in> bool_rel\<close>
    if
      \<open>case y of (M, N) \<Rightarrow> M = None\<close> and
      \<open>(Sb, x') \<in> ?Res\<close> and
      \<open>x' \<in> Collect (full (next_model_filtered P) (None, snd Sa))\<close> and
      \<open>get_conflict Sb = None\<close>
    for x x' Sa Sb S y
    using that (* TODO Proof *)
    by (auto simp: enum_mod_restriction_st_clss_after_def enum_model_st_def
        enum_mod_restriction_st_clss_def lits_of_def)
  have H2: \<open>(False, fst x' \<noteq> None) \<in> bool_rel\<close>
    if
      \<open>case y of (M, N) \<Rightarrow> M = None\<close> and
      \<open>(Sb, x') \<in> ?Res\<close> and
      \<open>x' \<in> Collect (full (next_model_filtered P) (None, snd Sa))\<close> and
      \<open>get_conflict Sb \<noteq> None\<close>
    for x x' Sa Sb S y
    using that
    by (auto simp: enum_mod_restriction_st_clss_after_def enum_model_st_def
        enum_mod_restriction_st_clss_def lits_of_def)
  show ?thesis
    supply if_splits[split]
    unfolding cdcl_twl_enum_def
    apply (intro frefI nres_relI)
    apply (subst next_model_filtered_nres_alt_def)
    subgoal by auto
    apply (refine_vcg conclusive_run)
    unfolding conc_fun_SPEC
      apply (rule loop; assumption)
     apply (rule H1; assumption)
    apply (rule H2; assumption)
    done
qed

end

end
