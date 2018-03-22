theory Watched_Literals_Algorithm_Enumeration
  imports Watched_Literals_Algorithm Watched_Literals_Transition_System_Enumeration
begin

definition cdcl_twl_enum_inv :: \<open>'v twl_st \<Rightarrow> bool\<close> where
  \<open>cdcl_twl_enum_inv S \<longleftrightarrow> twl_struct_invs S \<and> twl_stgy_invs S \<and> final_twl_state S \<and>
         cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S)\<close>

definition equisatisfiable :: \<open>'v clauses \<Rightarrow> 'v clauses \<Rightarrow> bool\<close> where
\<open>equisatisfiable N N' \<longleftrightarrow> (\<forall>M. M \<Turnstile>sm N \<longleftrightarrow> M \<Turnstile>sm N')\<close>

lemma equisatisfiable_satisfiable_iff:
  \<open>equisatisfiable M M' \<Longrightarrow> satisfiable (set_mset M) \<longleftrightarrow> satisfiable (set_mset M')\<close>
  by (auto simp: equisatisfiable_def satisfiable_carac[symmetric])


definition enum_equisatisfiable_st_clss :: \<open>('v twl_st \<times> ('v literal list option \<times> 'v clauses)) set\<close> where
  \<open>enum_equisatisfiable_st_clss = {(S, (M, N)). equisatisfiable (get_all_init_clss S) N \<and>
      twl_struct_invs S \<and> twl_stgy_invs S \<and> clauses_to_update S = {#} \<and>
      literals_to_update S = {#} \<and>
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S) \<and>
      atms_of_mm (get_all_init_clss S) = atms_of_mm N}\<close>


definition enum_model_st_direct :: \<open>('v twl_st \<times> ('v literal list option \<times> 'v clauses)) set\<close> where
  \<open>enum_model_st_direct = {(S, (M, N)).
         equisatisfiable (get_all_init_clss S) N \<and>
         (get_conflict S = None \<longrightarrow> M \<noteq> None \<and> lits_of_l (get_trail S) = set (the M)) \<and>
         (get_conflict S \<noteq> None \<longrightarrow> M = None) \<and>
         atms_of_mm (get_all_init_clss S) = atms_of_mm N \<and>
         (get_conflict S = None \<longrightarrow> next_model (map lit_of (get_trail S)) N) \<and>
         cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S) \<and>
         cdcl_twl_enum_inv S}\<close>

definition enum_model_st :: \<open>('v twl_st \<times> ('v literal list option \<times> 'v clauses)) set\<close> where
  \<open>enum_model_st = {(S, (M, N)).
         equisatisfiable (add_mset (DECO_clause (get_trail S)) (get_all_init_clss S)) N \<and>
         (get_conflict S = None \<longrightarrow> M \<noteq> None \<and> lits_of_l (get_trail S) = set (the M)) \<and>
         (get_conflict S \<noteq> None \<longrightarrow> M = None)}\<close>


fun add_to_init_cls :: \<open>'v twl_cls \<Rightarrow> 'v twl_st \<Rightarrow> 'v twl_st\<close> where
  \<open>add_to_init_cls C (M, N, U, D, NE, UE, WS, Q) = (M, add_mset C N, U, D, NE, UE, WS, Q)\<close>

(* TODO Move *)
lemma [twl_st]:
  \<open>init_clss (state\<^sub>W_of T) = get_all_init_clss T\<close>
  \<open>learned_clss (state\<^sub>W_of T) = get_all_learned_clss T\<close>
  by (cases T; auto simp: cdcl\<^sub>W_restart_mset_state; fail)+

lemma total_over_m_alt_def: \<open>total_over_m I S \<longleftrightarrow> atms_of_ms S \<subseteq> atms_of_s I\<close>
  by (auto simp: total_over_m_def total_over_set_def)
(* End Move *)

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
     (if P (set M) then (Some M, N) else (None, add_mset (uminus `# mset M) N))\<close> |
  \<open>negate_model_and_add (None, N) = (None, N)\<close>

definition cdcl_twl_enum :: \<open>'v twl_st \<Rightarrow> 'v twl_st nres\<close> where
  \<open>cdcl_twl_enum S = do {
     S \<leftarrow> conclusive_TWL_run S;
     WHILE\<^sub>T\<^bsup>cdcl_twl_enum_inv\<^esup>
       (\<lambda>S. get_conflict S = None \<and> P (lits_of_l (get_trail S)))
       (\<lambda>S. do {
             S \<leftarrow> SPEC (negate_model_and_add_twl S);
             conclusive_TWL_run S
           })
       S
    }\<close>

definition next_model_filtered_nres where
  \<open>next_model_filtered_nres N =
    SPEC (\<lambda>M. full (next_model_filtered P) N M)\<close>

(* TODO move *)
lemma no_step_next_model_filtered_next_model_iff:
  \<open>fst S = None \<Longrightarrow> no_step (next_model_filtered P) S \<longleftrightarrow> (\<nexists>M. next_model M (snd S))\<close>
  apply (cases S; auto simp: next_model_filtered.simps)
  by metis

lemma Ex_next_model_iff_statisfiable:
  \<open>(\<exists>M. next_model M N) \<longleftrightarrow> satisfiable (set_mset N)\<close>
  by (metis Watched_Literals_Algorithm_Enumeration.no_step_next_model_filtered_next_model_iff
      next_model.cases no_step_next_model_filtered_unsat prod.sel(1) prod.sel(2) satisfiable_carac')


lemma unsatisfiable_mono:
  \<open>N \<subseteq> N' \<Longrightarrow> unsatisfiable N \<Longrightarrow> unsatisfiable N'\<close>
  by (metis (full_types) satisfiable_decreasing subset_Un_eq)

lemma no_step_full_iff_eq:
  \<open>no_step R S \<Longrightarrow> full R S T \<longleftrightarrow> S = T\<close>
  unfolding full_def
  by (meson rtranclp.rtrancl_refl rtranclpD tranclpD)

lemma no_dup_map_lit_of: \<open>no_dup M \<Longrightarrow> distinct (map lit_of M)\<close>
  apply (induction M)
   apply (auto simp: dest: no_dup_imp_distinct)
  by (meson distinct.simps(2) no_dup_cons no_dup_imp_distinct)

lemma cdcl_twl_stgy_cdcl\<^sub>W_learned_clauses_entailed_by_init:
  assumes
    \<open>cdcl_twl_stgy S s\<close> and
    \<open>twl_struct_invs S\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S)\<close>
  shows 
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of s)\<close>
  by (meson assms cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_learned_clauses_entailed
      cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W_restart
      cdcl_twl_stgy_cdcl\<^sub>W_stgy twl_struct_invs_def)

lemma rtranclp_cdcl_twl_stgy_cdcl\<^sub>W_learned_clauses_entailed_by_init:
  assumes
    \<open>cdcl_twl_stgy\<^sup>*\<^sup>* S s\<close> and
    \<open>twl_struct_invs S\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S)\<close>
  shows 
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of s)\<close>
  using assms 
  by (induction rule: rtranclp_induct)
    (auto intro: cdcl_twl_stgy_cdcl\<^sub>W_learned_clauses_entailed_by_init
      rtranclp_cdcl_twl_stgy_twl_struct_invs)

lemma negate_model_and_add_twl_cdcl\<^sub>W_learned_clauses_entailed_by_init:
  assumes
    \<open>negate_model_and_add_twl S s\<close> and
    \<open>twl_struct_invs S\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S)\<close>
  shows 
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of s)\<close>
  using assms
  by (induction rule: negate_model_and_add_twl.induct)
     (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def
      cdcl\<^sub>W_restart_mset_state)

lemma true_cls_mset_add_mset[iff]: "I \<Turnstile>m add_mset C CC \<longleftrightarrow> I \<Turnstile> C \<and> I \<Turnstile>m CC"
  unfolding true_cls_mset_def by auto

lemma \<open>A \<union> CNot B \<Turnstile>ps C \<longleftrightarrow> A \<Turnstile>ps {B} \<union> C\<close>
  apply (auto simp: true_clss_clss_def)
  
(*  set_mset (init_clss (state\<^sub>W_of U)) \<union> set_mset (learned_clss (state\<^sub>W_of U)) \<union> CNot (DECO_clause (get_trail U)) \<Turnstile>ps unmark_l (trail (state\<^sub>W_of U)) \<Longrightarrow>
    init_clss (state\<^sub>W_of U) \<Turnstile>psm learned_clss (state\<^sub>W_of U) \<Longrightarrow> set_mset (get_all_init_clss U) \<union> CNot (DECO_clause (get_trail U)) \<Turnstile>ps unmark_l (trail (state\<^sub>W_of U))
 *)
(* End Move *)

lemma
  \<open>(cdcl_twl_enum, next_model_filtered_nres) \<in>
    [\<lambda>(M, N). M = None]\<^sub>f enum_equisatisfiable_st_clss \<rightarrow> \<langle>enum_model_st\<rangle>nres_rel\<close>
proof -
  define model_if_exists where
    \<open>model_if_exists S \<equiv> \<lambda>M.
      (if \<exists>M. next_model M (snd S)
       then (fst M \<noteq> None \<and> next_model (the (fst M)) (snd S) \<and> snd M = snd S)
       else (fst M = None \<and> M = S))\<close>
  for S :: \<open>_ \<times> 'v clauses\<close>

  have \<open>full (next_model_filtered P) S U \<longleftrightarrow>
         (\<exists>T. model_if_exists S T \<and> full (next_model_filtered P) (negate_model_and_add T) U)\<close>
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
        have \<open>no_step (next_model_filtered P) (negate_model_and_add S)\<close>
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
        then have \<open>full (next_model_filtered P) (negate_model_and_add S) U\<close>
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
      have \<open>model_if_exists S ?T\<close>
        using M T that unfolding model_if_exists_def
        by (cases S) auto
      moreover have \<open>full (next_model_filtered P) (negate_model_and_add ?T) U\<close>
        using s1(2) T
        by (auto split: if_splits)
      ultimately show ?B
        by blast
    qed
  next
    assume ?B
    then show ?A
      apply (auto simp: model_if_exists_def full1_is_full full_fullI split: if_splits
          dest: )
       apply (metis full1_is_full full_fullI next_model_filtered.intros(1) prod.exhaust_sel that)
      by (metis full1_is_full full_fullI next_model_filtered.intros(2) prod.exhaust_sel that)
  qed
  then have next_model_filtered_nres_alt_def: \<open>next_model_filtered_nres S  = do {
         S \<leftarrow> SPEC (model_if_exists S);
         SPEC (\<lambda>T. full (next_model_filtered P) (negate_model_and_add S) T)
       }\<close> if \<open>fst S = None\<close> for S
    using that
    unfolding next_model_filtered_nres_def (* model_if_exists_def *) RES_RES_RETURN_RES
    by blast
  have conclusive_run: \<open>conclusive_TWL_run S
      \<le> \<Down> enum_model_st_direct
          (SPEC (model_if_exists MN))\<close>
    if
      S_MN: \<open>(S, MN) \<in> enum_equisatisfiable_st_clss\<close> and
      M: \<open>case MN of (M, N) \<Rightarrow> M = None\<close>
    for S MN
  proof -
    have H: \<open>\<exists>s'\<in>Collect (model_if_exists MN).
         (s, s') \<in> enum_model_st_direct\<close>
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
        using S_MN unfolding enum_equisatisfiable_st_clss_def by blast
      moreover have stgy_S: \<open>twl_stgy_invs S\<close>
        using S_MN unfolding enum_equisatisfiable_st_clss_def by blast
      moreover have ent: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S)\<close>
        using S_MN unfolding enum_equisatisfiable_st_clss_def by blast
      then have ent_s: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of s)\<close>
        using rtranclp_cdcl_twl_stgy_cdcl\<^sub>W_learned_clauses_entailed_by_init star struct_S by blast
      then have enum_inv: \<open>cdcl_twl_enum_inv s\<close>
        using star S_MN final unfolding enum_equisatisfiable_st_clss_def cdcl_twl_enum_inv_def
        by (auto intro: rtranclp_cdcl_twl_stgy_twl_struct_invs
            rtranclp_cdcl_twl_stgy_twl_stgy_invs)
      show ?thesis
        using struct_S stgy_S ent
      proof (rule cdcl_twl_stgy_final_twl_stateE[OF star final])
        assume
          confl: \<open>get_conflict s \<noteq> None\<close> and
          unsat: \<open>unsatisfiable (set_mset (get_all_init_clss S))\<close>
        let ?s = \<open>(None, snd MN)\<close>
        have \<open>(s, ?s) \<in> enum_model_st_direct\<close>
          using S_MN confl unsat enum_inv ent star unfolding enum_model_st_def
          by (auto simp: enum_model_st_direct_def enum_equisatisfiable_st_clss_def
              intro: rtranclp_cdcl_twl_stgy_cdcl\<^sub>W_learned_clauses_entailed_by_init)
        moreover have \<open>model_if_exists MN ?s\<close>
          using unsat S_MN unsat_no_step_next_model_filtered[of N P] Ex_next_model_iff_statisfiable[of N]
          unfolding model_if_exists_def
          by (auto simp: enum_equisatisfiable_st_clss_def
                equisatisfiable_satisfiable_iff)
        ultimately show \<open>\<exists>s'\<in>Collect (model_if_exists MN). (s, s') \<in> enum_model_st_direct\<close>
            apply -
          by (rule bexI[of _ \<open>?s\<close>]) auto
      next
        let ?s = \<open>(Some (map lit_of (get_trail s)), N)\<close>
        assume
          \<open>get_conflict s = None\<close> and
          cons: \<open>consistent_interp (lits_of_l (get_trail s))\<close> and
          ent: \<open>get_trail s \<Turnstile>asm get_all_init_clss S\<close> and
          \<open>satisfiable (set_mset (get_all_init_clss S))\<close> and
          n_d: \<open>no_dup (get_trail s)\<close> and
          alien: \<open>atm_of ` (lits_of_l (get_trail s)) \<subseteq> atms_of_mm (get_all_init_clss s)\<close>
        moreover have nm: \<open>next_model (map lit_of (get_trail s)) N\<close>
          using ent cons n_d S_MN alien
          by (auto simp: next_model.simps true_annots_true_cls lits_of_def
              no_dup_map_lit_of enum_equisatisfiable_st_clss_def equisatisfiable_def)
        ultimately have \<open>(s, ?s) \<in> enum_model_st_direct\<close>
          using S_MN enum_inv star ent unfolding enum_model_st_direct_def
          by (auto simp: equisatisfiable_satisfiable_iff next_model.simps
              enum_equisatisfiable_st_clss_def lits_of_def
              rtranclp_cdcl_twl_stgy_cdcl\<^sub>W_learned_clauses_entailed_by_init)
        moreover have \<open>model_if_exists (None, N) (Some (map lit_of (get_trail s)), N)\<close>
            using nm by (auto simp: model_if_exists_def
                enum_equisatisfiable_st_clss_def
                equisatisfiable_satisfiable_iff)
        ultimately show \<open>\<exists>s'\<in>Collect (model_if_exists MN). (s, s') \<in> enum_model_st_direct\<close>
          apply -
          by (rule bexI[of _ \<open>(Some (map lit_of (get_trail s)), snd MN)\<close>])
            auto
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
  have \<open>WHILE\<^sub>T\<^bsup>cdcl_twl_enum_inv\<^esup>
       (\<lambda>S. get_conflict S = None \<and>
             P (lits_of_l (get_trail S)))
       (\<lambda>S. SPEC (negate_model_and_add_twl S) \<bind>
             conclusive_TWL_run) T
      \<le> SPEC
          (\<lambda>y. \<exists>x. (y, x) \<in> enum_model_st \<and>
                    full (next_model_filtered P)
                     (negate_model_and_add M) x)\<close>
    if 
      \<open>case MN of (M, N) \<Rightarrow> M = None\<close> and
      S: \<open>(S, MN) \<in> enum_equisatisfiable_st_clss\<close> and
      T: \<open>(T, M) \<in> enum_model_st_direct\<close> and
      \<open>M \<in> Collect (model_if_exists MN)\<close>
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
    have \<open>conclusive_TWL_run V \<le> SPEC (\<lambda>s'. cdcl_twl_enum_inv s' \<and> (s', U) \<in> R)\<close>
      if 
        U: \<open>cdcl_twl_enum_inv U\<close> and
        confl: \<open>get_conflict U = None \<and> \<not>P (lits_of_l (get_trail U))\<close> and
        neg: \<open>negate_model_and_add_twl U V\<close>
      for U V
    proof -
      { fix W
        assume star: \<open>cdcl_twl_stgy\<^sup>*\<^sup>* V W\<close> and final: \<open>final_twl_state W\<close>
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
          using negate_model_and_add_twl_twl_struct_invs  negate_model_and_add_twl_twl_stgy_invs
          by blast+
        moreover have ent_W: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of W)\<close>
          using U ent_V neg invs_V rtranclp_cdcl_twl_stgy_cdcl\<^sub>W_learned_clauses_entailed_by_init
            star
          unfolding cdcl_twl_enum_inv_def by blast
        ultimately have H1: \<open>cdcl_twl_enum_inv W\<close>
          using star final unfolding cdcl_twl_enum_inv_def
          using rtranclp_cdcl_twl_stgy_twl_stgy_invs rtranclp_cdcl_twl_stgy_twl_struct_invs by blast
        have [simp]: \<open>get_all_init_clss W = get_all_init_clss V\<close>
          by (metis rtranclp_cdcl_twl_stgy_all_learned_diff_learned star)
        have [simp]: \<open>get_all_init_clss V = add_mset (DECO_clause (get_trail U))(get_all_init_clss U)\<close>
          using neg by (auto simp: negate_model_and_add_twl.simps)

        have \<open>next_model (map lit_of (get_trail W)) (get_all_init_clss W)\<close> 
          if None: \<open>get_conflict W = None\<close>
          using invs_V ent_V
        proof (rule cdcl_twl_stgy_final_twl_stateE[OF star final])
          show ?thesis
            if \<open>get_conflict W \<noteq> None\<close>
            using that None by blast
          show ?thesis
            if 
              \<open>get_conflict W = None\<close> and
              \<open>consistent_interp (lits_of_l (get_trail W))\<close> and
              \<open>no_dup (get_trail W)\<close> and
              \<open>atm_of ` lits_of_l (get_trail W) \<subseteq> atms_of_mm (get_all_init_clss W)\<close> and
              \<open>get_trail W \<Turnstile>asm get_all_init_clss V\<close> and
              \<open>satisfiable (set_mset (get_all_init_clss V))\<close>
            using that that(5) unfolding next_model.simps
            by (auto simp: lits_of_def true_annots_true_cls no_dup_map_lit_of)
        qed

        have \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of U)\<close>  and
          decomp: \<open>all_decomposition_implies_m (cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of U))
             (get_all_ann_decomposition (trail (state\<^sub>W_of U)))\<close>
          using struct_U unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
          by fast+

        have \<open>all_models (add_mset (lit_of `# mset (get_trail U)) (get_all_init_clss U)) =
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
              \<open>atm_of ` lits_of_l (get_trail U) \<subseteq> atms_of_mm (get_all_init_clss U)\<close> and
              \<open>get_trail U \<Turnstile>asm get_all_init_clss U\<close> and
              \<open>satisfiable (set_mset (get_all_init_clss U))\<close>
          proof -
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
            then have \<open>set_mset (get_all_init_clss U) \<union>
                CNot (DECO_clause (get_trail U)) \<Turnstile>ps unmark_l (trail (state\<^sub>W_of U))\<close>
              using ent_U unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def
                cdcl\<^sub>W_restart_mset.clauses_def
              by (auto simp: clauses_def twl_st intro: ent3_gnerealise)
            have \<open>I \<Turnstile> DECO_clause (get_trail U)\<close>
              if 
                \<open>consistent_interp I\<close> and
                \<open>I \<Turnstile> lit_of `# mset (get_trail U)\<close> and
                \<open>atm_of ` I \<subseteq> atms_of (lit_of `# mset (get_trail U)) \<union> atms_of_mm (get_all_init_clss U)\<close> and
                \<open>I \<Turnstile>m get_all_init_clss U\<close>
              for I
            proof -
              have \<open>unmark_l (trail (state\<^sub>W_of U)) = unmark_l (trail (state\<^sub>W_of U)) \<union>
                        DECO_clause (get_trail U)\<close>
                apply (auto)
              show ?thesis sorry
            qed
            show ?thesis
              apply (auto simp: all_models_def)
              sorry
          qed
        qed

        have H2: \<open>(W, U) \<in> R\<close>
          using confl unfolding R_def apply (auto)
          
          
          sorry
        note H1 H2
      } note H = this
      show ?thesis
        apply (auto simp add:  conclusive_TWL_run_def)
        apply (rule Collect_mono)
        apply (intro conjI impI)
         apply clarify
        sorry
    qed
    show ?thesis
      apply (refine_vcg WHILEIT_rule[where R=\<open>R\<close>])
      subgoal by (rule wf)
      subgoal
        using T S unfolding enum_model_st_direct_def enum_equisatisfiable_st_clss_def 
          cdcl_twl_enum_inv_def
        by auto
      subgoal for U V
        explore_have
        apply (simp add: conclusive_TWL_run_def)
        apply (rule Collect_mono)
        apply (intro conjI impI)
        apply clarify
        sorry
      subgoal for U
  
        sorry
      sorry
  qed
  show ?thesis
    unfolding cdcl_twl_enum_def
    apply (intro frefI nres_relI)
    apply (subst next_model_filtered_nres_alt_def)
    subgoal by auto
    apply (refine_vcg conclusive_run WHILEIT_rule)
    unfolding conc_fun_SPEC
    subgoal for S MN T M
      explore_have
    apply (refine_vcg WHILEIT_rule)

    subgoal for S MN
      oops
      thm WHILEIT_rule

end

end