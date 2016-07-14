theory CDCL_W_Termination
imports CDCL_W
begin

context conflict_driven_clause_learning\<^sub>W
begin

subsection \<open>Termination\<close>

subsubsection \<open>No Relearning of a clause\<close>

lemma cdcl\<^sub>W_stgy_no_relearned_clause:
  assumes 
    cdcl: \<open>backtrack S T\<close> and
    inv: "cdcl\<^sub>W_all_struct_inv S" and
    smaller: \<open>no_smaller_propa S\<close> and
    confl: \<open>conflicting S = Some D\<close>
  shows
    \<open>D \<notin># clauses S\<close>
proof (rule ccontr)
  assume n_dist: \<open>\<not> ?thesis\<close>
  obtain K L :: "'v literal"  and
    M1 M2 :: "('v, 'v literal multiset) ann_lit list" and i :: nat where
    "conflicting S = Some D" and
    LD: "L \<in># D" and
    decomp: "(Decided K # M1, M2) \<in> set (get_all_ann_decomposition (trail S))" and
    "get_level (trail S) L = backtrack_lvl S" and
    "get_level (trail S) L = get_maximum_level (trail S) D" and
    i: "get_maximum_level (trail S) (D - {#L#}) \<equiv> i" and
    "get_level (trail S) K = i + 1" and
    T: "T \<sim> cons_trail (Propagated L D)
        (reduce_trail_to M1
          (add_learned_cls D
            (update_backtrack_lvl i
              (update_conflicting None S))))"
    using cdcl confl by (auto elim!: rulesE)
    
  obtain M2' where M2': \<open>trail S = (M2' @ M2) @ Decided K # M1\<close>  
    using decomp by auto
  have inv_T: \<open>cdcl\<^sub>W_all_struct_inv T\<close>
    using cdcl cdcl\<^sub>W_stgy_cdcl\<^sub>W_all_struct_inv inv W_other backtrack bj 
      cdcl\<^sub>W_all_struct_inv_inv cdcl\<^sub>W_cdcl\<^sub>W_restart by blast
  then have \<open>M1 \<Turnstile>as CNot (remove1_mset L D)\<close>
    using T decomp unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_conflicting_def
    by auto
  moreover have \<open>undefined_lit M1 L\<close>
    using inv_T T decomp unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def
    by (auto simp: defined_lit_map)
  moreover have \<open>remove1_mset L D + {#L#} \<in># clauses S\<close>
    using n_dist LD by (auto simp: clauses_def)
  ultimately show False
    using smaller unfolding no_smaller_propa_def M2' by blast
qed

lemma cdcl\<^sub>W_stgy_distinct_mset:
  assumes 
    cdcl: \<open>cdcl\<^sub>W_stgy S T\<close> and
    inv: "cdcl\<^sub>W_all_struct_inv S" and
    smaller: \<open>no_smaller_propa S\<close> and
    dist: \<open>distinct_mset (clauses S)\<close>
  shows  
    \<open>distinct_mset (clauses T)\<close>
proof (rule ccontr)
  assume n_dist: \<open>\<not> distinct_mset (clauses T)\<close>
  then have \<open>backtrack S T\<close>
    using cdcl dist by (auto simp: cdcl\<^sub>W_stgy.simps cdcl\<^sub>W_o.simps cdcl\<^sub>W_bj.simps 
        elim: propagateE conflictE decideE skipE resolveE)
  then show False
    using n_dist cdcl\<^sub>W_stgy_no_relearned_clause[of S T] dist
    by (auto simp: inv smaller distinct_mset_add_single elim!: rulesE)
qed

lemma rtranclp_cdcl\<^sub>W_stgy_distinct_mset_clauses:
  assumes
    st: "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* R S" and
    invR: "cdcl\<^sub>W_all_struct_inv R" and
    dist: "distinct_mset (clauses R)" and
    no_smaller: \<open>no_smaller_propa R\<close>
  shows "distinct_mset (clauses S)"
  using assms by (induction rule: rtranclp_induct)
    (auto simp: cdcl\<^sub>W_stgy_distinct_mset rtranclp_cdcl\<^sub>W_stgy_no_smaller_propa
      rtranclp_cdcl\<^sub>W_stgy_cdcl\<^sub>W_all_struct_inv)

lemma cdcl\<^sub>W_stgy_distinct_mset_clauses:
  assumes
    st: "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (init_state N) S" and
    no_duplicate_clause: "distinct_mset N" and
    no_duplicate_in_clause: "distinct_mset_mset N"
  shows "distinct_mset (clauses S)"
  using rtranclp_cdcl\<^sub>W_stgy_distinct_mset_clauses[OF st] assms
  by (auto simp: cdcl\<^sub>W_all_struct_inv_def distinct_cdcl\<^sub>W_state_def no_smaller_propa_def)


subsubsection \<open>Decrease of a Measure\<close>

fun cdcl\<^sub>W_restart_measure where
"cdcl\<^sub>W_restart_measure S =
  [(3::nat) ^ (card (atms_of_mm (init_clss S))) - card (set_mset (learned_clss S)),
    if conflicting S = None then 1 else 0,
    if conflicting S = None then card (atms_of_mm (init_clss S)) - length (trail S)
    else length (trail S)
    ]"

lemma length_model_le_vars:
  assumes
    "no_strange_atm S" and
    no_d: "no_dup (trail S)" and
    "finite (atms_of_mm (init_clss S))"
  shows "length (trail S) \<le> card (atms_of_mm (init_clss S))"
proof -
  obtain M N U k D where S: "state S = (M, N, U, k, D)" by (cases "state S", auto)
  have "finite (atm_of ` lits_of_l (trail S))"
    using assms(1,3) unfolding S by (auto simp add: finite_subset)
  have "length (trail S) = card (atm_of ` lits_of_l (trail S))"
    using no_dup_length_eq_card_atm_of_lits_of_l no_d by blast
  then show ?thesis using assms(1) unfolding no_strange_atm_def
  by (auto simp add: assms(3) card_mono)
qed

lemma length_model_le_vars_all_inv:
  assumes "cdcl\<^sub>W_all_struct_inv S"
  shows "length (trail S) \<le> card (atms_of_mm (init_clss S))"
  using assms length_model_le_vars[of S] unfolding cdcl\<^sub>W_all_struct_inv_def
  by (auto simp: cdcl\<^sub>W_M_level_inv_decomp)

lemma learned_clss_less_upper_bound:
  fixes S :: 'st
  assumes
    "distinct_cdcl\<^sub>W_state S" and
    "\<forall>s \<in># learned_clss S. \<not>tautology s"
  shows "card(set_mset (learned_clss S)) \<le> 3 ^ card (atms_of_mm (learned_clss S))"
proof -
  have "set_mset (learned_clss S) \<subseteq> simple_clss (atms_of_mm (learned_clss S))"
    apply (rule simplified_in_simple_clss)
    using assms unfolding distinct_cdcl\<^sub>W_state_def by auto
  then have "card(set_mset (learned_clss S))
    \<le> card (simple_clss (atms_of_mm (learned_clss S)))"
    by (simp add: simple_clss_finite card_mono)
  then show ?thesis
    by (meson atms_of_ms_finite simple_clss_card finite_set_mset order_trans)
qed


lemma cdcl\<^sub>W_restart_measure_decreasing:
  fixes S :: 'st
  assumes
    "cdcl\<^sub>W_restart S S'" and
    no_restart:
      "\<not>(learned_clss S \<subseteq># learned_clss S' \<and> [] = trail S' \<and> conflicting S' = None)"
    (*no restart*) and
    no_forget: "learned_clss S \<subseteq># learned_clss S'" (*no forget*) and
    no_relearn: "\<And>S'. backtrack S S' \<Longrightarrow> \<forall>T. conflicting S = Some T \<longrightarrow> T \<notin># learned_clss S"
      and
    alien: "no_strange_atm S" and
    M_level: "cdcl\<^sub>W_M_level_inv S" and
    no_taut: "\<forall>s \<in># learned_clss S. \<not>tautology s" and
    no_dup: "distinct_cdcl\<^sub>W_state S" and
    confl: "cdcl\<^sub>W_conflicting S"
  shows "(cdcl\<^sub>W_restart_measure S', cdcl\<^sub>W_restart_measure S) \<in> lexn less_than 3"
  using assms(1) M_level assms(2,3)
proof (induct rule: cdcl\<^sub>W_restart_all_induct)
  case (propagate C L) note conf = this(1) and undef = this(5) and T = this(6)
  have propa: "propagate S (cons_trail (Propagated L C) S)"
    using propagate_rule[OF propagate.hyps(1,2)] propagate.hyps by auto
  then have no_dup': "no_dup (Propagated L C # trail S)"
    using M_level cdcl\<^sub>W_M_level_inv_decomp(2) undef defined_lit_map by auto

  let ?N = "init_clss S"
  have "no_strange_atm (cons_trail (Propagated L C) S)"
    using alien cdcl\<^sub>W_restart.propagate cdcl\<^sub>W_restart_no_strange_atm_inv propa M_level by blast
  then have "atm_of ` lits_of_l (Propagated L C # trail S)
    \<subseteq> atms_of_mm (init_clss S)"
    using undef unfolding no_strange_atm_def by auto
  then have "card (atm_of ` lits_of_l (Propagated L C # trail S))
    \<le> card (atms_of_mm (init_clss S))"
    by (meson atms_of_ms_finite card_mono finite_set_mset)
  then have "length (Propagated L C # trail S) \<le> card (atms_of_mm ?N)"
    using no_dup_length_eq_card_atm_of_lits_of_l no_dup' by fastforce
  then have H: "card (atms_of_mm (init_clss S)) - length (trail S)
    = Suc (card (atms_of_mm (init_clss S)) - Suc (length (trail S)))"
    by simp
  show ?case using conf T undef by (auto simp: H lexn3_conv)
next
  case (decide L) note conf = this(1) and undef = this(2) and T = this(4)
  moreover
    have dec: "decide S (cons_trail (Decided L) (incr_lvl S))"
      using decide_rule decide.hyps by force
    then have cdcl\<^sub>W_restart:"cdcl\<^sub>W_restart S (cons_trail (Decided L) (incr_lvl S))"
      using cdcl\<^sub>W_restart.simps cdcl\<^sub>W_o.intros by blast
  moreover
    have lev: "cdcl\<^sub>W_M_level_inv (cons_trail (Decided L) (incr_lvl S))"
      using cdcl\<^sub>W_restart M_level cdcl\<^sub>W_restart_consistent_inv[OF cdcl\<^sub>W_restart] by auto
    then have no_dup: "no_dup (Decided L # trail S)"
      using undef unfolding cdcl\<^sub>W_M_level_inv_def by auto
    have "no_strange_atm (cons_trail (Decided L) (incr_lvl S))"
      using M_level alien calculation(4) cdcl\<^sub>W_restart_no_strange_atm_inv by blast
    then have "length (Decided L # (trail S))
      \<le> card (atms_of_mm (init_clss S))"
      using no_dup undef
      length_model_le_vars[of "cons_trail (Decided L) (incr_lvl S)"]
      by fastforce
  ultimately show ?case using conf by (simp add: lexn3_conv)
next
  case (skip L C' M D) note tr = this(1) and conf = this(2) and T = this(5)
  show ?case using conf T by (simp add: tr lexn3_conv)
next
  case conflict
  then show ?case by (simp add: lexn3_conv)
next
  case resolve
  then show ?case using finite by (simp add: lexn3_conv)
next
  case (backtrack L D K i M1 M2 T) note conf = this(1) and decomp = this(3) and T = this(8) and
  lev = this(9)
  have bt: "backtrack S T"
    using backtrack_rule[OF backtrack.hyps] by auto
  have "D \<notin># learned_clss S"
    using no_relearn conf bt by auto
  then have card_T:
    "card (set_mset ({#D#} + learned_clss S)) = Suc (card (set_mset (learned_clss S)))"
    by simp
  have "distinct_cdcl\<^sub>W_state T"
    using bt M_level distinct_cdcl\<^sub>W_state_inv no_dup other cdcl\<^sub>W_o.intros cdcl\<^sub>W_bj.intros by blast
  moreover have "\<forall>s\<in>#learned_clss T. \<not> tautology s"
    using learned_clss_are_not_tautologies[OF cdcl\<^sub>W_restart.other[OF cdcl\<^sub>W_o.bj[OF
      cdcl\<^sub>W_bj.backtrack[OF bt]]]] M_level no_taut confl by auto
  ultimately have "card (set_mset (learned_clss T)) \<le> 3 ^ card (atms_of_mm (learned_clss T))"
      by (auto simp: learned_clss_less_upper_bound)
    then have H: "card (set_mset ({#D#} + learned_clss S))
      \<le> 3 ^ card (atms_of_mm ({#D#} + learned_clss S))"
      using T decomp M_level by (simp add: cdcl\<^sub>W_M_level_inv_decomp)
  moreover
    have "atms_of_mm ({#D#} + learned_clss S) \<subseteq> atms_of_mm (init_clss S)"
      using alien conf unfolding no_strange_atm_def by auto
    then have card_f: "card (atms_of_mm ({#D#} + learned_clss S))
      \<le> card (atms_of_mm (init_clss S))"
      by (meson atms_of_ms_finite card_mono finite_set_mset)
    then have "(3::nat) ^ card (atms_of_mm ({#D#} + learned_clss S))
      \<le> 3 ^ card (atms_of_mm (init_clss S))" by simp
  ultimately have "(3::nat) ^ card (atms_of_mm (init_clss S))
    \<ge> card (set_mset ({#D#} + learned_clss S))"
    using le_trans by blast
  then show ?case using decomp diff_less_mono2 card_T T M_level
    by (auto simp: cdcl\<^sub>W_M_level_inv_decomp lexn3_conv)
next
  case restart
  then show ?case using alien by (auto simp: state_eq_def simp del: state_simp)
next
  case (forget C T) note no_forget = this(9)
  then have "C \<in># learned_clss S" and "C \<notin># learned_clss T"
    using forget.hyps by auto
  then have "\<not> learned_clss S \<subseteq># learned_clss T"
     by (auto simp add: mset_subset_eqD)
  then show ?case using no_forget by blast
qed

lemma propagate_measure_decreasing:
  fixes S :: 'st
  assumes "propagate S S'" and "cdcl\<^sub>W_all_struct_inv S"
  shows "(cdcl\<^sub>W_restart_measure S', cdcl\<^sub>W_restart_measure S) \<in> lexn less_than 3"
  apply (rule cdcl\<^sub>W_restart_measure_decreasing)
  using assms(1) propagate apply blast
           using assms(1) apply (auto simp add: propagate.simps)[3]
        using assms(2) apply (auto simp add: cdcl\<^sub>W_all_struct_inv_def)
  done

lemma conflict_measure_decreasing:
  fixes S :: 'st
  assumes "conflict S S'" and "cdcl\<^sub>W_all_struct_inv S"
  shows "(cdcl\<^sub>W_restart_measure S', cdcl\<^sub>W_restart_measure S) \<in> lexn less_than 3"
  apply (rule cdcl\<^sub>W_restart_measure_decreasing)
  using assms(1) conflict apply blast
            using assms(1) apply (auto simp: state_eq_def simp del: state_simp elim!: conflictE)[3]
         using assms(2) apply (auto simp add: cdcl\<^sub>W_all_struct_inv_def elim: conflictE)
  done

lemma decide_measure_decreasing:
  fixes S :: 'st
  assumes "decide S S'" and "cdcl\<^sub>W_all_struct_inv S"
  shows "(cdcl\<^sub>W_restart_measure S', cdcl\<^sub>W_restart_measure S) \<in> lexn less_than 3"
  apply (rule cdcl\<^sub>W_restart_measure_decreasing)
  using assms(1) decide other apply blast
            using assms(1) apply (auto simp: state_eq_def simp del: state_simp elim!: decideE)[3]
         using assms(2) apply (auto simp add: cdcl\<^sub>W_all_struct_inv_def elim: decideE)
  done

lemma cdcl\<^sub>W_stgy_step_decreasing:
  fixes S T :: 'st
  assumes 
    cdcl: \<open>cdcl\<^sub>W_stgy S T\<close> and
    struct_inv: \<open>cdcl\<^sub>W_all_struct_inv S\<close> and
    smaller: \<open>no_smaller_propa S\<close>
  shows "(cdcl\<^sub>W_restart_measure T, cdcl\<^sub>W_restart_measure S) \<in> lexn less_than 3"
proof -
  from assms struct_inv show ?thesis
    proof (cases rule: cdcl\<^sub>W_stgy_cases)
      case conflict note cp = this(1)
      show ?thesis
        using struct_inv conflict_measure_decreasing cp by blast
    next
      case propagate note cp = this(1)
      show ?thesis
        using struct_inv propagate_measure_decreasing cp by blast
    next
      case decide note dec = this(3)
      show ?thesis
        using struct_inv decide_measure_decreasing dec by blast
    next    
      case backtrack note n_s = this(1,2) and bt = this(3)
      then have no_relearn: "\<forall>T. conflicting S = Some T \<longrightarrow> T \<notin># learned_clss S"
        using cdcl\<^sub>W_stgy_no_relearned_clause[of S T] 
        cdcl\<^sub>W_stgy_no_smaller_propa[of S T]
        cdcl struct_inv smaller
        unfolding clauses_def
        by (auto simp: distinct_mset_add disjunct_not_in elim!: rulesE)
      show ?thesis
        apply (rule cdcl\<^sub>W_restart_measure_decreasing)
                using bt cdcl\<^sub>W_bj.backtrack cdcl\<^sub>W_o.bj other apply (simp; fail)
               using bt struct_inv unfolding cdcl\<^sub>W_all_struct_inv_def
               cdcl\<^sub>W_M_level_inv_def apply (auto elim: backtrackE; fail)[]
              using bt struct_inv unfolding cdcl\<^sub>W_all_struct_inv_def
               cdcl\<^sub>W_M_level_inv_def apply (auto elim: backtrackE; fail)[]
             using bt no_relearn apply auto[]
            using struct_inv unfolding cdcl\<^sub>W_all_struct_inv_def apply simp
           using struct_inv unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def apply simp
          using struct_inv unfolding cdcl\<^sub>W_all_struct_inv_def apply simp
         using struct_inv unfolding cdcl\<^sub>W_all_struct_inv_def apply simp
        using struct_inv unfolding cdcl\<^sub>W_all_struct_inv_def by simp
    next
      case skip
      then show ?thesis by (auto simp: lexn3_conv elim!: skipE)
    next
      case resolve
      then show ?thesis by (auto simp: lexn3_conv elim!: resolveE)
    qed
qed

lemma empty_trail_no_smaller_propa: \<open>trail R = [] \<Longrightarrow> no_smaller_propa R\<close>
  by (simp add: no_smaller_propa_def)

text \<open>Roughly corresponds to \cwref{theo:prop:cdcltermlc}{theorem 2.9.15 page 86}
  (using a different bound)\<close>
lemma tranclp_cdcl\<^sub>W_stgy_decreasing:
  fixes R S T :: 'st
  assumes "cdcl\<^sub>W_stgy\<^sup>+\<^sup>+ R S" and
  tr: "trail R = []" and
  "cdcl\<^sub>W_all_struct_inv R"
  shows "(cdcl\<^sub>W_restart_measure S, cdcl\<^sub>W_restart_measure R) \<in> lexn less_than 3"
  using assms
  apply induction
   using empty_trail_no_smaller_propa cdcl\<^sub>W_stgy_no_relearned_clause cdcl\<^sub>W_stgy_step_decreasing 
    apply blast
  using tranclp_into_rtranclp[of cdcl\<^sub>W_stgy R] lexn_transI[OF trans_less_than, of 3] 
    rtranclp_cdcl\<^sub>W_stgy_no_smaller_propa unfolding trans_def
  by (meson cdcl\<^sub>W_stgy_step_decreasing empty_trail_no_smaller_propa 
      rtranclp_cdcl\<^sub>W_stgy_cdcl\<^sub>W_all_struct_inv)

lemma tranclp_cdcl\<^sub>W_stgy_S0_decreasing:
  fixes R S T :: 'st
  assumes
    pl: "cdcl\<^sub>W_stgy\<^sup>+\<^sup>+ (init_state N) S" and
    no_dup: "distinct_mset_mset N"
  shows "(cdcl\<^sub>W_restart_measure S, cdcl\<^sub>W_restart_measure (init_state N)) \<in> lexn less_than 3"
proof -
  have "cdcl\<^sub>W_all_struct_inv (init_state N)"
    using no_dup unfolding cdcl\<^sub>W_all_struct_inv_def by auto
  then show ?thesis using pl tranclp_cdcl\<^sub>W_stgy_decreasing init_state_trail by blast
qed

lemma wf_tranclp_cdcl\<^sub>W_stgy:
  "wf {(S::'st, init_state N)| S N. distinct_mset_mset N \<and> cdcl\<^sub>W_stgy\<^sup>+\<^sup>+ (init_state N) S}"
  apply (rule wf_wf_if_measure'_notation2[of "lexn less_than 3" _ _ cdcl\<^sub>W_restart_measure])
   apply (simp add: wf wf_lexn)
  using tranclp_cdcl\<^sub>W_stgy_S0_decreasing by blast

end

end
