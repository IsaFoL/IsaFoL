theory DPLL_W_Optimal_Model
imports CDCL_W_Optimal_Model
  CDCL.DPLL_W
begin


lemma
  assumes \<open>dpll\<^sub>W S T\<close> and
    \<open>rev (trail S) = M1 @ Propagated K () # M2\<close>
  shows
    \<open>\<exists>M1 M2 M2' K'. (rev (trail S) = M1 @ Propagated K' () # M2 \<or>
         rev (trail S) = M1 @ Decided (-K') # M2) \<and>
      rev (trail T) = M1 @ Propagated K' () # M2'\<close>
  using assms
  apply (induction S T rule: dpll\<^sub>W.induct)
  subgoal
    by auto
  subgoal
    by auto
  subgoal for S M' L M D
    using backtrack_split_snd_hd_decided[of \<open>trail S\<close>]
      backtrack_split_list_eq[of \<open>trail S\<close>, symmetric]
    apply - apply (rule exI[of _ \<open>rev M\<close>], rule exI[of _ \<open>rev M'\<close>], rule exI[of _ \<open>[]\<close>],
       rule exI[of _ \<open>-lit_of L\<close>])
    apply (cases L)
    by (auto intro: )
  done

locale bnb_ops =
  fixes
    weight :: \<open>'st \<Rightarrow> 'a\<close> and
    update_weight_information :: "'v dpll\<^sub>W_ann_lits \<Rightarrow> 'st \<Rightarrow> 'st" and
    is_improving_int :: "'v  dpll\<^sub>W_ann_lits \<Rightarrow> 'v  dpll\<^sub>W_ann_lits \<Rightarrow> 'v clauses \<Rightarrow> 'a \<Rightarrow> bool" and
    trail :: \<open>'st \<Rightarrow> 'v  dpll\<^sub>W_ann_lits\<close> and
    clauses :: \<open>'st \<Rightarrow> 'v clauses\<close> and
    tl_trail :: \<open>'st \<Rightarrow> 'st\<close> and
    cons_trail :: \<open>'v  dpll\<^sub>W_ann_lit \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    state_eq  :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> (infix "\<sim>" 50) and
    conflicting_clauses :: "'v clauses \<Rightarrow> 'a \<Rightarrow> 'v clauses"
begin

definition state :: \<open>'st \<Rightarrow> 'v  dpll\<^sub>W_ann_lits \<times> 'v clauses \<times> 'a\<close> where
  \<open>state S = (trail S, clauses S, weight S)\<close>

definition conflicting_clss :: \<open>'st \<Rightarrow> 'v literal multiset multiset\<close> where
  \<open>conflicting_clss S = conflicting_clauses (clauses S) (weight S)\<close>

definition abs_state where
  \<open>abs_state S = (trail S, clauses S + conflicting_clss S)\<close>

abbreviation is_improving where
  \<open>is_improving M M' S \<equiv> is_improving_int M M' (clauses S) (weight S)\<close>

end

locale bnb =
  bnb_ops weight update_weight_information is_improving_int trail clauses
    tl_trail cons_trail state_eq conflicting_clauses
  for
    weight :: \<open>'st \<Rightarrow> 'a\<close> and
    update_weight_information :: "'v dpll\<^sub>W_ann_lits \<Rightarrow> 'st \<Rightarrow> 'st" and
    is_improving_int :: "'v  dpll\<^sub>W_ann_lits \<Rightarrow> 'v  dpll\<^sub>W_ann_lits \<Rightarrow> 'v clauses \<Rightarrow> 'a \<Rightarrow> bool" and
    trail :: \<open>'st \<Rightarrow> 'v  dpll\<^sub>W_ann_lits\<close> and
    clauses :: \<open>'st \<Rightarrow> 'v clauses\<close> and
    tl_trail :: \<open>'st \<Rightarrow> 'st\<close> and
    cons_trail :: \<open>'v  dpll\<^sub>W_ann_lit \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    state_eq  :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> (infix "\<sim>" 50) and
    conflicting_clauses :: "'v clauses \<Rightarrow> 'a \<Rightarrow> 'v clauses" +
  assumes
    state_eq_ref[simp, intro]: \<open>S \<sim> S\<close> and
    state_eq_sym: \<open>S \<sim> T \<longleftrightarrow> T \<sim> S\<close> and
    state_eq_trans: \<open>S \<sim> T \<Longrightarrow> T \<sim> U' \<Longrightarrow> S \<sim> U'\<close> and
    state_eq_state: \<open>S \<sim> T \<Longrightarrow> state S = state T\<close> and

    cons_trail:
      "\<And>S'. state st = (M, S') \<Longrightarrow>
        state (cons_trail L st) = (L # M, S')" and

    tl_trail:
      "\<And>S'. state st = (M, S') \<Longrightarrow> state (tl_trail st) = (tl M, S')" and
    update_weight_information:
       \<open>state S = (M, N, w) \<Longrightarrow>
          \<exists>w'. state (update_weight_information M' S) = (M, N, w')\<close> and

    conflicting_clss_update_weight_information_mono:
      \<open>dpll\<^sub>W_all_inv (abs_state S) \<Longrightarrow> is_improving M M' S \<Longrightarrow>
        conflicting_clss S \<subseteq># conflicting_clss (update_weight_information M' S)\<close> and
    conflicting_clss_update_weight_information_in:
      \<open>is_improving M M' S \<Longrightarrow>         negate_ann_lits M' \<in># conflicting_clss (update_weight_information M' S)\<close> and
    atms_of_conflicting_clss:
      \<open>atms_of_mm (conflicting_clss S) \<subseteq> atms_of_mm (clauses S)\<close>
begin

inductive dpll\<^sub>W_core :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
propagate: "add_mset L C \<in># clauses S \<Longrightarrow> trail S \<Turnstile>as CNot C \<Longrightarrow> undefined_lit (trail S) L \<Longrightarrow>
  abs_state T = (Propagated L () # trail S, clauses S + conflicting_clss S) \<Longrightarrow>
  dpll\<^sub>W_core S T" |
decided: "undefined_lit (trail S) L \<Longrightarrow> atm_of L \<in> atms_of_mm (clauses S)
  \<Longrightarrow> abs_state T = (Decided L # trail S, clauses S + conflicting_clss S)
  \<Longrightarrow> dpll\<^sub>W_core S T " |
backtrack: "backtrack_split (trail S) = (M', L # M) \<Longrightarrow> is_decided L \<Longrightarrow> D \<in># clauses S
  \<Longrightarrow> abs_state T = (Propagated (- (lit_of L)) () # M, clauses S + conflicting_clss S)
  \<Longrightarrow> trail S \<Turnstile>as CNot D \<Longrightarrow> dpll\<^sub>W_core S T" |
backtrack_opt: "backtrack_split (trail S) = (M', L # M) \<Longrightarrow> is_decided L \<Longrightarrow> D \<in># conflicting_clss S
  \<Longrightarrow> trail S \<Turnstile>as CNot D
  \<Longrightarrow> abs_state T = (Propagated (- (lit_of L)) () # M, clauses S + conflicting_clss S)
  \<Longrightarrow> dpll\<^sub>W_core S T"

inductive dpll\<^sub>W_branch  :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
update_info:
  \<open>is_improving M M' S \<Longrightarrow> state T = state (update_weight_information M' S)
   \<Longrightarrow> dpll\<^sub>W_branch S T\<close>

lemma [simp]: \<open>DPLL_W.clauses (abs_state S) = clauses S + conflicting_clss S\<close>
  \<open>DPLL_W.trail (abs_state S) = trail S\<close>
  by (auto simp: abs_state_def)

lemma dpll\<^sub>W_core_is_dpll\<^sub>W:
  \<open>dpll\<^sub>W_core S T \<Longrightarrow> dpll\<^sub>W (abs_state S) (abs_state T)\<close>
  apply (induction rule: dpll\<^sub>W_core.induct)
  subgoal
    by (auto simp: dpll\<^sub>W.simps)
  subgoal
    by (auto simp: dpll\<^sub>W.simps)
  subgoal
    by (auto simp: dpll\<^sub>W.simps)
  subgoal
    by (auto simp: dpll\<^sub>W.simps)
  done

lemma [simp]: \<open>trail (update_weight_information M' S) = trail S\<close>
  using update_weight_information[of S]
  by (auto simp: state_def)

lemma [simp]:
  \<open>clauses (update_weight_information M' S) = clauses S\<close>
  using update_weight_information[of S]
  by (auto simp: state_def)

lemma dpll\<^sub>W_branch_trail:
    \<open>dpll\<^sub>W_branch S T \<Longrightarrow> trail S = trail T\<close> and
   dpll\<^sub>W_branch_clauses:
    \<open>dpll\<^sub>W_branch S T \<Longrightarrow> clauses S = clauses T\<close> and
  dpll\<^sub>W_branch_conflicting_clss:
    \<open>dpll\<^sub>W_branch S T \<Longrightarrow> dpll\<^sub>W_all_inv (abs_state S) \<Longrightarrow> conflicting_clss S \<subseteq># conflicting_clss T\<close>
  subgoal
    by (induction rule: dpll\<^sub>W_branch.induct)
     (auto simp: dpll\<^sub>W_all_inv_def state_def dest!: conflicting_clss_update_weight_information_mono)
  subgoal
    by (induction rule: dpll\<^sub>W_branch.induct)
     (auto simp: dpll\<^sub>W_all_inv_def state_def dest!: conflicting_clss_update_weight_information_mono)
  subgoal
    by (induction rule: dpll\<^sub>W_branch.induct)
      (auto simp: state_def conflicting_clss_def
        dest!: conflicting_clss_update_weight_information_mono)
  done

lemma dpll\<^sub>W_branch_abs_state_all_inv:
  \<open>dpll\<^sub>W_branch S T \<Longrightarrow> dpll\<^sub>W_all_inv (abs_state S) \<Longrightarrow> dpll\<^sub>W_all_inv (abs_state T)\<close>
  using dpll\<^sub>W_branch_conflicting_clss[of S T] dpll\<^sub>W_branch_clauses[of S T]
   atms_of_conflicting_clss[of T] atms_of_conflicting_clss[of S]
  apply (auto simp: dpll\<^sub>W_all_inv_def dpll\<^sub>W_branch_trail lits_of_def image_image
    intro: all_decomposition_implies_mono[OF set_mset_mono] dest: dpll\<^sub>W_branch_conflicting_clss)
  by (blast intro: all_decomposition_implies_mono)

end

end
