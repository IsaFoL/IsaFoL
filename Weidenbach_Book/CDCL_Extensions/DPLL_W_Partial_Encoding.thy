theory DPLL_W_Partial_Encoding
imports
  DPLL_W_Optimal_Model
  CDCL_W_Partial_Encoding
begin

locale dpll_optimal_encoding_opt =
  dpll\<^sub>W_state_optimal_weight trail clauses
    tl_trail cons_trail state_eq state   \<rho> update_additional_info +
  optimal_encoding_opt_ops \<Sigma> \<Delta>\<Sigma> new_vars 
  for
    trail :: \<open>'st \<Rightarrow> 'v  dpll\<^sub>W_ann_lits\<close> and
    clauses :: \<open>'st \<Rightarrow> 'v clauses\<close> and
    tl_trail :: \<open>'st \<Rightarrow> 'st\<close> and
    cons_trail :: \<open>'v  dpll\<^sub>W_ann_lit \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    state_eq  :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> (infix "\<sim>" 50) and
    state :: \<open>'st \<Rightarrow> 'v  dpll\<^sub>W_ann_lits \<times> 'v clauses \<times> 'v clause option \<times> 'b\<close> and
    update_additional_info :: \<open>'v clause option \<times> 'b \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    \<Sigma> \<Delta>\<Sigma> :: \<open>'v set\<close> and
    \<rho> :: \<open>'v clause \<Rightarrow> 'a :: {linorder}\<close> and
    new_vars :: \<open>'v \<Rightarrow> 'v \<times> 'v\<close>
begin

end


locale dpll_optimal_encoding =
  dpll_optimal_encoding_opt trail clauses
    tl_trail cons_trail state_eq state
    update_additional_info \<Sigma> \<Delta>\<Sigma> \<rho> new_vars  +
  optimal_encoding_ops
    \<Sigma> \<Delta>\<Sigma>
    new_vars \<rho>
  for
    trail :: \<open>'st \<Rightarrow> 'v  dpll\<^sub>W_ann_lits\<close> and
    clauses :: \<open>'st \<Rightarrow> 'v clauses\<close> and
    tl_trail :: \<open>'st \<Rightarrow> 'st\<close> and
    cons_trail :: \<open>'v  dpll\<^sub>W_ann_lit \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    state_eq  :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> (infix "\<sim>" 50) and
    state :: \<open>'st \<Rightarrow> 'v  dpll\<^sub>W_ann_lits \<times> 'v clauses \<times> 'v clause option \<times> 'b\<close> and
    update_additional_info :: \<open>'v clause option \<times> 'b \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    \<Sigma> \<Delta>\<Sigma> :: \<open>'v set\<close> and
    \<rho> :: \<open>'v clause \<Rightarrow> 'a :: {linorder}\<close> and
    new_vars :: \<open>'v \<Rightarrow> 'v \<times> 'v\<close>
begin


inductive odecide :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> where
  odecide_noweight: \<open>odecide S T\<close>
if
  \<open>undefined_lit (trail S) L\<close> and
  \<open>atm_of L \<in> atms_of_mm (clauses S)\<close> and
  \<open>T \<sim> cons_trail (Decided L) S\<close> and
  \<open>atm_of L \<in> \<Sigma> - \<Delta>\<Sigma>\<close> |
  odecide_replacement_pos: \<open>odecide S T\<close>
if
  \<open>undefined_lit (trail S) (Pos (replacement_pos L))\<close> and
  \<open>T \<sim> cons_trail (Decided (Pos (replacement_pos L))) S\<close> and
  \<open>L \<in> \<Delta>\<Sigma>\<close> |
  odecide_replacement_neg: \<open>odecide S T\<close>
if
  \<open>undefined_lit (trail S) (Pos (replacement_neg L))\<close> and
  \<open>T \<sim> cons_trail (Decided (Pos (replacement_neg L))) S\<close> and
  \<open>L \<in> \<Delta>\<Sigma>\<close>

inductive_cases odecideE: \<open>odecide S T\<close>

inductive dpll_conflict :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> where
\<open>dpll_conflict S S\<close>
if \<open>C \<in># clauses S\<close> and
  \<open>trail S \<Turnstile>as CNot C\<close>

inductive odpll\<^sub>W_core_stgy :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S T where
propagate: "dpll_propagate S T \<Longrightarrow> odpll\<^sub>W_core_stgy S T" |
decided: "odecide S T \<Longrightarrow> no_step dpll_propagate S  \<Longrightarrow> no_step dpll_backtrack S \<Longrightarrow>
  no_step dpll_conflict S \<Longrightarrow> odpll\<^sub>W_core_stgy S T " |
backtrack: "dpll_backtrack S T \<Longrightarrow> odpll\<^sub>W_core_stgy S T" |
backtrack_opt: \<open>bnb.backtrack_opt S T \<Longrightarrow> odpll\<^sub>W_core_stgy S T\<close>

lemma odpll\<^sub>W_core_stgy_clauses:
  \<open>odpll\<^sub>W_core_stgy S T \<Longrightarrow> clauses T = clauses S\<close>
  by (induction rule: odpll\<^sub>W_core_stgy.induct)
   (auto simp: dpll_propagate.simps odecide.simps dpll_backtrack.simps
      bnb.backtrack_opt.simps)

lemma rtranclp_odpll\<^sub>W_core_stgy_clauses:
  \<open>odpll\<^sub>W_core_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> clauses T = clauses S\<close>
  by (induction rule: rtranclp_induct)
    (auto dest: odpll\<^sub>W_core_stgy_clauses)


inductive odpll\<^sub>W_bnb_stgy :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> for S T :: 'st where
dpll:
  \<open>odpll\<^sub>W_bnb_stgy S T\<close>
  if \<open>odpll\<^sub>W_core_stgy S T\<close> |
bnb:
  \<open>odpll\<^sub>W_bnb_stgy S T\<close>
  if \<open>bnb.dpll\<^sub>W_bound S T\<close>

lemma odpll\<^sub>W_bnb_stgy_clauses:
  \<open>odpll\<^sub>W_bnb_stgy S T \<Longrightarrow> clauses T = clauses S\<close>
  by (induction rule: odpll\<^sub>W_bnb_stgy.induct)
   (auto simp: bnb.dpll\<^sub>W_bound.simps dest: odpll\<^sub>W_core_stgy_clauses)

lemma rtranclp_odpll\<^sub>W_bnb_stgy_clauses:
  \<open>odpll\<^sub>W_bnb_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> clauses T = clauses S\<close>
  by (induction rule: rtranclp_induct)
    (auto dest: odpll\<^sub>W_bnb_stgy_clauses)

lemma odecide_dpll_decide_iff:
  assumes \<open>clauses S = penc N\<close> \<open>atms_of_mm N = \<Sigma>\<close>
  shows \<open>odecide S T \<Longrightarrow> dpll_decide S T\<close>
    \<open>dpll_decide S T \<Longrightarrow> Ex(odecide S)\<close>
  using assms atms_of_mm_penc_subset2[of N] \<Delta>\<Sigma>_\<Sigma>
  unfolding odecide.simps dpll_decide.simps
  apply (auto simp: odecide.simps dpll_decide.simps)
  apply (metis defined_lit_Pos_atm_iff state_eq_ref)+
  done

lemma
  assumes \<open>clauses S = penc N\<close> \<open>atms_of_mm N = \<Sigma>\<close>
  shows
    odpll\<^sub>W_core_stgy_dpll\<^sub>W_core_stgy: \<open>odpll\<^sub>W_core_stgy S T \<Longrightarrow> bnb.dpll\<^sub>W_core_stgy S T\<close>
  using odecide_dpll_decide_iff[OF assms]
  by (auto simp: odpll\<^sub>W_core_stgy.simps bnb.dpll\<^sub>W_core_stgy.simps)

lemma
  assumes \<open>clauses S = penc N\<close> \<open>atms_of_mm N = \<Sigma>\<close>
  shows
    odpll\<^sub>W_bnb_stgy_dpll\<^sub>W_bnb_stgy: \<open>odpll\<^sub>W_bnb_stgy S T \<Longrightarrow> bnb.dpll\<^sub>W_bnb S T\<close>
  using odecide_dpll_decide_iff[OF assms]
  by (auto simp: odpll\<^sub>W_bnb_stgy.simps bnb.dpll\<^sub>W_bnb.simps dest: odpll\<^sub>W_core_stgy_dpll\<^sub>W_core_stgy[OF assms]
    bnb.dpll\<^sub>W_core_stgy_dpll\<^sub>W_core)

lemma
  assumes \<open>clauses S = penc N\<close> and [simp]: \<open>atms_of_mm N = \<Sigma>\<close>
  shows
    rtranclp_odpll\<^sub>W_bnb_stgy_dpll\<^sub>W_bnb_stgy: \<open>odpll\<^sub>W_bnb_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> bnb.dpll\<^sub>W_bnb\<^sup>*\<^sup>* S T\<close>
  using assms(1) apply -
  apply (induction rule: rtranclp_induct)
  subgoal by auto
  subgoal for T U
    using odpll\<^sub>W_bnb_stgy_dpll\<^sub>W_bnb_stgy[of T N U] rtranclp_odpll\<^sub>W_bnb_stgy_clauses[of S T]
    by auto
  done

(*
lemma no_step_odpll\<^sub>W_core_stgy_no_step_dpll\<^sub>W_core_stgy:
  assumes \<open>clauses S = penc N\<close> and [simp]:\<open>atms_of_mm N = \<Sigma>\<close>
  shows
    \<open>no_step odpll\<^sub>W_core_stgy S \<longleftrightarrow> no_step bnb.dpll\<^sub>W_core_stgy S\<close>
  using odecide_dpll_decide_iff[of S, OF assms]
  by (auto simp: odpll\<^sub>W_core_stgy.simps bnb.dpll\<^sub>W_core_stgy.simps)

lemma no_step_odpll\<^sub>W_bnb_stgy_no_step_dpll\<^sub>W_bnb:
  assumes \<open>clauses S = penc N\<close> and [simp]:\<open>atms_of_mm N = \<Sigma>\<close>
  shows
    \<open>no_step odpll\<^sub>W_bnb_stgy S \<longleftrightarrow> no_step bnb.dpll\<^sub>W_bnb S\<close>
  using no_step_odpll\<^sub>W_core_stgy_no_step_dpll\<^sub>W_core_stgy[of S, OF assms] bnb.no_step_stgy_iff
  by (auto simp: odpll\<^sub>W_bnb_stgy.simps bnb.dpll\<^sub>W_bnb.simps dest: odpll\<^sub>W_core_stgy_dpll\<^sub>W_core_stgy[OF assms]
    bnb.dpll\<^sub>W_core_stgy_dpll\<^sub>W_core)

lemma full_odpll\<^sub>W_core_stgy_full_dpll\<^sub>W_core_stgy:
  assumes \<open>clauses S = penc N\<close> and [simp]:\<open>atms_of_mm N = \<Sigma>\<close>
  shows
    \<open>full odpll\<^sub>W_bnb_stgy S T \<Longrightarrow> full bnb.dpll\<^sub>W_bnb S T\<close>
  using no_step_odpll\<^sub>W_bnb_stgy_no_step_dpll\<^sub>W_bnb[of T, OF _ assms(2)]
    rtranclp_odpll\<^sub>W_bnb_stgy_clauses[of S T, symmetric, unfolded assms]
    rtranclp_odpll\<^sub>W_bnb_stgy_dpll\<^sub>W_bnb_stgy[of S N T, OF assms]
   by (auto simp: full_def)
*)

definition "no_smaller_confl (S ::'st) \<equiv>
  (\<forall>M K M' D. trail S = M' @ Decided K # M \<longrightarrow> D \<in># clauses S \<longrightarrow> \<not>M \<Turnstile>as CNot D)"

lemma decided_cons_eq_append_decide_cons:
  "Decided L # Ms = M' @ Decided K # M \<longleftrightarrow>
    (L = K \<and> Ms = M \<and> M' = []) \<or>
    (hd M' = Decided L \<and> Ms = tl M' @ Decided K # M \<and> M' \<noteq> [])"
  by (cases M')
   auto

lemma [simp]: \<open>T \<sim> S \<Longrightarrow> no_smaller_confl T = no_smaller_confl S\<close>
  by (auto simp: no_smaller_confl_def)

lemma no_smaller_confl_cons_trail[simp]:
  \<open>no_smaller_confl (cons_trail (Propagated L C) S) \<longleftrightarrow> no_smaller_confl S\<close>
  \<open>no_smaller_confl (update_weight_information M' S) \<longleftrightarrow> no_smaller_confl S\<close>
  by (force simp: no_smaller_confl_def cdcl\<^sub>W_restart_mset.propagated_cons_eq_append_decide_cons)+

lemma no_smaller_confl_cons_trail_decided[simp]:
  \<open>no_smaller_confl S \<Longrightarrow> no_smaller_confl (cons_trail (Decided L) S) \<longleftrightarrow> (\<forall>C \<in># clauses S. \<not>trail S \<Turnstile>as CNot C)\<close>
  by (auto simp: no_smaller_confl_def cdcl\<^sub>W_restart_mset.propagated_cons_eq_append_decide_cons
    decided_cons_eq_append_decide_cons)



lemma no_step_dpll_backtrack_iff:
  \<open>no_step dpll_backtrack S \<longleftrightarrow> (count_decided (trail S) = 0 \<or> (\<forall>C \<in># clauses S. \<not>trail S \<Turnstile>as CNot C))\<close>
  using backtrack_snd_empty_not_decided[of \<open>trail S\<close>] backtrack_split_list_eq[of \<open>trail S\<close>, symmetric]
  apply (cases \<open>backtrack_split (trail S)\<close>; cases \<open>snd(backtrack_split (trail S))\<close>)
  by (auto simp: dpll_backtrack.simps count_decided_0_iff)

lemma no_step_dpll_conflict:
  \<open>(\<forall>S'. \<not> dpll_conflict S S') \<longleftrightarrow> (\<forall>C \<in># clauses S. \<not>trail S \<Turnstile>as CNot C)\<close>
  by (auto simp: dpll_conflict.simps)

lemma count_decided_0_no_smaller_confl: \<open>count_decided (trail S) = 0 \<Longrightarrow> no_smaller_confl S\<close>
  by (auto simp: no_smaller_confl_def)

lemma no_smaller_confl_backtrack_split:
  \<open>no_smaller_confl S \<Longrightarrow>
       backtrack_split (trail S) = (M', L # M) \<Longrightarrow>
       no_smaller_confl (reduce_trail_to M S)\<close>
  using backtrack_split_list_eq[of \<open>trail S\<close>, symmetric]
  by (auto simp: no_smaller_confl_def)
  
lemma odpll\<^sub>W_core_stgy_no_smaller_conflict:
  \<open>odpll\<^sub>W_core_stgy S T \<Longrightarrow> no_smaller_confl S \<Longrightarrow> no_smaller_confl T\<close>
  using no_step_dpll_backtrack_iff[of S] apply -
  by (induction rule: odpll\<^sub>W_core_stgy.induct)
   (auto simp: cdcl\<^sub>W_restart_mset.propagated_cons_eq_append_decide_cons count_decided_0_no_smaller_confl
      dpll_propagate.simps dpll_decide.simps odecide.simps decided_cons_eq_append_decide_cons
      bnb.backtrack_opt.simps dpll_backtrack.simps no_step_dpll_conflict no_smaller_confl_backtrack_split)

lemma odpll\<^sub>W_bound_stgy_no_smaller_conflict: \<open>bnb.dpll\<^sub>W_bound S T \<Longrightarrow> no_smaller_confl S \<Longrightarrow> no_smaller_confl T\<close>
  by (auto simp: cdcl\<^sub>W_restart_mset.propagated_cons_eq_append_decide_cons count_decided_0_no_smaller_confl
      dpll_propagate.simps dpll_decide.simps odecide.simps decided_cons_eq_append_decide_cons bnb.dpll\<^sub>W_bound.simps
      bnb.backtrack_opt.simps dpll_backtrack.simps no_step_dpll_conflict no_smaller_confl_backtrack_split)

lemma odpll\<^sub>W_bnb_stgy_no_smaller_conflict:
  \<open>odpll\<^sub>W_bnb_stgy S T \<Longrightarrow> no_smaller_confl S \<Longrightarrow> no_smaller_confl T\<close>
  by (induction rule: odpll\<^sub>W_bnb_stgy.induct)
    (auto simp: odpll\<^sub>W_core_stgy_no_smaller_conflict odpll\<^sub>W_bound_stgy_no_smaller_conflict)

end

end