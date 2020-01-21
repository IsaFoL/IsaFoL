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

definition no_smaller_confl :: \<open>'st \<Rightarrow> bool\<close> where
"no_smaller_confl (S ::'st) \<longleftrightarrow>
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
  \<open>no_step dpll_conflict S \<longleftrightarrow> (\<forall>C \<in># clauses S. \<not>trail S \<Turnstile>as CNot C)\<close>
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


definition no_smaller_propa :: \<open>'st \<Rightarrow> bool\<close> where
"no_smaller_propa (S ::'st) \<longleftrightarrow>
  (\<forall>M K M' D L. trail S = M' @ Decided K # M \<longrightarrow> add_mset L D \<in># clauses S \<longrightarrow> undefined_lit M L \<longrightarrow> \<not>M \<Turnstile>as CNot D)"

    
lemma [simp]: \<open>T \<sim> S \<Longrightarrow> no_smaller_propa T = no_smaller_propa S\<close>
  by (auto simp: no_smaller_propa_def)

lemma no_smaller_propa_cons_trail[simp]:
  \<open>no_smaller_propa (cons_trail (Propagated L C) S) \<longleftrightarrow> no_smaller_propa S\<close>
  \<open>no_smaller_propa (update_weight_information M' S) \<longleftrightarrow> no_smaller_propa S\<close>
  by (force simp: no_smaller_propa_def cdcl\<^sub>W_restart_mset.propagated_cons_eq_append_decide_cons)+

lemma no_smaller_propa_cons_trail_decided[simp]:
  \<open>no_smaller_propa S \<Longrightarrow> no_smaller_propa (cons_trail (Decided L) S) \<longleftrightarrow> (\<forall>L C. add_mset L C \<in># clauses S \<longrightarrow> undefined_lit (trail S)L \<longrightarrow> \<not>trail S \<Turnstile>as CNot C)\<close>
  by (auto simp: no_smaller_propa_def cdcl\<^sub>W_restart_mset.propagated_cons_eq_append_decide_cons
    decided_cons_eq_append_decide_cons)

lemma no_step_dpll_propagate_iff:
  \<open>no_step dpll_propagate S \<longleftrightarrow> (\<forall>L C. add_mset L C \<in># clauses S \<longrightarrow> undefined_lit (trail S)L \<longrightarrow> \<not>trail S \<Turnstile>as CNot C)\<close>
  by (auto simp: dpll_propagate.simps)

lemma count_decided_0_no_smaller_propa: \<open>count_decided (trail S) = 0 \<Longrightarrow> no_smaller_propa S\<close>
  by (auto simp: no_smaller_propa_def)

lemma no_smaller_propa_backtrack_split:
  \<open>no_smaller_propa S \<Longrightarrow>
       backtrack_split (trail S) = (M', L # M) \<Longrightarrow>
       no_smaller_propa (reduce_trail_to M S)\<close>
  using backtrack_split_list_eq[of \<open>trail S\<close>, symmetric]
  by (auto simp: no_smaller_propa_def)

lemma odpll\<^sub>W_core_stgy_no_smaller_propa:
  \<open>odpll\<^sub>W_core_stgy S T \<Longrightarrow> no_smaller_propa S \<Longrightarrow> no_smaller_propa T\<close>
  using no_step_dpll_backtrack_iff[of S] apply -
  by (induction rule: odpll\<^sub>W_core_stgy.induct)
   (auto 5 5 simp: cdcl\<^sub>W_restart_mset.propagated_cons_eq_append_decide_cons count_decided_0_no_smaller_propa
      dpll_propagate.simps dpll_decide.simps odecide.simps decided_cons_eq_append_decide_cons
      bnb.backtrack_opt.simps dpll_backtrack.simps no_step_dpll_conflict no_smaller_propa_backtrack_split)

lemma odpll\<^sub>W_bound_stgy_no_smaller_propa: \<open>bnb.dpll\<^sub>W_bound S T \<Longrightarrow> no_smaller_propa S \<Longrightarrow> no_smaller_propa T\<close>
  by (auto simp: cdcl\<^sub>W_restart_mset.propagated_cons_eq_append_decide_cons count_decided_0_no_smaller_propa
      dpll_propagate.simps dpll_decide.simps odecide.simps decided_cons_eq_append_decide_cons bnb.dpll\<^sub>W_bound.simps
      bnb.backtrack_opt.simps dpll_backtrack.simps no_step_dpll_conflict no_smaller_propa_backtrack_split)

lemma odpll\<^sub>W_bnb_stgy_no_smaller_propa:
  \<open>odpll\<^sub>W_bnb_stgy S T \<Longrightarrow> no_smaller_propa S \<Longrightarrow> no_smaller_propa T\<close>
  by (induction rule: odpll\<^sub>W_bnb_stgy.induct)
    (auto simp: odpll\<^sub>W_core_stgy_no_smaller_propa odpll\<^sub>W_bound_stgy_no_smaller_propa)

definition all_clauses_literals :: \<open>'v list\<close> where
  \<open>all_clauses_literals =
    (SOME xs. mset xs = mset_set ((\<Sigma> - \<Delta>\<Sigma>) \<union> replacement_neg ` \<Delta>\<Sigma> \<union> replacement_pos ` \<Delta>\<Sigma>))\<close>

definition base_atm :: \<open>'v \<Rightarrow> 'v\<close> where
  \<open>base_atm L = (if L \<in> \<Sigma> - \<Delta>\<Sigma> then L else
    if L \<in> replacement_neg ` \<Delta>\<Sigma> then (SOME K. (K \<in> \<Delta>\<Sigma> \<and> L = replacement_neg K))
    else (SOME K. (K \<in> \<Delta>\<Sigma> \<and> L = replacement_pos K)))\<close>

lemma normalize_lit_Some_simp[simp]: \<open>(SOME K. K \<in> \<Delta>\<Sigma> \<and> (L\<^sup>\<mapsto>\<^sup>0 = K\<^sup>\<mapsto>\<^sup>0)) = L\<close> if \<open>L \<in> \<Delta>\<Sigma>\<close> for K
  by (rule some1_equality) (use that in auto)

lemma base_atm_simps1[simp]:
  \<open>L \<in> \<Sigma> \<Longrightarrow> L \<notin> \<Delta>\<Sigma> \<Longrightarrow> base_atm L = L\<close>
  by (auto simp: base_atm_def)

lemma base_atm_simps2[simp]:
  \<open>L \<in> (\<Sigma> - \<Delta>\<Sigma>) \<union> replacement_neg ` \<Delta>\<Sigma> \<union> replacement_pos ` \<Delta>\<Sigma> \<Longrightarrow>
    K \<in> \<Sigma> \<Longrightarrow> K \<notin> \<Delta>\<Sigma> \<Longrightarrow> L \<in> \<Sigma> \<Longrightarrow> K = base_atm L \<longleftrightarrow> L = K\<close>
  by (auto simp: base_atm_def)

lemma base_atm_simps3[simp]:
  \<open>L \<in> \<Sigma> - \<Delta>\<Sigma> \<Longrightarrow> base_atm L \<in> \<Sigma>\<close>
  \<open>L \<in> replacement_neg ` \<Delta>\<Sigma> \<union> replacement_pos ` \<Delta>\<Sigma> \<Longrightarrow> base_atm L \<in> \<Delta>\<Sigma>\<close>
  apply (auto simp: base_atm_def)
  by (metis (mono_tags, lifting) tfl_some)

lemma base_atm_simps4[simp]:
  \<open>L \<in> \<Delta>\<Sigma> \<Longrightarrow> base_atm (replacement_pos L) = L\<close>
  \<open>L \<in> \<Delta>\<Sigma> \<Longrightarrow> base_atm (replacement_neg L) = L\<close>
  by (auto simp: base_atm_def)

definition opposite_var where
  \<open>opposite_var L = (if L \<in> replacement_pos ` \<Delta>\<Sigma> then replacement_neg (base_atm L)
    else replacement_pos (base_atm L))\<close>


lemma opposite_var_replacement_if[simp]:
  \<open>L \<in> (replacement_neg ` \<Delta>\<Sigma> \<union> replacement_pos ` \<Delta>\<Sigma>) \<Longrightarrow> A \<in> \<Delta>\<Sigma> \<Longrightarrow>
   opposite_var L = replacement_pos A \<longleftrightarrow> L = replacement_neg A\<close>
  \<open>L \<in> (replacement_neg ` \<Delta>\<Sigma> \<union> replacement_pos ` \<Delta>\<Sigma>) \<Longrightarrow> A \<in> \<Delta>\<Sigma> \<Longrightarrow>
   opposite_var L = replacement_neg A \<longleftrightarrow> L = replacement_pos A\<close>
  \<open>A \<in> \<Delta>\<Sigma> \<Longrightarrow> opposite_var (replacement_pos A) = replacement_neg A\<close>
  \<open>A \<in> \<Delta>\<Sigma> \<Longrightarrow> opposite_var (replacement_neg A) = replacement_pos A\<close>
  by (auto simp: opposite_var_def)

context
  assumes finite_\<Sigma>: \<open>finite \<Sigma>\<close>
begin
lemma all_clauses_literals:
  \<open>mset all_clauses_literals = mset_set ((\<Sigma> - \<Delta>\<Sigma>) \<union> replacement_neg ` \<Delta>\<Sigma> \<union> replacement_pos ` \<Delta>\<Sigma>)\<close>
  \<open>distinct all_clauses_literals\<close>
  \<open>set all_clauses_literals = ((\<Sigma> - \<Delta>\<Sigma>) \<union> replacement_neg ` \<Delta>\<Sigma> \<union> replacement_pos ` \<Delta>\<Sigma>)\<close>
proof -
  let ?A = \<open>mset_set ((\<Sigma> - \<Delta>\<Sigma>) \<union> replacement_neg ` \<Delta>\<Sigma> \<union>
      replacement_pos ` \<Delta>\<Sigma>)\<close>
  show 1: \<open>mset all_clauses_literals = ?A\<close>
    using someI[of \<open>\<lambda>xs. mset xs = ?A\<close>]
      finite_\<Sigma> ex_mset[of ?A]
    unfolding all_clauses_literals_def[symmetric]
    by metis
  show 2: \<open>distinct all_clauses_literals\<close>
    using someI[of \<open>\<lambda>xs. mset xs = ?A\<close>]
      finite_\<Sigma> ex_mset[of ?A]
    unfolding all_clauses_literals_def[symmetric]
    by (metis distinct_mset_mset_set distinct_mset_mset_distinct)
  show 3: \<open>set all_clauses_literals = ((\<Sigma> - \<Delta>\<Sigma>) \<union> replacement_neg ` \<Delta>\<Sigma> \<union> replacement_pos ` \<Delta>\<Sigma>)\<close>
    using arg_cong[OF 1, of set_mset] finite_\<Sigma>
    by simp
qed

definition unset_literals_in_\<Sigma> where
  \<open>unset_literals_in_\<Sigma>  M L \<longleftrightarrow> undefined_lit M (Pos L) \<and> L \<in> \<Sigma> - \<Delta>\<Sigma>\<close>

definition full_unset_literals_in_\<Delta>\<Sigma> where
  \<open>full_unset_literals_in_\<Delta>\<Sigma>  M L \<longleftrightarrow>
    undefined_lit M (Pos L) \<and> L \<notin> \<Sigma> - \<Delta>\<Sigma> \<and> undefined_lit M (Pos (opposite_var L)) \<and>
    L \<in> replacement_pos ` \<Delta>\<Sigma>\<close>

definition full_unset_literals_in_\<Delta>\<Sigma>' where
  \<open>full_unset_literals_in_\<Delta>\<Sigma>'  M L \<longleftrightarrow>
    undefined_lit M (Pos L) \<and> L \<notin> \<Sigma> - \<Delta>\<Sigma> \<and> undefined_lit M (Pos (opposite_var L)) \<and>
    L \<in> replacement_neg ` \<Delta>\<Sigma>\<close>

definition half_unset_literals_in_\<Delta>\<Sigma> where
  \<open>half_unset_literals_in_\<Delta>\<Sigma>  M L \<longleftrightarrow>
    undefined_lit M (Pos L) \<and> L \<notin> \<Sigma> - \<Delta>\<Sigma> \<and> defined_lit M (Pos (opposite_var L))\<close>

definition sorted_unadded_literals :: \<open>_ \<Rightarrow> 'v list\<close> where
\<open>sorted_unadded_literals M =
  (let
    M0 = filter (full_unset_literals_in_\<Delta>\<Sigma>' M) all_clauses_literals;
      \<comment> \<open>weight is 0\<close>
    M1 = filter (unset_literals_in_\<Sigma> M) all_clauses_literals;
      \<comment> \<open>weight is 2\<close>
    M2 = filter (full_unset_literals_in_\<Delta>\<Sigma> M) all_clauses_literals;
      \<comment> \<open>weight is 2\<close>
    M3 = filter (half_unset_literals_in_\<Delta>\<Sigma> M) all_clauses_literals
      \<comment> \<open>weight is 1\<close>
  in
    M0 @ M3 @ M1 @ M2)\<close>

definition complete_trail :: \<open>_ \<Rightarrow> _\<close> where
\<open>complete_trail M =
  (map (Decided o Neg) (sorted_unadded_literals M) @ M)\<close>

lemma in_sorted_unadded_literals_undefD:
  \<open>atm_of (lit_of l) \<in> set (sorted_unadded_literals M) \<Longrightarrow> l \<notin> set M\<close>
  \<open>atm_of (l') \<in> set (sorted_unadded_literals M) \<Longrightarrow> undefined_lit M l'\<close>
  \<open>xa \<in> set (sorted_unadded_literals M) \<Longrightarrow> lit_of x = Neg xa \<Longrightarrow>  x \<notin> set M\<close> and
  set_sorted_unadded_literals[simp]:
  \<open>set (sorted_unadded_literals M) =
     Set.filter (\<lambda>L. undefined_lit M (Pos L)) (set all_clauses_literals)\<close>
  by (auto simp: sorted_unadded_literals_def undefined_notin  all_clauses_literals(1,2)
    defined_lit_Neg_Pos_iff half_unset_literals_in_\<Delta>\<Sigma>_def full_unset_literals_in_\<Delta>\<Sigma>_def
    unset_literals_in_\<Sigma>_def Let_def full_unset_literals_in_\<Delta>\<Sigma>'_def
    all_clauses_literals(3))

lemma [simp]:
  \<open>full_unset_literals_in_\<Delta>\<Sigma> [] = (\<lambda>L. L \<in> replacement_pos ` \<Delta>\<Sigma>)\<close>
  \<open>full_unset_literals_in_\<Delta>\<Sigma>' [] = (\<lambda>L. L \<in> replacement_neg ` \<Delta>\<Sigma>)\<close>
  \<open>half_unset_literals_in_\<Delta>\<Sigma> [] = (\<lambda>L. False)\<close>
  \<open>unset_literals_in_\<Sigma> [] = (\<lambda>L. L \<in> \<Sigma> - \<Delta>\<Sigma>)\<close>
  by (auto simp: full_unset_literals_in_\<Delta>\<Sigma>_def
    unset_literals_in_\<Sigma>_def full_unset_literals_in_\<Delta>\<Sigma>'_def
    half_unset_literals_in_\<Delta>\<Sigma>_def intro!: ext)

lemma filter_disjount_union:
  \<open>(\<And>x. x \<in> set xs \<Longrightarrow> P x \<Longrightarrow> \<not>Q x) \<Longrightarrow>
   length (filter P xs) + length (filter Q xs) =
     length (filter (\<lambda>x. P x \<or> Q x) xs)\<close>
  by (induction xs) auto
lemma length_sorted_unadded_literals_empty[simp]:
  \<open>length (sorted_unadded_literals []) = length all_clauses_literals\<close>
  apply (auto simp: sorted_unadded_literals_def sum_length_filter_compl
    Let_def ac_simps filter_disjount_union)
  apply (subst filter_disjount_union)
  apply auto
  apply (subst filter_disjount_union)
  apply auto
  by (metis (no_types, lifting) Diff_iff UnE all_clauses_literals(3) filter_True)

lemma sorted_unadded_literals_Cons_notin_all_clauses_literals[simp]:
  assumes
    \<open>atm_of (lit_of K) \<notin> set all_clauses_literals\<close>
  shows
    \<open>sorted_unadded_literals (K # M) = sorted_unadded_literals M\<close>
proof -
  have [simp]: \<open>filter (full_unset_literals_in_\<Delta>\<Sigma>' (K # M))
                            all_clauses_literals =
                           filter (full_unset_literals_in_\<Delta>\<Sigma>' M)
                            all_clauses_literals\<close>
     \<open>filter (full_unset_literals_in_\<Delta>\<Sigma> (K # M))
                            all_clauses_literals =
                           filter (full_unset_literals_in_\<Delta>\<Sigma> M)
                            all_clauses_literals\<close>
     \<open>filter (half_unset_literals_in_\<Delta>\<Sigma> (K # M))
                            all_clauses_literals =
                           filter (half_unset_literals_in_\<Delta>\<Sigma> M)
                            all_clauses_literals\<close>
     \<open>filter (unset_literals_in_\<Sigma> (K # M)) all_clauses_literals =
       filter (unset_literals_in_\<Sigma> M) all_clauses_literals\<close>
   using assms unfolding full_unset_literals_in_\<Delta>\<Sigma>'_def  full_unset_literals_in_\<Delta>\<Sigma>_def
     half_unset_literals_in_\<Delta>\<Sigma>_def unset_literals_in_\<Sigma>_def
   by (auto simp: sorted_unadded_literals_def undefined_notin all_clauses_literals(1,2)
         defined_lit_Neg_Pos_iff all_clauses_literals(3) defined_lit_cons
        intro!: ext filter_cong)

  show ?thesis
    by (auto simp: undefined_notin all_clauses_literals(1,2)
      defined_lit_Neg_Pos_iff all_clauses_literals(3) sorted_unadded_literals_def)
qed

lemma sorted_unadded_literals_cong:
  assumes \<open>\<And>L. L \<in> set all_clauses_literals \<Longrightarrow> defined_lit M (Pos L) = defined_lit M' (Pos L)\<close>
  shows \<open>sorted_unadded_literals M = sorted_unadded_literals M'\<close>
proof -
  have [simp]: \<open>filter (full_unset_literals_in_\<Delta>\<Sigma>' (M))
                            all_clauses_literals =
                           filter (full_unset_literals_in_\<Delta>\<Sigma>' M')
                            all_clauses_literals\<close>
     \<open>filter (full_unset_literals_in_\<Delta>\<Sigma> (M))
                            all_clauses_literals =
                           filter (full_unset_literals_in_\<Delta>\<Sigma> M')
                            all_clauses_literals\<close>
     \<open>filter (half_unset_literals_in_\<Delta>\<Sigma> (M))
                            all_clauses_literals =
                           filter (half_unset_literals_in_\<Delta>\<Sigma> M')
                            all_clauses_literals\<close>
     \<open>filter (unset_literals_in_\<Sigma> (M)) all_clauses_literals =
       filter (unset_literals_in_\<Sigma> M') all_clauses_literals\<close>
   using assms unfolding full_unset_literals_in_\<Delta>\<Sigma>'_def  full_unset_literals_in_\<Delta>\<Sigma>_def
     half_unset_literals_in_\<Delta>\<Sigma>_def unset_literals_in_\<Sigma>_def
   by (auto simp: sorted_unadded_literals_def undefined_notin all_clauses_literals(1,2)
         defined_lit_Neg_Pos_iff all_clauses_literals(3) defined_lit_cons
        intro!: ext filter_cong)

  show ?thesis
    by (auto simp: undefined_notin all_clauses_literals(1,2)
      defined_lit_Neg_Pos_iff all_clauses_literals(3) sorted_unadded_literals_def)

qed

lemma sorted_unadded_literals_Cons_already_set[simp]:
  assumes
    \<open>defined_lit M (lit_of K)\<close>
  shows
    \<open>sorted_unadded_literals (K # M) = sorted_unadded_literals M\<close>
  by (rule sorted_unadded_literals_cong)
    (use assms in \<open>auto simp: defined_lit_cons\<close>)


lemma distinct_sorted_unadded_literals[simp]:
  \<open>distinct (sorted_unadded_literals M)\<close>
    unfolding half_unset_literals_in_\<Delta>\<Sigma>_def
      full_unset_literals_in_\<Delta>\<Sigma>_def unset_literals_in_\<Sigma>_def
      sorted_unadded_literals_def
      full_unset_literals_in_\<Delta>\<Sigma>'_def
  by (auto simp: sorted_unadded_literals_def all_clauses_literals(1,2))


lemma Collect_req_remove1:
  \<open>{a \<in> A. a \<noteq> b \<and> P a} = (if P b then Set.remove b {a \<in> A. P a} else {a \<in> A. P a})\<close> and
  Collect_req_remove2:
  \<open>{a \<in> A. b \<noteq> a \<and> P a} = (if P b then Set.remove b {a \<in> A. P a} else {a \<in> A. P a})\<close>
  by auto

lemma card_remove:
  \<open>card (Set.remove a A) = (if a \<in> A then card A - 1 else card A)\<close>
  apply (auto simp: Set.remove_def)
  by (metis Diff_empty One_nat_def card_Diff_insert card_infinite empty_iff
    finite_Diff_insert gr_implies_not0 neq0_conv zero_less_diff)

lemma isabelle_should_do_that_automatically: \<open>Suc (a - Suc 0) = a \<longleftrightarrow> a \<ge> 1\<close>
  by auto

lemma sorted_unadded_literals_cons_in_undef[simp]:
  \<open>undefined_lit M (lit_of K) \<Longrightarrow>
             atm_of (lit_of K) \<in> set all_clauses_literals \<Longrightarrow>
             Suc (length (sorted_unadded_literals (K # M))) =
             length (sorted_unadded_literals M)\<close>
  by (auto simp flip: distinct_card simp: Set.filter_def Collect_req_remove2
    card_remove isabelle_should_do_that_automatically
    card_gt_0_iff simp flip: less_eq_Suc_le)


lemma no_dup_complete_trail[simp]:
  \<open>no_dup (complete_trail M) \<longleftrightarrow> no_dup M\<close>
  by (auto simp: complete_trail_def no_dup_def comp_def all_clauses_literals(1,2)
    undefined_notin)

lemma tautology_complete_trail[simp]:
  \<open>tautology (lit_of `# mset (complete_trail M)) \<longleftrightarrow> tautology (lit_of `# mset M)\<close>
  apply (auto simp: complete_trail_def tautology_decomp' comp_def all_clauses_literals
          undefined_notin uminus_lit_swap defined_lit_Neg_Pos_iff
       simp flip: defined_lit_Neg_Pos_iff)
  apply (metis defined_lit_uminus uminus_Neg undefined_notin)+
  done

lemma atms_of_complete_trail:
  \<open>atms_of (lit_of `# mset (complete_trail M)) =
     atms_of (lit_of `# mset M) \<union> (\<Sigma> - \<Delta>\<Sigma>) \<union> replacement_neg ` \<Delta>\<Sigma> \<union> replacement_pos ` \<Delta>\<Sigma>\<close>
  by (auto simp add: complete_trail_def all_clauses_literals
    image_image image_Un atms_of_def defined_lit_map)

lemma length_complete_trail_Cons:
  \<open>no_dup (K # M) \<Longrightarrow>
    length (complete_trail (K # M)) =
      (if atm_of (lit_of K) \<in> set all_clauses_literals then 0 else 1) + length (complete_trail M)\<close>
  unfolding complete_trail_def by auto

lemma length_complete_trail[simp]: \<open>length (complete_trail []) = length all_clauses_literals\<close>
  unfolding complete_trail_def
  by (auto simp: sum_length_filter_compl)

lemma distinct_count_list_if: \<open>distinct xs \<Longrightarrow> count_list xs x = (if x \<in> set xs then 1 else 0)\<close>
  by (induction xs) auto

lemma length_complete_trail_eq:
  \<open>no_dup M \<Longrightarrow> atm_of ` (lits_of_l M) \<subseteq> set all_clauses_literals \<Longrightarrow>
  length (complete_trail M) = length all_clauses_literals\<close>
  by (induction M rule: ann_lit_list_induct) (auto simp: length_complete_trail_Cons)

lemma in_set_all_clauses_literals_simp[simp]:
  \<open>atm_of L \<in> \<Sigma> - \<Delta>\<Sigma> \<Longrightarrow> atm_of L \<in> set all_clauses_literals\<close>
  \<open>K \<in> \<Delta>\<Sigma> \<Longrightarrow> replacement_pos K \<in> set all_clauses_literals\<close>
  \<open>K \<in> \<Delta>\<Sigma> \<Longrightarrow> replacement_neg K \<in> set all_clauses_literals\<close>
  by (auto simp: all_clauses_literals)


abbreviation cut_and_complete_trail :: \<open>'st \<Rightarrow> 'v clause\<close> where
\<open>cut_and_complete_trail S \<equiv> lit_of `# mset (snd (backtrack_split (trail S)))\<close>


(*TODO prove that favouring conflict over propagate works [this is obvious, but still]...*)
inductive odpll\<^sub>W_core_stgy_count :: "'st \<times>'v clauses \<Rightarrow> 'st \<times> 'v clauses \<Rightarrow> bool" where
propagate: "dpll_propagate S T \<Longrightarrow> odpll\<^sub>W_core_stgy_count (S, C) (T, C)" |
decided: "odecide S T \<Longrightarrow> no_step dpll_propagate S  \<Longrightarrow> no_step dpll_backtrack S \<Longrightarrow>
  no_step dpll_conflict S \<Longrightarrow> odpll\<^sub>W_core_stgy_count (S, C) (T, C) " |
backtrack: "dpll_backtrack S T \<Longrightarrow> odpll\<^sub>W_core_stgy_count (S, C) (T, add_mset (cut_and_complete_trail S) C)" |
backtrack_opt: \<open>bnb.backtrack_opt S T \<Longrightarrow> odpll\<^sub>W_core_stgy_count (S, C) (T, add_mset (cut_and_complete_trail S) C)\<close>


inductive odpll\<^sub>W_bnb_stgy_count :: \<open>'st \<times> 'v clauses \<Rightarrow> 'st \<times> 'v clauses \<Rightarrow> bool\<close> where
dpll:
  \<open>odpll\<^sub>W_bnb_stgy_count S T\<close>
  if \<open>odpll\<^sub>W_core_stgy_count S T\<close> |
bnb:
  \<open>odpll\<^sub>W_bnb_stgy_count (S, C) (T, C)\<close>
  if \<open>bnb.dpll\<^sub>W_bound S T\<close>


lemma odpll\<^sub>W_core_stgy_countD:
  \<open>odpll\<^sub>W_core_stgy_count S T \<Longrightarrow> odpll\<^sub>W_core_stgy (fst S) (fst T)\<close>
  \<open>odpll\<^sub>W_core_stgy_count S T \<Longrightarrow> snd S \<subseteq># snd T\<close>
  by (induction rule: odpll\<^sub>W_core_stgy_count.induct; auto intro: odpll\<^sub>W_core_stgy.intros)+

lemma odpll\<^sub>W_bnb_stgy_countD:
  \<open>odpll\<^sub>W_bnb_stgy_count S T \<Longrightarrow> odpll\<^sub>W_bnb_stgy (fst S) (fst T)\<close>
  \<open>odpll\<^sub>W_bnb_stgy_count S T \<Longrightarrow> snd S \<subseteq># snd T\<close>
  by (induction rule: odpll\<^sub>W_bnb_stgy_count.induct; auto dest: odpll\<^sub>W_core_stgy_countD intro: odpll\<^sub>W_bnb_stgy.intros)+

lemma rtranclp_odpll\<^sub>W_bnb_stgy_countD:
  \<open>odpll\<^sub>W_bnb_stgy_count\<^sup>*\<^sup>* S T \<Longrightarrow> odpll\<^sub>W_bnb_stgy\<^sup>*\<^sup>* (fst S) (fst T)\<close>
  \<open>odpll\<^sub>W_bnb_stgy_count\<^sup>*\<^sup>* S T \<Longrightarrow> snd S \<subseteq># snd T\<close>
  by (induction rule: rtranclp_induct; auto dest: odpll\<^sub>W_bnb_stgy_countD)+

lemmas odpll\<^sub>W_core_stgy_count_induct = odpll\<^sub>W_core_stgy_count.induct[of \<open>(S, n)\<close> \<open>(T, m)\<close> for S n T m, split_format(complete), OF dpll_optimal_encoding_axioms,
   consumes 1]

definition no_conflict_of_constraint_on_trail :: \<open>'st \<Rightarrow> bool\<close> where
\<open>no_conflict_of_constraint_on_trail S \<longleftrightarrow>
  (\<forall>L \<in> \<Delta>\<Sigma>. \<forall>M M' K. trail S = M' @ Decided K # M \<longrightarrow> Pos (replacement_pos L) \<in> lits_of_l M \<longrightarrow> Pos (replacement_neg L) \<in> lits_of_l M \<longrightarrow> False)\<close>

lemma no_smaller_confl_no_conflict_of_constraint_on_trail:
  assumes
    \<open>clauses S = penc N\<close> and
    \<open>no_smaller_confl S\<close>
 shows
    \<open>no_conflict_of_constraint_on_trail S\<close>
  unfolding no_conflict_of_constraint_on_trail_def
proof (intro allI impI ballI)
  fix L M M' K
  assume \<open>L \<in> \<Delta>\<Sigma>\<close> and tr: \<open>trail S = M' @ Decided K # M\<close> and
   neg: \<open>Pos (replacement_pos L) \<in> lits_of_l M\<close>
    \<open>Pos (replacement_neg L) \<in> lits_of_l M\<close>
  have H: \<open>trail S = M' @ Decided K # M \<Longrightarrow> D \<in># clauses S \<Longrightarrow> \<not>M \<Turnstile>as CNot D\<close> for M K M' D
    using assms unfolding no_smaller_confl_def by auto
  have \<open>{#Neg (replacement_pos L), Neg (replacement_neg L)#} \<in># clauses S\<close>
    using assms(1) \<open>L \<in> \<Delta>\<Sigma>\<close> multi_member_split[of L \<open>mset_set \<Delta>\<Sigma>\<close>]
    by (auto simp: penc_def additional_constraints_def additional_constraint_def dest!: bspec[of _ _ L])
  from H[OF tr this] show \<open>False\<close>
    using neg by auto
qed

lemma
  assumes
    \<open>\<forall>L \<in> \<Delta>\<Sigma>. Pos (replacement_pos L) \<in> lits_of_l M \<longrightarrow> Pos (replacement_neg L) \<in> lits_of_l M \<longrightarrow> False\<close> and
    \<open>atm_of ` lits_of_l M \<subseteq> \<Sigma>\<close>
  shows
    \<open>\<forall>L \<in> \<Delta>\<Sigma>. Pos (replacement_pos L) \<in> lits_of_l (complete_trail M) \<longrightarrow> Pos (replacement_neg L) \<in> lits_of_l (complete_trail M) \<longrightarrow> False\<close>
  using assms
  apply (auto simp: complete_trail_def lits_of_def image_image)
  done

definition conflict_clauses_are_entailed :: \<open>'st \<times> 'v clauses \<Rightarrow> bool\<close> where
\<open>conflict_clauses_are_entailed =
  (\<lambda>(S, Cs). \<forall>C \<in># Cs. \<exists>M' K M. trail S = M' @ Propagated K () # M \<and> lit_of `# mset (Decided (-K) # M) \<subseteq># C)\<close>>

lemma propagated_cons_eq_append_propagated_cons:
 \<open>Propagated L () # M = M' @ Propagated K () # Ma \<longleftrightarrow>
  (M' = [] \<and> K = L \<and> M = Ma) \<or>
  (M' \<noteq> [] \<and> hd M' = Propagated L () \<and> M = tl M' @ Propagated K () # Ma)\<close>
  by (cases M')
    auto


lemma odpll\<^sub>W_core_stgy_count_conflict_clauses_are_entailed:
  assumes
    \<open>odpll\<^sub>W_core_stgy_count S T\<close> and
    \<open>conflict_clauses_are_entailed S\<close>
  shows
    \<open>conflict_clauses_are_entailed T\<close>
  using assms
  apply (induction rule: odpll\<^sub>W_core_stgy_count.induct)
  subgoal
    apply (auto simp: dpll_propagate.simps conflict_clauses_are_entailed_def
      cdcl\<^sub>W_restart_mset.propagated_cons_eq_append_decide_cons)
    by (metis append_Cons)
  subgoal for S T
    apply (auto simp: odecide.simps conflict_clauses_are_entailed_def
      dest!: multi_member_split intro: exI[of _ \<open>Decided _ # _\<close>])
    by (metis append_Cons)+
  subgoal for S T C
    using backtrack_split_list_eq[of \<open>trail S\<close>, symmetric]
      backtrack_split_snd_hd_decided[of \<open>trail S\<close>]
    apply (auto simp: dpll_backtrack.simps conflict_clauses_are_entailed_def
        propagated_cons_eq_append_propagated_cons is_decided_def append_eq_append_conv2
        eq_commute[of _ \<open>Propagated _ () # _\<close>] conj_disj_distribR ex_disj_distrib
      cdcl\<^sub>W_restart_mset.propagated_cons_eq_append_decide_cons
      dest!: multi_member_split
      simp del: backtrack_split_list_eq
     )
    using subset_mset.dual_order.trans apply force
    by (metis append.left_neutral cdcl\<^sub>W_restart_mset.propagated_cons_eq_append_decide_cons list.distinct(1) list.sel(1) list.sel(3) tl_append2)
  subgoal for S T C
    using backtrack_split_list_eq[of \<open>trail S\<close>, symmetric]
      backtrack_split_snd_hd_decided[of \<open>trail S\<close>]
    apply (auto simp: bnb.backtrack_opt.simps conflict_clauses_are_entailed_def
        propagated_cons_eq_append_propagated_cons is_decided_def append_eq_append_conv2
        eq_commute[of _ \<open>Propagated _ () # _\<close>] conj_disj_distribR ex_disj_distrib
      cdcl\<^sub>W_restart_mset.propagated_cons_eq_append_decide_cons
      dest!: multi_member_split
      simp del: backtrack_split_list_eq
     )
    using subset_mset.dual_order.trans apply force
    by (metis append.left_neutral cdcl\<^sub>W_restart_mset.propagated_cons_eq_append_decide_cons list.distinct(1) list.sel(1) list.sel(3) tl_append2)
  done

lemma odpll\<^sub>W_core_stgy_count_conflict_clauses_are_entailed:
  assumes
    \<open>odpll\<^sub>W_core_stgy_count S T\<close> and
    \<open>conflict_clauses_are_entailed S\<close> and
    \<open>distinct_mset (snd S)\<close>
  shows
    \<open>distinct_mset (snd T)\<close>
  using assms(1,2,3) odpll\<^sub>W_core_stgy_count_conflict_clauses_are_entailed[OF assms(1,2)]
  apply (induction rule: odpll\<^sub>W_core_stgy_count.induct)
  subgoal
    by (auto simp: dpll_propagate.simps conflict_clauses_are_entailed_def
      cdcl\<^sub>W_restart_mset.propagated_cons_eq_append_decide_cons)
  subgoal
    by (auto simp:)
  subgoal for S T C
    apply (clarsimp simp: dpll_backtrack.simps dest!: multi_member_split)
    (* a trail does not entail a subset *)
     sorry

oops

lemma
  assumes \<open>clauses S = penc N\<close> \<open>atms_of_mm N = \<Sigma>\<close> and
    \<open>odpll\<^sub>W_bnb_stgy_count\<^sup>*\<^sup>* (S, n) (T, m)\<close> and
    tr: \<open>trail S = []\<close>
  shows \<open>size m < 3 ^ (card \<Sigma>) + size n\<close>
proof -
  have \<open>no_smaller_confl S\<close> \<open>no_smaller_propa S\<close>
    using tr unfolding no_smaller_confl_def no_smaller_propa_def by auto


oops
  
end

end