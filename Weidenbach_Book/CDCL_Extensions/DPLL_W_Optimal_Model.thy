theory DPLL_W_Optimal_Model
imports
  CDCL_W_Optimal_Model
  CDCL.DPLL_W
begin

lemma funpow_tl_append_skip_last:
  \<open>((tl ^^ length M') (M' @ M)) = M\<close>
  by (induction M')
    (auto simp del: funpow.simps(2) simp: funpow_Suc_right)

(*TODO MOVE*)
text \<open>The following version is more suited than @{thm backtrack_split_some_is_decided_then_snd_has_hd}
 for direct use.\<close>
lemma backtrack_split_some_is_decided_then_snd_has_hd':
  \<open>l\<in>set M \<Longrightarrow> is_decided l \<Longrightarrow> \<exists>M' L' M''. backtrack_split M = (M'', L' # M')\<close>
  by (metis backtrack_snd_empty_not_decided list.exhaust prod.collapse)

lemma total_over_m_entailed_or_conflict:
  shows \<open>total_over_m M N \<Longrightarrow> M \<Turnstile>s N \<or> (\<exists>C \<in> N. M \<Turnstile>s CNot C)\<close>
  by (metis Set.set_insert total_not_true_cls_true_clss_CNot total_over_m_empty total_over_m_insert true_clss_def)

locale dpll_ops =
  fixes
    trail :: \<open>'st \<Rightarrow> 'v  dpll\<^sub>W_ann_lits\<close> and
    clauses :: \<open>'st \<Rightarrow> 'v clauses\<close> and
    tl_trail :: \<open>'st \<Rightarrow> 'st\<close> and
    cons_trail :: \<open>'v  dpll\<^sub>W_ann_lit \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    state_eq  :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> (infix "\<sim>" 50) and
    state :: \<open>'st \<Rightarrow> 'v  dpll\<^sub>W_ann_lits \<times> 'v clauses \<times> 'b\<close> 
begin

definition additional_info :: \<open>'st \<Rightarrow> 'b\<close> where
  \<open>additional_info S = (\<lambda>(M, N, w). w) (state S)\<close>

end

locale bnb_ops =
  fixes
    trail :: \<open>'st \<Rightarrow> 'v  dpll\<^sub>W_ann_lits\<close> and
    clauses :: \<open>'st \<Rightarrow> 'v clauses\<close> and
    tl_trail :: \<open>'st \<Rightarrow> 'st\<close> and
    cons_trail :: \<open>'v  dpll\<^sub>W_ann_lit \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    state_eq  :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> (infix "\<sim>" 50) and
    state :: \<open>'st \<Rightarrow> 'v  dpll\<^sub>W_ann_lits \<times> 'v clauses \<times> 'a \<times> 'b\<close> and
    weight :: \<open>'st \<Rightarrow> 'a\<close> and
    update_weight_information :: "'v dpll\<^sub>W_ann_lits \<Rightarrow> 'st \<Rightarrow> 'st" and
    is_improving_int :: "'v  dpll\<^sub>W_ann_lits \<Rightarrow> 'v  dpll\<^sub>W_ann_lits \<Rightarrow> 'v clauses \<Rightarrow> 'a \<Rightarrow> bool" and
    conflicting_clauses :: "'v clauses \<Rightarrow> 'a \<Rightarrow> 'v clauses"
begin

interpretation dpll: dpll_ops where
  trail = trail and
  clauses = clauses and
  tl_trail = tl_trail and
  cons_trail = cons_trail and
  state_eq = state_eq and
  state = state
  .

definition conflicting_clss :: \<open>'st \<Rightarrow> 'v literal multiset multiset\<close> where
  \<open>conflicting_clss S = conflicting_clauses (clauses S) (weight S)\<close>

definition abs_state where
  \<open>abs_state S = (trail S, clauses S + conflicting_clss S)\<close>

abbreviation is_improving where
  \<open>is_improving M M' S \<equiv> is_improving_int M M' (clauses S) (weight S)\<close>

definition state' :: \<open>'st \<Rightarrow> 'v  dpll\<^sub>W_ann_lits \<times> 'v clauses \<times> 'a \<times> 'v clauses\<close> where
  \<open>state' S = (trail S, clauses S, weight S, conflicting_clss S)\<close>

definition additional_info :: \<open>'st \<Rightarrow> 'b\<close> where
  \<open>additional_info S = (\<lambda>(M, N, _, w). w) (state S)\<close>


end


locale dpll\<^sub>W_state =
  dpll_ops trail clauses
    tl_trail cons_trail state_eq state
  for
    trail :: \<open>'st \<Rightarrow> 'v  dpll\<^sub>W_ann_lits\<close> and
    clauses :: \<open>'st \<Rightarrow> 'v clauses\<close> and
    tl_trail :: \<open>'st \<Rightarrow> 'st\<close> and
    cons_trail :: \<open>'v  dpll\<^sub>W_ann_lit \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    state_eq  :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> (infix "\<sim>" 50) and
    state :: \<open>'st \<Rightarrow> 'v  dpll\<^sub>W_ann_lits \<times> 'v clauses \<times> 'b\<close> +
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
    state:
       \<open>state S = (trail S, clauses S, additional_info S)\<close>
begin

end

locale bnb =
  bnb_ops trail clauses
    tl_trail cons_trail state_eq state weight update_weight_information is_improving_int conflicting_clauses
  for
    weight :: \<open>'st \<Rightarrow> 'a\<close> and
    update_weight_information :: "'v dpll\<^sub>W_ann_lits \<Rightarrow> 'st \<Rightarrow> 'st" and
    is_improving_int :: "'v  dpll\<^sub>W_ann_lits \<Rightarrow> 'v  dpll\<^sub>W_ann_lits \<Rightarrow> 'v clauses \<Rightarrow> 'a \<Rightarrow> bool" and
    trail :: \<open>'st \<Rightarrow> 'v  dpll\<^sub>W_ann_lits\<close> and
    clauses :: \<open>'st \<Rightarrow> 'v clauses\<close> and
    tl_trail :: \<open>'st \<Rightarrow> 'st\<close> and
    cons_trail :: \<open>'v  dpll\<^sub>W_ann_lit \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    state_eq  :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> (infix "\<sim>" 50) and
    conflicting_clauses :: "'v clauses \<Rightarrow> 'a \<Rightarrow> 'v clauses"and
    state :: \<open>'st \<Rightarrow> 'v  dpll\<^sub>W_ann_lits \<times> 'v clauses \<times> 'a \<times> 'b\<close> +
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
       \<open>state S = (M, N, w, oth) \<Longrightarrow>
          \<exists>w'. state (update_weight_information M' S) = (M, N, w', oth)\<close> and

    conflicting_clss_update_weight_information_mono:
      \<open>dpll\<^sub>W_all_inv (abs_state S) \<Longrightarrow> is_improving M M' S \<Longrightarrow>
        conflicting_clss S \<subseteq># conflicting_clss (update_weight_information M' S)\<close> and
    conflicting_clss_update_weight_information_in:
      \<open>is_improving M M' S \<Longrightarrow> negate_ann_lits M' \<in># conflicting_clss (update_weight_information M' S)\<close> and
    atms_of_conflicting_clss:
      \<open>atms_of_mm (conflicting_clss S) \<subseteq> atms_of_mm (clauses S)\<close> and
    state:
       \<open>state S = (trail S, clauses S, weight S, additional_info S)\<close>
begin

lemma [simp]: \<open>DPLL_W.clauses (abs_state S) = clauses S + conflicting_clss S\<close>
  \<open>DPLL_W.trail (abs_state S) = trail S\<close>
  by (auto simp: abs_state_def)


lemma [simp]: \<open>trail (update_weight_information M' S) = trail S\<close>
  using update_weight_information[of S]
  by (auto simp: state)

lemma [simp]:
  \<open>clauses (update_weight_information M' S) = clauses S\<close>
  \<open>weight (cons_trail uu S) = weight S\<close>
  \<open>clauses (cons_trail uu S) = clauses S\<close>
  \<open>conflicting_clss (cons_trail uu S) = conflicting_clss S\<close>
  \<open>trail (cons_trail uu S) = uu # trail S\<close>
  \<open>trail (tl_trail S) = tl (trail S)\<close>
  \<open>clauses (tl_trail S) = clauses (S)\<close>
  \<open>weight (tl_trail S) = weight (S)\<close>
  \<open>conflicting_clss (tl_trail S) = conflicting_clss (S)\<close>
  \<open>additional_info (cons_trail L S) = additional_info S\<close>
  \<open>additional_info (tl_trail S) = additional_info S\<close>
  \<open>additional_info (update_weight_information M' S) = additional_info S\<close>
  using update_weight_information[of S]
    cons_trail[of S]
    tl_trail[of S]
  by (auto simp: state conflicting_clss_def)

lemma state_simp[simp]:
  \<open>T \<sim> S \<Longrightarrow> trail T = trail S\<close>
  \<open>T \<sim> S \<Longrightarrow> clauses T = clauses S\<close>
  \<open>T \<sim> S \<Longrightarrow> weight T = weight S\<close>
  \<open>T \<sim> S \<Longrightarrow> conflicting_clss T = conflicting_clss S\<close>
  by (auto dest!: state_eq_state simp: state conflicting_clss_def)


interpretation dpll: dpll_ops trail clauses tl_trail cons_trail state_eq state
  .

interpretation dpll: dpll\<^sub>W_state trail clauses tl_trail cons_trail state_eq state
  apply standard
  apply (auto dest: state_eq_sym[THEN iffD1] intro: state_eq_trans dest: state_eq_state)
  apply (auto simp: state cons_trail dpll.additional_info_def)
  done


text \<open>
  In the definition below the \<^term>\<open>state' T = (Propagated L () # trail
  S, clauses S, weight S, conflicting_clss S)\<close> are not necessary, but
  avoids to change the DPLL formalisation with proper locales, as we
  did for CDCL.

  The DPLL calculus looks slightly more general than the CDCL calculus
  because we can take any conflicting clause from \<^term>\<open>conflicting_clss S\<close>.
  However, this does not make a difference for the trail, as we backtrack
  to the last decision independantly of the conflict.
\<close>
inductive dpll\<^sub>W_core :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S T where
propagate: "add_mset L C \<in># clauses S \<Longrightarrow> trail S \<Turnstile>as CNot C \<Longrightarrow> undefined_lit (trail S) L \<Longrightarrow>
  T \<sim> cons_trail (Propagated L ()) S \<Longrightarrow>
  dpll\<^sub>W_core S T" |
decided: "undefined_lit (trail S) L \<Longrightarrow> atm_of L \<in> atms_of_mm (clauses S) \<Longrightarrow>
  T \<sim> cons_trail (Decided L) S \<Longrightarrow>
  dpll\<^sub>W_core S T " |
backtrack: "backtrack_split (trail S) = (M', L # M) \<Longrightarrow> is_decided L \<Longrightarrow> D \<in># clauses S
  \<Longrightarrow> trail S \<Turnstile>as CNot D
  \<Longrightarrow> state' T = (Propagated (- (lit_of L)) () # M, clauses S, weight S, conflicting_clss S)
  \<Longrightarrow> trail S \<Turnstile>as CNot D \<Longrightarrow> dpll\<^sub>W_core S T" |
backtrack_opt: "backtrack_split (trail S) = (M', L # M) \<Longrightarrow> is_decided L \<Longrightarrow> D \<in># conflicting_clss S
  \<Longrightarrow> trail S \<Turnstile>as CNot D
  \<Longrightarrow> state' T = (Propagated (- (lit_of L)) () # M, clauses S, weight S, conflicting_clss S)
  \<Longrightarrow> dpll\<^sub>W_core S T"

inductive_cases dpll\<^sub>W_coreE: \<open>dpll\<^sub>W_core S T\<close>

inductive dpll\<^sub>W_branch :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
update_info:
  \<open>is_improving M M' S \<Longrightarrow> T \<sim> (update_weight_information M' S)
   \<Longrightarrow> dpll\<^sub>W_branch S T\<close>

inductive dpll\<^sub>W_bnb :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> where
dpll:
  \<open>dpll\<^sub>W_bnb S T\<close>
  if \<open>dpll\<^sub>W_core S T\<close> |
bnb:
  \<open>dpll\<^sub>W_bnb S T\<close>
  if \<open>dpll\<^sub>W_branch S T\<close>

inductive_cases dpll\<^sub>W_bnbE: \<open>dpll\<^sub>W_bnb S T\<close>

lemma dpll\<^sub>W_core_is_dpll\<^sub>W:
  \<open>dpll\<^sub>W_core S T \<Longrightarrow> dpll\<^sub>W (abs_state S) (abs_state T)\<close>
  supply abs_state_def[simp] state'_def[simp]
  apply (induction rule: dpll\<^sub>W_core.induct)
  subgoal
    by (auto simp: dpll\<^sub>W.simps dest!: )
  subgoal
    by (auto simp: dpll\<^sub>W.simps dest!: )
  subgoal
    by (auto simp: dpll\<^sub>W.simps)
  subgoal
    by (auto simp: dpll\<^sub>W.simps)
  done

lemma dpll\<^sub>W_core_abs_state_all_inv:
  \<open>dpll\<^sub>W_core S T \<Longrightarrow> dpll\<^sub>W_all_inv (abs_state S) \<Longrightarrow> dpll\<^sub>W_all_inv (abs_state T)\<close>
  by (auto dest!: dpll\<^sub>W_core_is_dpll\<^sub>W intro: dpll\<^sub>W_all_inv)

lemma dpll\<^sub>W_core_same_weight:
  \<open>dpll\<^sub>W_core S T \<Longrightarrow> weight S = weight T\<close>
  supply abs_state_def[simp] state'_def[simp]
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

lemma dpll\<^sub>W_branch_trail:
    \<open>dpll\<^sub>W_branch S T \<Longrightarrow> trail S = trail T\<close> and
   dpll\<^sub>W_branch_clauses:
    \<open>dpll\<^sub>W_branch S T \<Longrightarrow> clauses S = clauses T\<close> and
  dpll\<^sub>W_branch_conflicting_clss:
    \<open>dpll\<^sub>W_branch S T \<Longrightarrow> dpll\<^sub>W_all_inv (abs_state S) \<Longrightarrow> conflicting_clss S \<subseteq># conflicting_clss T\<close>
  subgoal
    by (induction rule: dpll\<^sub>W_branch.induct)
     (auto simp: dpll\<^sub>W_all_inv_def state dest!: conflicting_clss_update_weight_information_mono)
  subgoal
    by (induction rule: dpll\<^sub>W_branch.induct)
     (auto simp: dpll\<^sub>W_all_inv_def state dest!: conflicting_clss_update_weight_information_mono)
  subgoal
    by (induction rule: dpll\<^sub>W_branch.induct)
      (auto simp: state conflicting_clss_def
        dest!: conflicting_clss_update_weight_information_mono)
  done

lemma dpll\<^sub>W_branch_abs_state_all_inv:
  \<open>dpll\<^sub>W_branch S T \<Longrightarrow> dpll\<^sub>W_all_inv (abs_state S) \<Longrightarrow> dpll\<^sub>W_all_inv (abs_state T)\<close>
  using dpll\<^sub>W_branch_conflicting_clss[of S T] dpll\<^sub>W_branch_clauses[of S T]
   atms_of_conflicting_clss[of T] atms_of_conflicting_clss[of S]
  apply (auto simp: dpll\<^sub>W_all_inv_def dpll\<^sub>W_branch_trail lits_of_def image_image
    intro: all_decomposition_implies_mono[OF set_mset_mono] dest: dpll\<^sub>W_branch_conflicting_clss)
  by (blast intro: all_decomposition_implies_mono)

lemma dpll\<^sub>W_bnb_abs_state_all_inv:
  \<open>dpll\<^sub>W_bnb S T \<Longrightarrow> dpll\<^sub>W_all_inv (abs_state S) \<Longrightarrow> dpll\<^sub>W_all_inv (abs_state T)\<close>
  by (auto elim!: dpll\<^sub>W_bnb.cases intro: dpll\<^sub>W_branch_abs_state_all_inv dpll\<^sub>W_core_abs_state_all_inv)

lemma rtranclp_dpll\<^sub>W_bnb_abs_state_all_inv:
  \<open>dpll\<^sub>W_bnb\<^sup>*\<^sup>* S T \<Longrightarrow> dpll\<^sub>W_all_inv (abs_state S) \<Longrightarrow> dpll\<^sub>W_all_inv (abs_state T)\<close>
  by (induction rule: rtranclp_induct)
   (auto simp: dpll\<^sub>W_bnb_abs_state_all_inv)

lemma dpll\<^sub>W_core_clauses:
  \<open>dpll\<^sub>W_core S T \<Longrightarrow> clauses S = clauses T\<close>
  supply abs_state_def[simp] state'_def[simp]
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

lemma dpll\<^sub>W_bnb_clauses:
  \<open>dpll\<^sub>W_bnb S T \<Longrightarrow> clauses S = clauses T\<close>
  by (auto elim!: dpll\<^sub>W_bnbE simp: dpll\<^sub>W_branch_clauses dpll\<^sub>W_core_clauses)

lemma rtranclp_dpll\<^sub>W_bnb_clauses:
  \<open>dpll\<^sub>W_bnb\<^sup>*\<^sup>* S T \<Longrightarrow> clauses S = clauses T\<close>
  by (induction rule: rtranclp_induct)
    (auto simp:  dpll\<^sub>W_bnb_clauses)


lemma atms_of_clauses_conflicting_clss[simp]:
  \<open>atms_of_mm (clauses S) \<union> atms_of_mm (conflicting_clss S) = atms_of_mm (clauses S)\<close>
  using atms_of_conflicting_clss[of S] by blast

lemma wf_dpll\<^sub>W_bnb_bnb: (* \htmllink{wf_dpll_bnb} *)
  assumes improve: \<open>\<And>S T. dpll\<^sub>W_branch S T \<Longrightarrow> clauses S = N \<Longrightarrow> (\<nu> (weight T), \<nu> (weight S)) \<in> R\<close> and
    wf_R: \<open>wf R\<close>
  shows \<open>wf {(T, S). dpll\<^sub>W_all_inv (abs_state S) \<and> dpll\<^sub>W_bnb S T \<and>
      clauses S = N}\<close>
    (is \<open>wf ?A\<close>)
proof -
  let ?R = \<open>{(T, S). (\<nu> (weight T), \<nu> (weight S)) \<in> R}\<close>

  have \<open>wf {(T, S). dpll\<^sub>W_all_inv S \<and> dpll\<^sub>W S T}\<close>
    by (rule wf_dpll\<^sub>W)
  from wf_if_measure_f[OF this, of abs_state]
  have wf: \<open>wf {(T, S).  dpll\<^sub>W_all_inv (abs_state S) \<and>
      dpll\<^sub>W (abs_state S) (abs_state T) \<and> weight S = weight T}\<close>
    (is \<open>wf ?CDCL\<close>)
    by (rule wf_subset) auto
  have \<open>wf (?R \<union> ?CDCL)\<close>
    apply (rule wf_union_compatible)
    subgoal by (rule wf_if_measure_f[OF wf_R, of \<open>\<lambda>x. \<nu> (weight x)\<close>])
    subgoal by (rule wf)
    subgoal by (auto simp: dpll\<^sub>W_core_same_weight)
    done

  moreover have \<open>?A \<subseteq> ?R \<union> ?CDCL\<close>
    by (auto elim!: dpll\<^sub>W_bnbE dest: dpll\<^sub>W_core_abs_state_all_inv dpll\<^sub>W_core_is_dpll\<^sub>W
      simp: dpll\<^sub>W_core_same_weight improve)
  ultimately show ?thesis
    by (rule wf_subset)
qed

lemma state_tl_trail: \<open>state (tl_trail S) = (tl (trail S), clauses S, weight S, additional_info S)\<close>
  by (auto simp: state)

lemma state_tl_trail_comp_pow: \<open>state ((tl_trail ^^ n) S) = ((tl ^^ n) (trail S), clauses S, weight S, additional_info S)\<close>
  apply (induction n)
    using state apply fastforce
  apply (auto simp: state_tl_trail state)[]
  done


lemma [simp]:
  \<open>weight ((tl_trail ^^ n) S) = weight S\<close>
  \<open>trail ((tl_trail ^^ n) S) = (tl ^^ n) (trail S)\<close>
  \<open>clauses ((tl_trail ^^ n) S) = clauses S\<close>
  \<open>conflicting_clss ((tl_trail ^^ n) S) = conflicting_clss S\<close>
  using state_tl_trail_comp_pow[of n S]
  by (auto simp: state conflicting_clss_def)

lemma dpll\<^sub>W_core_Ex_propagate:
  \<open>add_mset L C \<in># clauses S \<Longrightarrow> trail S \<Turnstile>as CNot C \<Longrightarrow> undefined_lit (trail S) L \<Longrightarrow>
    Ex (dpll\<^sub>W_core S)\<close> and
   dpll\<^sub>W_core_Ex_decide:
   "undefined_lit (trail S) L \<Longrightarrow> atm_of L \<in> atms_of_mm (clauses S) \<Longrightarrow>
     Ex (dpll\<^sub>W_core S)" and
    dpll\<^sub>W_core_Ex_backtrack: "backtrack_split (trail S) = (M', L' # M) \<Longrightarrow> is_decided L' \<Longrightarrow> D \<in># clauses S \<Longrightarrow>
   trail S \<Turnstile>as CNot D \<Longrightarrow> Ex (dpll\<^sub>W_core S)" and
    dpll\<^sub>W_core_Ex_backtrack_opt: "backtrack_split (trail S) = (M', L' # M) \<Longrightarrow> is_decided L' \<Longrightarrow> D \<in># conflicting_clss S
  \<Longrightarrow> trail S \<Turnstile>as CNot D \<Longrightarrow>
   Ex (dpll\<^sub>W_core S)"
  subgoal
    by (rule exI[of _ \<open>cons_trail (Propagated L ()) S\<close>])
     (fastforce simp: dpll\<^sub>W_core.simps state_eq_ref)
  subgoal
    by (rule exI[of _ \<open>cons_trail (Decided L) S\<close>])
     (auto simp: dpll\<^sub>W_core.simps state'_def)
  subgoal
    using backtrack_split_list_eq[of \<open>trail S\<close>, symmetric] apply -
    apply (rule exI[of _ \<open>cons_trail (Propagated (-lit_of L') ()) ((tl_trail ^^ (length (L' # M'))) S)\<close>])
    apply (auto simp: dpll\<^sub>W_core.simps state'_def state_tl_trail_comp_pow funpow_tl_append_skip_last)
    done
  subgoal
    using backtrack_split_list_eq[of \<open>trail S\<close>, symmetric] apply -
    apply (rule exI[of _ \<open>cons_trail (Propagated (-lit_of L') ()) ((tl_trail ^^ (length (L' # M'))) S)\<close>])
    apply (auto simp: dpll\<^sub>W_core.simps state'_def state_tl_trail_comp_pow funpow_tl_append_skip_last)
    done
  done


text \<open>
  Unlike the CDCL case, we do not need assumptions on improve. The reason behind it is that
  we do not need any strategy on propagation and decisions.
\<close>
lemma no_step_dpll_bnb_dpll\<^sub>W:
  assumes
    ns: \<open>no_step dpll\<^sub>W_bnb S\<close> and
    struct_invs: \<open>dpll\<^sub>W_all_inv (abs_state S)\<close>
  shows \<open>no_step dpll\<^sub>W (abs_state S)\<close>
proof -
  have no_decide: \<open>atm_of L \<in> atms_of_mm (clauses S) \<Longrightarrow>
                  defined_lit (trail S) L\<close> for L
    using spec[OF ns, of \<open>cons_trail _ S\<close>]
    apply (fastforce simp: dpll\<^sub>W_bnb.simps total_over_m_def total_over_set_def
      dpll\<^sub>W_core.simps state'_def)
    done
  have [intro]: \<open>is_decided L \<Longrightarrow>
       backtrack_split (trail S) = (M', L # M) \<Longrightarrow>
       trail S \<Turnstile>as CNot D \<Longrightarrow> D \<in># clauses S \<Longrightarrow> False\<close> for M' L M D
    using dpll\<^sub>W_core_Ex_backtrack[of S M' L M D] ns
    by (auto simp: dpll\<^sub>W_bnb.simps)
  have [intro]: \<open>is_decided L \<Longrightarrow>
       backtrack_split (trail S) = (M', L # M) \<Longrightarrow>
       trail S \<Turnstile>as CNot D \<Longrightarrow> D \<in># conflicting_clss S \<Longrightarrow> False\<close> for M' L M D
    using dpll\<^sub>W_core_Ex_backtrack_opt[of S M' L M D] ns
    by (auto simp: dpll\<^sub>W_bnb.simps)
  have tot: \<open>total_over_m (lits_of_l (trail S)) (set_mset (clauses S))\<close>
    using no_decide
    by (force simp: total_over_m_def total_over_set_def state'_def
      Decided_Propagated_in_iff_in_lits_of_l)
  have [simp]: \<open>add_mset L C \<in># clauses S \<Longrightarrow> defined_lit (trail S) L\<close> for L C
     using no_decide
    by (auto dest!: multi_member_split)
  have [simp]: \<open>add_mset L C \<in># conflicting_clss S \<Longrightarrow> defined_lit (trail S) L\<close> for L C
     using no_decide atms_of_conflicting_clss[of S]
    by (auto dest!: multi_member_split)
  show ?thesis
    by (auto simp: dpll\<^sub>W.simps no_decide)
qed


context
  assumes can_always_improve:
     \<open>\<And>S. trail S \<Turnstile>asm clauses S \<Longrightarrow> (\<forall>C \<in># conflicting_clss S. \<not> trail S \<Turnstile>as CNot C) \<Longrightarrow>
       dpll\<^sub>W_all_inv (abs_state S) \<Longrightarrow>
       total_over_m (lits_of_l (trail S)) (set_mset (clauses S)) \<Longrightarrow> Ex (dpll\<^sub>W_branch S)\<close>
begin

lemma no_step_dpll\<^sub>W_bnb_conflict:
  assumes
    ns: \<open>no_step dpll\<^sub>W_bnb S\<close> and
    invs: \<open>dpll\<^sub>W_all_inv (abs_state S)\<close>
  shows \<open>\<exists>C \<in># clauses S + conflicting_clss S. trail S \<Turnstile>as CNot C\<close> (is ?A) and
      \<open>count_decided (trail S) = 0\<close> and
     \<open>unsatisfiable (set_mset (clauses S + conflicting_clss S))\<close>
proof (rule ccontr)
  have no_decide: \<open>atm_of L \<in> atms_of_mm (clauses S) \<Longrightarrow> defined_lit (trail S) L\<close> for L
    using spec[OF ns, of \<open>cons_trail _ S\<close>]
    apply (fastforce simp: dpll\<^sub>W_bnb.simps total_over_m_def total_over_set_def
      dpll\<^sub>W_core.simps state'_def)
    done
  have tot: \<open>total_over_m (lits_of_l (trail S)) (set_mset (clauses S))\<close>
    using no_decide
    by (force simp: total_over_m_def total_over_set_def state'_def
      Decided_Propagated_in_iff_in_lits_of_l)
  have dec0: \<open>count_decided (trail S) = 0\<close> if ent: \<open>?A\<close>
  proof -
    obtain C where
      \<open>C \<in># clauses S + conflicting_clss S\<close> and
      \<open>trail S \<Turnstile>as CNot C\<close>
      using ent tot ns invs
      by (auto simp: dpll\<^sub>W_bnb.simps)
    then show \<open>count_decided (trail S) = 0\<close>
      using ns  dpll\<^sub>W_core_Ex_backtrack[of S _ _ _ C]  dpll\<^sub>W_core_Ex_backtrack_opt[of S _ _ _ C]
      unfolding count_decided_0_iff
      apply clarify
      apply (frule backtrack_split_some_is_decided_then_snd_has_hd'[of _ \<open>trail S\<close>], assumption)
     apply (auto simp: dpll\<^sub>W_bnb.simps count_decided_0_iff)
     apply (metis backtrack_split_snd_hd_decided list.sel(1) list.simps(3) snd_conv)+
     done
   qed

  show A: False if \<open>\<not>?A\<close>
  proof -
    have \<open>trail S \<Turnstile>a C\<close> if \<open>C \<in># clauses S + conflicting_clss S\<close> for C
    proof -
      have \<open>\<not> trail S \<Turnstile>as CNot C\<close>
        using \<open>\<not>?A\<close> that by (auto dest!: multi_member_split)
      then show \<open>?thesis\<close>
        using tot that
        total_not_true_cls_true_clss_CNot[of \<open>lits_of_l (trail S)\<close> C]
          apply (auto simp: true_annots_def simp del: true_clss_def_iff_negation_in_model  dest!: multi_member_split )
          using true_annot_def apply blast
          using true_annot_def apply blast
        by (metis Decided_Propagated_in_iff_in_lits_of_l atms_of_clauses_conflicting_clss atms_of_ms_union
          in_m_in_literals no_decide set_mset_union that true_annot_def true_cls_add_mset)
    qed
    then have \<open>trail S \<Turnstile>asm clauses S + conflicting_clss S\<close>
      by (auto simp: true_annots_def  dest!: multi_member_split )
    then show ?thesis
      using can_always_improve[of S] \<open>\<not>?A\<close> tot invs ns by (auto simp: dpll\<^sub>W_bnb.simps)
  qed
  then show \<open>count_decided (trail S) = 0\<close>
    using dec0 by blast
  moreover have ?A
    using A by blast
  ultimately show \<open>unsatisfiable (set_mset (clauses S + conflicting_clss S))\<close>
    using only_propagated_vars_unsat[of \<open>trail S\<close> _  \<open>set_mset (clauses S + conflicting_clss S)\<close>] invs
    unfolding dpll\<^sub>W_all_inv_def count_decided_0_iff
   by auto
qed

end

end


locale dpll\<^sub>W_state_optimal_weight =
  dpll\<^sub>W_state trail clauses
    tl_trail cons_trail state_eq state +
  ocdcl_weight \<rho>
  for
    trail :: \<open>'st \<Rightarrow> 'v  dpll\<^sub>W_ann_lits\<close> and
    clauses :: \<open>'st \<Rightarrow> 'v clauses\<close> and
    tl_trail :: \<open>'st \<Rightarrow> 'st\<close> and
    cons_trail :: \<open>'v  dpll\<^sub>W_ann_lit \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    state_eq  :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> (infix "\<sim>" 50) and
    state :: \<open>'st \<Rightarrow> 'v  dpll\<^sub>W_ann_lits \<times> 'v clauses \<times> 'v clause option \<times> 'b\<close> and
    \<rho> :: \<open>'v clause \<Rightarrow> 'a :: {linorder}\<close> +
  fixes
    update_additional_info :: \<open>'v clause option \<times> 'b \<Rightarrow> 'st \<Rightarrow> 'st\<close>
  assumes
    update_additional_info:
      \<open>state S = (M, N, K) \<Longrightarrow> state (update_additional_info K' S) = (M, N, K')\<close>
begin

definition update_weight_information :: \<open>('v literal, 'v literal, unit) annotated_lits \<Rightarrow> 'st \<Rightarrow> 'st\<close> where
  \<open>update_weight_information M S =
    update_additional_info (Some (lit_of `# mset M), snd (additional_info S)) S\<close>

lemma [simp]:
  \<open>trail (update_weight_information M' S) = trail S\<close>
  \<open>clauses (update_weight_information M' S) = clauses S\<close>
  \<open>clauses (update_additional_info c S) = clauses S\<close>
  \<open>additional_info (update_additional_info (w, oth) S) = (w, oth)\<close>
  using update_additional_info[of S] unfolding update_weight_information_def
  by (auto simp: state)

lemma state_update_weight_information: \<open>state S = (M, N, w, oth) \<Longrightarrow>
       \<exists>w'. state (update_weight_information M' S) = (M, N, w', oth)\<close>
  apply (auto simp: state)
  apply (auto simp: update_weight_information_def)
  done

definition weight where
  \<open>weight S = fst (additional_info S)\<close>

lemma [simp]: \<open>(weight (update_weight_information M' S)) = Some (lit_of `# mset M')\<close>
  unfolding weight_def by (auto simp: update_weight_information_def)

text \<open>

  We test here a slightly different decision. In the CDCL version, we renamed \<^term>\<open>additional_info\<close>
  from the BNB version to avoid collisions. Here instead of renaming, we add the prefix
  \<^text>\<open>bnb.\<close> to every name.

\<close>
sublocale bnb: bnb_ops where
  trail = trail and
  clauses = clauses and
  tl_trail = tl_trail and
  cons_trail = cons_trail and
  state_eq = state_eq and
  state = state and
  weight = weight and
  conflicting_clauses = conflicting_clauses and
  is_improving_int = is_improving_int and
  update_weight_information = update_weight_information
  by unfold_locales


lemma atms_of_mm_conflicting_clss_incl_init_clauses:
  \<open>atms_of_mm (bnb.conflicting_clss S) \<subseteq> atms_of_mm (clauses S)\<close>
  using conflicting_clss_incl_init_clauses[of \<open>clauses S\<close> \<open>weight S\<close>]
  unfolding bnb.conflicting_clss_def
  by auto

lemma is_improving_conflicting_clss_update_weight_information: \<open>bnb.is_improving M M' S \<Longrightarrow>
       bnb.conflicting_clss S \<subseteq># bnb.conflicting_clss (update_weight_information M' S)\<close>
  using is_improving_conflicting_clss_update_weight_information[of M M' \<open>clauses S\<close> \<open>weight S\<close>]
  unfolding bnb.conflicting_clss_def
  by (auto simp: update_weight_information_def weight_def)

lemma conflicting_clss_update_weight_information_in2:
  assumes \<open>bnb.is_improving M M' S\<close>
  shows \<open>negate_ann_lits M' \<in># bnb.conflicting_clss (update_weight_information M' S)\<close>
  using conflicting_clss_update_weight_information_in2[of M M' \<open>clauses S\<close> \<open>weight S\<close>] assms
  unfolding bnb.conflicting_clss_def
  unfolding bnb.conflicting_clss_def
  by (auto simp: update_weight_information_def weight_def)


lemma state_additional_info':
  \<open>state S = (trail S, clauses S, weight S, bnb.additional_info S)\<close>
  unfolding additional_info_def by (cases \<open>state S\<close>; auto simp: state weight_def bnb.additional_info_def)

sublocale bnb: bnb where
  trail = trail and
  clauses = clauses and
  tl_trail = tl_trail and
  cons_trail = cons_trail and
  state_eq = state_eq and
  state = state and
  weight = weight and
  conflicting_clauses = conflicting_clauses and
  is_improving_int = is_improving_int and
  update_weight_information = update_weight_information
  apply unfold_locales
  subgoal by auto
  subgoal by (rule state_eq_sym)
  subgoal by (rule state_eq_trans)
  subgoal by (auto dest!: state_eq_state)
  subgoal by (rule cons_trail)
  subgoal by (rule tl_trail)
  subgoal by (rule state_update_weight_information)
  subgoal by (rule is_improving_conflicting_clss_update_weight_information)
  subgoal by (rule conflicting_clss_update_weight_information_in2; assumption)
  subgoal by (rule atms_of_mm_conflicting_clss_incl_init_clauses)
  subgoal by (rule state_additional_info')
  done

lemma improve_model_still_model:
  assumes
    \<open>bnb.dpll\<^sub>W_branch S T\<close> and
    all_struct: \<open>dpll\<^sub>W_all_inv (bnb.abs_state S)\<close> and
    ent: \<open>set_mset I \<Turnstile>sm clauses S\<close>  \<open>set_mset I \<Turnstile>sm bnb.conflicting_clss S\<close> and
    dist: \<open>distinct_mset I\<close> and
    cons: \<open>consistent_interp (set_mset I)\<close> and
    tot: \<open>atms_of I = atms_of_mm (clauses S)\<close> and
    le: \<open>Found (\<rho> I) < \<rho>' (weight T)\<close>
  shows
    \<open>set_mset I \<Turnstile>sm clauses T \<and> set_mset I \<Turnstile>sm bnb.conflicting_clss T\<close>
  using assms(1)
proof (cases rule: bnb.dpll\<^sub>W_branch.cases)
  case (update_info M M') note imp = this(1) and T = this(2)
  have atm_trail: \<open>atms_of (lit_of `# mset (trail S)) \<subseteq> atms_of_mm (clauses S)\<close> and
       dist2: \<open>distinct_mset (lit_of `# mset (trail S))\<close> and
      taut2: \<open>\<not> tautology (lit_of `# mset (trail S))\<close>
    using all_struct unfolding dpll\<^sub>W_all_inv_def by (auto simp: lits_of_def atms_of_def
      dest: no_dup_distinct no_dup_not_tautology)

  have tot2: \<open>total_over_m (set_mset I) (set_mset (clauses S))\<close>
    using tot[symmetric]
    by (auto simp: total_over_m_def total_over_set_def atm_iff_pos_or_neg_lit)
  have atm_trail: \<open>atms_of (lit_of `# mset M') \<subseteq> atms_of_mm (clauses S)\<close> and
    dist2: \<open>distinct_mset (lit_of `# mset M')\<close> and
    taut2: \<open>\<not> tautology (lit_of `# mset M')\<close>
    using imp by (auto simp: lits_of_def atms_of_def is_improving_int_def
      simple_clss_def)

  have tot2: \<open>total_over_m (set_mset I) (set_mset (clauses S))\<close>
    using tot[symmetric]
    by (auto simp: total_over_m_def total_over_set_def atm_iff_pos_or_neg_lit)
  have
    \<open>set_mset I \<Turnstile>m conflicting_clauses (clauses S) (weight (update_weight_information M' S))\<close>
    using entails_conflicting_clauses_if_le[of I \<open>clauses S\<close> M' M \<open>weight S\<close>]
    using T dist cons tot le imp by auto
  then have \<open>set_mset I \<Turnstile>m bnb.conflicting_clss (update_weight_information M' S)\<close>
    by (auto simp: update_weight_information_def bnb.conflicting_clss_def)
  then show ?thesis
    using ent T by (auto simp: bnb.conflicting_clss_def state)
qed

lemma cdcl_bnb_still_model:
  assumes
    \<open>bnb.dpll\<^sub>W_bnb S T\<close> and
    all_struct: \<open>dpll\<^sub>W_all_inv (bnb.abs_state S)\<close> and
    ent: \<open>set_mset I \<Turnstile>sm clauses S\<close> \<open>set_mset I \<Turnstile>sm bnb.conflicting_clss S\<close> and
    dist: \<open>distinct_mset I\<close> and
    cons: \<open>consistent_interp (set_mset I)\<close> and
    tot: \<open>atms_of I = atms_of_mm (clauses S)\<close> 
  shows
    \<open>(set_mset I \<Turnstile>sm clauses T \<and> set_mset I \<Turnstile>sm bnb.conflicting_clss T) \<or> Found (\<rho> I) \<ge> \<rho>' (weight T)\<close>
  using assms
proof (induction rule: bnb.dpll\<^sub>W_bnb.induct)
  case (dpll S T)
  then show ?case using ent by (auto elim!: bnb.dpll\<^sub>W_coreE simp: bnb.state'_def)
next
  case (bnb S T)
  then show ?case
    using improve_model_still_model[of S T I] using assms(2-) by auto
qed

lemma cdcl_bnb_larger_still_larger:
  assumes
    \<open>bnb.dpll\<^sub>W_bnb S T\<close>
  shows \<open>\<rho>' (weight S) \<ge> \<rho>' (weight T)\<close>
  using assms apply (cases rule: bnb.dpll\<^sub>W_bnb.cases)
  by (auto simp: bnb.dpll\<^sub>W_branch.simps is_improving_int_def bnb.dpll\<^sub>W_core_same_weight)

lemma rtranclp_cdcl_bnb_still_model:
  assumes
    st: \<open>bnb.dpll\<^sub>W_bnb\<^sup>*\<^sup>* S T\<close> and
    all_struct: \<open>dpll\<^sub>W_all_inv (bnb.abs_state S)\<close> and
    ent: \<open>(set_mset I \<Turnstile>sm clauses S \<and> set_mset I \<Turnstile>sm bnb.conflicting_clss S) \<or> Found (\<rho> I) \<ge> \<rho>' (weight S)\<close> and
    dist: \<open>distinct_mset I\<close> and
    cons: \<open>consistent_interp (set_mset I)\<close> and
    tot: \<open>atms_of I = atms_of_mm (clauses S)\<close>
  shows
    \<open>(set_mset I \<Turnstile>sm clauses T \<and> set_mset I \<Turnstile>sm bnb.conflicting_clss T) \<or> Found (\<rho> I) \<ge> \<rho>' (weight T)\<close>
  using st
proof (induction rule: rtranclp_induct)
  case base
  then show ?case
    using ent by auto
next
  case (step T U) note star = this(1) and st = this(2) and IH = this(3)
  have 1: \<open>dpll\<^sub>W_all_inv (bnb.abs_state T)\<close>
    using bnb.rtranclp_dpll\<^sub>W_bnb_abs_state_all_inv[OF star all_struct] .
  have 3: \<open>atms_of I = atms_of_mm (clauses T)\<close>
    using bnb.rtranclp_dpll\<^sub>W_bnb_clauses[OF star] tot by auto
  show ?case
    using cdcl_bnb_still_model[OF st 1 _ _ dist cons 3] IH
      cdcl_bnb_larger_still_larger[OF st]
    by auto
qed

lemma simple_clss_entailed_by_too_heavy_in_conflicting:
   \<open>C \<in># mset_set (simple_clss (atms_of_mm (clauses S))) \<Longrightarrow>
    too_heavy_clauses (clauses S) (weight S) \<Turnstile>pm
     (C) \<Longrightarrow> C \<in># bnb.conflicting_clss S\<close>
  by (auto simp: conflicting_clauses_def bnb.conflicting_clss_def)

lemma can_always_improve:
  assumes
    ent: \<open>trail S \<Turnstile>asm clauses S\<close> and
    total: \<open>total_over_m (lits_of_l (trail S)) (set_mset (clauses S))\<close> and
    n_s: \<open>(\<forall>C \<in># bnb.conflicting_clss S. \<not> trail S \<Turnstile>as CNot C)\<close> and
    all_struct: \<open>dpll\<^sub>W_all_inv (bnb.abs_state S)\<close>
   shows \<open>Ex (bnb.dpll\<^sub>W_branch S)\<close>
proof -
  have H: \<open>(lit_of `# mset (trail S)) \<in># mset_set (simple_clss (atms_of_mm (clauses S)))\<close>
    \<open>(lit_of `# mset (trail S)) \<in> simple_clss (atms_of_mm (clauses S))\<close>
    \<open>no_dup (trail S)\<close>
    apply (subst finite_set_mset_mset_set[OF simple_clss_finite])
    using all_struct by (auto simp: simple_clss_def
        dpll\<^sub>W_all_inv_def atms_of_def lits_of_def image_image clauses_def
      dest: no_dup_not_tautology no_dup_distinct)
  moreover have \<open>trail S \<Turnstile>as CNot (pNeg (lit_of `# mset (trail S)))\<close>
    by (auto simp: pNeg_def true_annots_true_cls_def_iff_negation_in_model lits_of_def)

  ultimately have le: \<open>Found (\<rho> (lit_of `# mset (trail S))) < \<rho>' (weight S)\<close>
    using n_s total not_entailed_too_heavy_clauses_ge[of \<open>lit_of `# mset (trail S)\<close> \<open>clauses S\<close> \<open>weight S\<close>]
     simple_clss_entailed_by_too_heavy_in_conflicting[of \<open>pNeg (lit_of `# mset (trail S))\<close> S]
    by (cases \<open>\<not> too_heavy_clauses (clauses S) (weight S) \<Turnstile>pm
       pNeg (lit_of `# mset (trail S))\<close>)
     (auto simp:  lits_of_def
         conflicting_clauses_def clauses_def negate_ann_lits_pNeg_lit_of image_iff
         simple_clss_finite subset_iff
       dest: bspec[of _ _ \<open>(lit_of `# mset (trail S))\<close>] dest: total_over_m_atms_incl
          true_clss_cls_in too_heavy_clauses_contains_itself
          dest!: multi_member_split)
  have tr: \<open>trail S \<Turnstile>asm clauses S\<close>
    using ent by (auto simp: clauses_def)
  have tot': \<open>total_over_m (lits_of_l (trail S)) (set_mset (clauses S))\<close>
    using total all_struct by (auto simp: total_over_m_def total_over_set_def)
  have M': \<open>\<rho> (lit_of `# mset M') = \<rho> (lit_of `# mset (trail S))\<close>
    if \<open>total_over_m (lits_of_l M') (set_mset (clauses S))\<close> and
      incl: \<open>mset (trail S) \<subseteq># mset M'\<close> and
      \<open>lit_of `# mset M' \<in> simple_clss (atms_of_mm (clauses S))\<close>
      for M'
    proof -
      have [simp]: \<open>lits_of_l M' = set_mset (lit_of `# mset M')\<close>
        by (auto simp: lits_of_def)
      obtain A where A: \<open>mset M' = A + mset (trail S)\<close>
        using incl by (auto simp: mset_subset_eq_exists_conv)
      have M': \<open>lits_of_l M' = lit_of ` set_mset A \<union> lits_of_l (trail S)\<close>
        unfolding lits_of_def
        by (metis A image_Un set_mset_mset set_mset_union)
      have \<open>mset M' = mset (trail S)\<close>
        using that tot' total unfolding A total_over_m_alt_def
          apply (case_tac A)
        apply (auto simp: A simple_clss_def distinct_mset_add M' image_Un
            tautology_union mset_inter_empty_set_mset atms_of_def atms_of_s_def
            atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set image_image
            tautology_add_mset)
          by (metis (no_types, lifting) atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set
          lits_of_def subsetCE)
      then show ?thesis
        using total by auto
    qed
  have \<open>bnb.is_improving (trail S) (trail S) S\<close>
    if \<open>Found (\<rho> (lit_of `# mset (trail S))) < \<rho>' (weight S)\<close>
    using that total H tr tot' M' unfolding is_improving_int_def lits_of_def
    by fast
  then show ?thesis
    using bnb.dpll\<^sub>W_branch.intros[of \<open>trail S\<close> _ S \<open>update_weight_information (trail S) S\<close>] total H le
    by fast
qed


lemma no_step_dpll\<^sub>W_bnb_conflict:
  assumes
    ns: \<open>no_step bnb.dpll\<^sub>W_bnb S\<close> and
    invs: \<open>dpll\<^sub>W_all_inv (bnb.abs_state S)\<close>
  shows \<open>\<exists>C \<in># clauses S + bnb.conflicting_clss S. trail S \<Turnstile>as CNot C\<close> (is ?A) and
      \<open>count_decided (trail S) = 0\<close> and
     \<open>unsatisfiable (set_mset (clauses S + bnb.conflicting_clss S))\<close>
  apply (rule bnb.no_step_dpll\<^sub>W_bnb_conflict[OF _ assms])
  subgoal using can_always_improve by blast
  apply (rule bnb.no_step_dpll\<^sub>W_bnb_conflict[OF _ assms])
  subgoal using can_always_improve by blast
  apply (rule bnb.no_step_dpll\<^sub>W_bnb_conflict[OF _ assms])
  subgoal using can_always_improve by blast
  done

lemma full_cdcl_bnb_stgy_larger_or_equal_weight:
  assumes
    st: \<open>full bnb.dpll\<^sub>W_bnb S T\<close> and
    all_struct: \<open>dpll\<^sub>W_all_inv (bnb.abs_state S)\<close> and
    ent: \<open>(set_mset I \<Turnstile>sm clauses S \<and> set_mset I \<Turnstile>sm bnb.conflicting_clss S) \<or> Found (\<rho> I) \<ge> \<rho>' (weight S)\<close> and
    dist: \<open>distinct_mset I\<close> and
    cons: \<open>consistent_interp (set_mset I)\<close> and
    tot: \<open>atms_of I = atms_of_mm (clauses S)\<close>
  shows
    \<open>Found (\<rho> I) \<ge> \<rho>' (weight T)\<close> and
    \<open>unsatisfiable (set_mset (clauses T + bnb.conflicting_clss T))\<close>
proof -
  have ns: \<open>no_step bnb.dpll\<^sub>W_bnb T\<close> and
    st: \<open>bnb.dpll\<^sub>W_bnb\<^sup>*\<^sup>* S T\<close>
    using st unfolding full_def by (auto intro: )
  have struct_T: \<open>dpll\<^sub>W_all_inv (bnb.abs_state T)\<close>
    using bnb.rtranclp_dpll\<^sub>W_bnb_abs_state_all_inv[OF st all_struct]  .

  have atms_eq: \<open>atms_of I \<union> atms_of_mm (bnb.conflicting_clss T) = atms_of_mm (clauses T)\<close>
    using atms_of_mm_conflicting_clss_incl_init_clauses[of T]
      bnb.rtranclp_dpll\<^sub>W_bnb_clauses[OF st] tot
    by auto

  show \<open>unsatisfiable (set_mset (clauses T + bnb.conflicting_clss T))\<close>
    using no_step_dpll\<^sub>W_bnb_conflict[of T] ns struct_T
    by fast
  then have \<open>\<not>set_mset I \<Turnstile>sm clauses T + bnb.conflicting_clss T\<close>
    using dist cons by auto
  then have \<open>False\<close> if \<open>Found (\<rho> I) < \<rho>' (weight T)\<close>
    using ent that rtranclp_cdcl_bnb_still_model[OF st assms(2-)]
      bnb.rtranclp_dpll\<^sub>W_bnb_clauses[OF st] by auto
  then show \<open>Found (\<rho> I) \<ge> \<rho>' (weight T)\<close>
    by force
qed


(*TODO:
full_cdcl_bnb_stgy_larger_or_equal_weight
full_cdcl_bnb_stgy_no_conflicting_clause_from_init_state
*)

end

end
