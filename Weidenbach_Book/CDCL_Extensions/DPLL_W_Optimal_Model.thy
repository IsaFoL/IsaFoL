theory DPLL_W_Optimal_Model
imports
  CDCL_W_Optimal_Model
  CDCL.DPLL_W
begin

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

sublocale dpll: dpll_ops where
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


sublocale dpll: dpll\<^sub>W_state trail clauses tl_trail cons_trail state_eq state
  apply standard
  apply (auto dest: state_eq_sym[THEN iffD1] intro: state_eq_trans dest: state_eq_state)
  apply (auto simp: state dpll.additional_info_def)
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
inductive dpll\<^sub>W_core :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
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


inductive dpll\<^sub>W_branch :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
update_info:
  \<open>is_improving M M' S \<Longrightarrow> state T = state (update_weight_information M' S)
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

lemma (in -)funpow_tl_append_skip_last:
  \<open>((tl ^^ length M') (M' @ M)) = M\<close>
  by (induction M')
    (auto simp del: funpow.simps(2) simp: funpow_Suc_right)


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

(*TODO MOVE*)
lemma (in -) backtrack_split_some_is_decided_then_snd_has_hd':
  \<open>l\<in>set M \<Longrightarrow> is_decided l \<Longrightarrow> \<exists>M' L' M''. backtrack_split M = (M'', L' # M')\<close>
  by (metis backtrack_snd_empty_not_decided list.exhaust prod.collapse)

lemma (in -) total_over_m_entailed_or_conflict:
  shows \<open>total_over_m M N \<Longrightarrow> M \<Turnstile>s N \<or> (\<exists>C \<in> N. M \<Turnstile>s CNot C)\<close>
  by (metis Set.set_insert total_not_true_cls_true_clss_CNot total_over_m_empty total_over_m_insert true_clss_def)


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
      \<open>count_decided (trail S) = 0\<close>
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

  show False if \<open>\<not>?A\<close>
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
qed

end

end
