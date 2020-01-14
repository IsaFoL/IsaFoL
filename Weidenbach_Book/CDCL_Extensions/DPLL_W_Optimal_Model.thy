theory DPLL_W_Optimal_Model
imports
  CDCL_W_Optimal_Model
  CDCL.DPLL_W
begin


lemma dpll\<^sub>W_trail_after_step1:
  assumes \<open>dpll\<^sub>W S T\<close>
  shows
    \<open>\<exists>K' M1 M2' M2''.
      (rev (trail T) = rev (trail S) @ M2' \<and> M2' \<noteq> []) \<or>
      (rev (trail S) = M1 @ Decided (-K') # M2' \<and>
        rev (trail T) = M1 @ Propagated K' () # M2'' \<and>
       Suc (length M1) \<le> length (trail S))\<close>
  using assms
  apply (induction S T rule: dpll\<^sub>W.induct)
  subgoal for L C T
    by auto
  subgoal
    by auto
  subgoal for S M' L M D
    using backtrack_split_snd_hd_decided[of \<open>trail S\<close>]
      backtrack_split_list_eq[of \<open>trail S\<close>, symmetric]
    apply - apply (rule exI[of _ \<open>-lit_of L\<close>], rule exI[of _ \<open>rev M\<close>], rule exI[of _ \<open>rev M'\<close>], rule exI[of _ \<open>[]\<close>])
    by (cases L)
      auto
  done

lemma tranclp_dpll\<^sub>W_trail_after_step:
  assumes \<open>dpll\<^sub>W\<^sup>+\<^sup>+ S T\<close>
  shows
    \<open>\<exists>K' M1 M2' M2''.
      (rev (trail T) = rev (trail S) @ M2' \<and> M2' \<noteq> []) \<or>
      (rev (trail S) = M1 @ Decided (-K') # M2' \<and>
        rev (trail T) = M1 @ Propagated K' () # M2'' \<and> Suc (length M1) \<le> length (trail S))\<close>
  using assms(1)
proof (induction rule: tranclp_induct)
  case (base y)
  then show ?case by (auto dest!: dpll\<^sub>W_trail_after_step1)
next
  case (step y z)
  then consider
    (1) M2' where
      \<open>rev (DPLL_W.trail y) = rev (DPLL_W.trail S) @ M2'\<close> \<open>M2' \<noteq> []\<close> |
    (2) K' M1 M2' M2'' where \<open>rev (DPLL_W.trail S) = M1 @ Decided (- K') # M2'\<close>
       \<open>rev (DPLL_W.trail y) = M1 @ Propagated K' () # M2''\<close> and \<open>Suc (length M1) \<le> length (trail S)\<close>
    by blast
  then show ?case
  proof cases
    case (1 M2')
    consider
      (a) M2' where
        \<open>rev (DPLL_W.trail z) = rev (DPLL_W.trail y) @ M2'\<close> \<open>M2' \<noteq> []\<close> |
      (b) K'' M1' M2'' M2''' where \<open>rev (DPLL_W.trail y) = M1' @ Decided (- K'') # M2''\<close>
         \<open>rev (DPLL_W.trail z) = M1' @ Propagated K'' () # M2'''\<close> and
        \<open>Suc (length M1') \<le> length (trail y)\<close>
      using dpll\<^sub>W_trail_after_step1[OF step(2)]
      by blast
    then show ?thesis
    proof cases
      case a
      then show ?thesis using 1 by auto
    next
      case b
      have H: \<open>rev (DPLL_W.trail S) @ M2' = M1' @ Decided (- K'') # M2'' \<Longrightarrow>
           length M1' \<noteq> length (DPLL_W.trail S) \<Longrightarrow>
           length M1' < Suc (length (DPLL_W.trail S)) \<Longrightarrow> rev (DPLL_W.trail S) =
           M1' @ Decided (- K'') # drop (Suc (length M1')) (rev (DPLL_W.trail S))\<close>
        apply (drule arg_cong[of _ _ \<open>take (length (trail S))\<close>])
        by (auto simp: take_Cons')
      show ?thesis using b 1 apply -
        apply (rule exI[of _ \<open>K''\<close>])
        apply (rule exI[of _ \<open>M1'\<close>])
        apply (rule exI[of _ \<open>if length (trail S) \<le> length M1' then drop (length (DPLL_W.trail S)) (rev (DPLL_W.trail z)) else
              drop (Suc (length M1')) (rev (DPLL_W.trail S))\<close>])
        apply (cases \<open>length (trail S) < length M1'\<close>)
        subgoal
          apply auto
          by (simp add: append_eq_append_conv_if)
        apply (cases \<open>length M1' = length (trail S)\<close>)
        subgoal by auto
        subgoal
          using H
          apply (clarsimp simp: )
          done
        done
      qed
    next
      case (2 K'' M1' M2'' M2''')
      consider
        (a) M2' where
          \<open>rev (DPLL_W.trail z) = rev (DPLL_W.trail y) @ M2'\<close> \<open>M2' \<noteq> []\<close> |
        (b) K'' M1' M2'' M2''' where \<open>rev (DPLL_W.trail y) = M1' @ Decided (- K'') # M2''\<close>
           \<open>rev (DPLL_W.trail z) = M1' @ Propagated K'' () # M2'''\<close> and
          \<open>Suc (length M1') \<le> length (trail y)\<close>
        using dpll\<^sub>W_trail_after_step1[OF step(2)]
        by blast
      then show ?thesis
      proof cases
        case a
        then show ?thesis using 2 by auto
      next
        case (b K''' M1'' M2'''' M2''''')
        have [iff]: \<open>M1' @ Propagated K'' () # M2''' = M1'' @ Decided (- K''') # M2'''' \<longleftrightarrow>
          (\<exists>N1''. M1'' = M1' @ Propagated K'' () # N1'' \<and> M2''' = N1'' @ Decided (- K''') # M2'''')\<close> if \<open>length M1' < length M1''\<close>
          using that apply (auto simp: append_eq_append_conv_if)
          by (metis (no_types, lifting) Cons_eq_append_conv append_take_drop_id drop_eq_Nil leD)
        have [iff]: \<open>M1' @ Propagated K'' () # M2''' = M1'' @ Decided (- K''') # M2'''' \<longleftrightarrow>
          (\<exists>N1''. M1' = M1'' @ Decided (- K''') # N1'' \<and> M2'''' = N1'' @ Propagated K'' () # M2''')\<close> if \<open>\<not>length M1' < length M1''\<close>
          using that apply (auto simp: append_eq_append_conv_if)
          by (metis (no_types, lifting) Cons_eq_append_conv append_take_drop_id drop_eq_Nil le_eq_less_or_eq)

        show ?thesis using b 2 apply -
          apply (rule exI[of _ \<open>if length M1' < length M1'' then K'' else K'''\<close>])
          apply (rule exI[of _ \<open>if length M1' < length M1'' then M1' else M1''\<close>])
          apply (cases \<open>length (trail S) < min (length M1') (length M1'')\<close>)
          subgoal
            by auto
          apply (cases \<open>min (length M1') (length M1'') = length (trail S)\<close>)
          subgoal by auto
          subgoal
            by (auto simp: )
          done
       qed
   qed
qed

text \<open>
  This theorem is an important (although rather obvious) property: the model
  induced by trails are not repeated.
\<close>
lemma tranclp_dpll\<^sub>W_no_dup_trail:
  assumes \<open>dpll\<^sub>W\<^sup>+\<^sup>+ S T\<close> and \<open>dpll\<^sub>W_all_inv S\<close>
  shows \<open>set (trail S) \<noteq> set (trail T)\<close>
proof -
  have [simp]: \<open>A = B \<union> A \<longleftrightarrow> B \<subseteq> A\<close> for A B
    by auto
  have [simp]: \<open>rev (trail U) = xs \<longleftrightarrow>trail U = rev xs\<close> for xs U
    by auto
  have \<open>dpll\<^sub>W_all_inv T\<close>
    by (metis assms(1) assms(2) reflclp_tranclp rtranclp_dpll\<^sub>W_all_inv sup2CI)
  then have n_d: \<open>no_dup (trail S)\<close> \<open>no_dup (trail T)\<close>
    using assms unfolding dpll\<^sub>W_all_inv_def by (auto dest: no_dup_imp_distinct)
  have [simp]: \<open>no_dup (rev M2' @ DPLL_W.trail S) \<Longrightarrow>
          dpll\<^sub>W_all_inv S \<Longrightarrow>
          set M2' \<subseteq> set (DPLL_W.trail S) \<longleftrightarrow> M2' = []\<close> for M2'
    by (cases M2' rule: rev_cases)
      (auto simp: undefined_notin)
  show ?thesis
    using n_d tranclp_dpll\<^sub>W_trail_after_step[OF assms(1)] assms(2) apply auto
    by (metis (no_types, lifting) Un_insert_right insertI1 list.simps(15) lit_of.simps(1,2)
      n_d(1) no_dup_cannot_not_lit_and_uminus set_append set_rev)
qed


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
      \<open>is_improving M M' S \<Longrightarrow> negate_ann_lits M' \<in># conflicting_clss (update_weight_information M' S)\<close> and
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

inductive odpll\<^sub>W :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> where
dpll:
  \<open>odpll\<^sub>W S T\<close>
  if \<open>dpll\<^sub>W_core S T\<close> |
bnb:
  \<open>odpll\<^sub>W S T\<close>
  if \<open>dpll\<^sub>W_branch S T\<close>

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
