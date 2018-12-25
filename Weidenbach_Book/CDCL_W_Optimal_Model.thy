theory CDCL_W_Optimal_Model
imports CDCL_W_Abstract_State "HOL-Library.Extended_Nat" "../lib/Explorer"
begin

section \<open>CDCL Extensions\<close>

subsection \<open>Optimisations\<close>

text \<open>
  A counter-example for the original version from the book has been found (see below). There is no
  simple fix, except taking complete models.
\<close>

notation image_mset (infixr "`#" 90)

text \<open> The initial version was supposed to work on partial models directly. I found a counter
example while writing the proof:

\nitpicking{

\shortrules{Propagate}{$(M;N;U;k;\top;O)$}{$(ML^{C\lor L};N;U;k;\top;O)$}

provided $C\lor L\in (N\cup U)$, $M\models \neg C$, $L$ is undefined in $M$.

\bigskip
\shortrules{Decide}{$(M;N;U;k;\top;O)$}{$(ML^{k+1};N;U;k+1;\top;O)$}

provided $L$ is undefined in $M$, contained in $N$.

\bigskip
\shortrules{ConflSat}{$(M;N;U;k;\top;O)$}{$(M;N;U;k;D;O)$}

provided $D\in (N\cup U)$ and $M\models \neg D$.

\bigskip
\shortrules{ConflOpt}{$(M;N;U;k;\top;O)$}{$(M;N;U;k;\neg M;O)$}

provided $O\neq\epsilon$ and $\operatorname{cost}(M) \geq \operatorname{cost}(O)$.

\bigskip
\shortrules{Skip}{$(ML^{C\lor L};N;U;k;D;O)$}{$(M;N;U;k;D;O)$}

provided $D\not\in\{\top,\bot\}$ and $\neg L$ does not occur in $D$.


\bigskip
\shortrules{Resolve}{$(ML^{C\lor L};N;U;k;D\lor-(L);O)$}{$(M;N;U;k;D\lor C;O)$}

provided $D$ is of level $k$.

\bigskip
\shortrules{Backtrack}{$(M_1K^{i+1}M_2;N;U;k;D\lor L;O)$}{$(M_1L^{D\vee L};N;U\cup\{D\lor L\};i;\top;O)$}

provided $L$ is of level $k$ and $D$ is of level $i$.

\bigskip
\shortrules{Improve}{$(M;N;U;k;\top;O)$}{$(M;N;U;k;\top;M)$}

provided $M\models N$ and $O=\epsilon$ or $\operatorname{cost}(M)<\operatorname{cost}(O)$.
}
{This calculus does not always find the model with minimum cost. Take for example the following cost function:
\[\operatorname{cost}: \left\{
\begin{array}{c@ {\rightarrow}c}
P & 3\\
\neg P & 1\\
Q & 1\\
\neg Q & 1\\
\end{array}
 \right.\]
and the clauses $N = \{P\lor Q\}$. We can then do the following transitions:


$(\epsilon, N, \varnothing, \top, \infty)$

\shortrules{Decide}{}{$(P^1, N, \varnothing, \top, \infty)$}

\shortrules{Improve}{}{$(P^1, N, \varnothing, \top, (P, 3))$}

\shortrules{conflictOpt}{}{$(P^1, N, \varnothing, \neg P, (P, 3))$}

\shortrules{backtrack}{}{$({\neg P}^{\neg P}, N, \{\neg P\}, \top, (P, 3))$}

\shortrules{propagate}{}{$({\neg P}^{\neg P}Q^{P\lor Q}, N, \{\neg P\}, \top, (P, 3))$}

\shortrules{improve}{}{$({\neg P}^{\neg P}Q^{P\lor Q}, N, \{\neg P\}, \top, (\neg P\, Q, 2))$}

\shortrules{conflictOpt}{}{$({\neg P}^{\neg P}Q^{P\lor Q}, N, \{\neg P\}, P \lor \neg Q, (\neg P\, Q, 2))$}

\shortrules{resolve}{}{$({\neg P}^{\neg P}, N, \{\neg P\}, P, (\neg P\, Q, 2))$}

\shortrules{resolve}{}{$(\epsilon, N, \{\neg P\}, \bot, (\neg P\, Q, 3))$}


However, the optimal model (obviously) is $Q$.
}
\<close>

text \<open>The idea of the proof is the following:
  \<^enum> We start with a calculus CDCLopt on \<^term>\<open>(M, N, U, D, Op)\<close>.
  \<^enum> This extended to a state  \<^term>\<open>(M, N +  all_models_of_higher_cost, U, D, Op)\<close>.
  \<^enum> Each transition step of CDCLopt is mapped to a step in CDCL over the abstract state. The
    abstract set of clauses is likely unsatisfiable, but we only use it to prove the invariants on
    the state.
  \<^enum> The last proofs are done over CDCLopt.

We abstract about how the optimisation is done in the locale below. It is parametrised by what is
the optimisation criterion and which clauses are generated.

We later instantiate it with the optimisation calculus from Weidenbach's book.
\<close>
locale conflict_driven_clause_learning_with_adding_init_clause_cost\<^sub>W_no_state =
  state\<^sub>W_no_state
    state_eq state
    \<comment> \<open>functions for the state:\<close>
      \<comment> \<open>access functions:\<close>
    trail init_clss learned_clss conflicting
      \<comment> \<open>changing state:\<close>
    cons_trail tl_trail add_learned_cls remove_cls
    update_conflicting

      \<comment> \<open>get state:\<close>
    init_state
  for
    state_eq :: "'st \<Rightarrow> 'st \<Rightarrow> bool" (infix "\<sim>" 50) and
    state :: "'st \<Rightarrow> ('v, 'v clause) ann_lits \<times> 'v clauses \<times> 'v clauses \<times> 'v clause option \<times>
      'a \<times> 'b" and
    trail :: "'st \<Rightarrow> ('v, 'v clause) ann_lits" and
    init_clss :: "'st \<Rightarrow> 'v clauses" and
    learned_clss :: "'st \<Rightarrow> 'v clauses" and
    conflicting :: "'st \<Rightarrow> 'v clause option" and

    cons_trail :: "('v, 'v clause) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    tl_trail :: "'st \<Rightarrow> 'st" and
    add_learned_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    remove_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_conflicting :: "'v clause option \<Rightarrow> 'st \<Rightarrow> 'st" and

    init_state :: "'v clauses \<Rightarrow> 'st" +
  fixes
    update_weight_information :: "('v, 'v clause) ann_lits \<Rightarrow> 'st \<Rightarrow> 'st" and
    is_improving_int :: "('v, 'v clause) ann_lits \<Rightarrow> 'v clauses \<Rightarrow> 'a \<Rightarrow> bool" and
    conflicting_clauses :: "'v clauses \<Rightarrow> 'a \<Rightarrow> 'v clauses" and
    weight :: \<open>'st \<Rightarrow> 'a\<close>
begin

abbreviation is_improving where
  \<open>is_improving M S \<equiv> is_improving_int M (init_clss S) (weight S)\<close>

definition additional_info' :: "'st \<Rightarrow> 'b" where
"additional_info' S = (\<lambda>(_, _, _, _, _, D). D) (state S)"

definition conflicting_clss :: \<open>'st \<Rightarrow> 'v literal multiset multiset\<close> where
\<open>conflicting_clss S = conflicting_clauses (init_clss S) (weight S)\<close>

definition negate_ann_lits :: "('v, 'v clause) ann_lits \<Rightarrow> 'v literal multiset" where
  \<open>negate_ann_lits M = (\<lambda>L. - lit_of L) `# (mset M)\<close>

definition abs_state :: "'st \<Rightarrow> ('v, 'v clause) ann_lit list \<times> 'v clauses \<times> 'v clauses \<times> 'v clause option" where
  \<open>abs_state S = (trail S, init_clss S + {#C. C \<in># conflicting_clss S#}, learned_clss S,
  conflicting S)\<close>
end

locale conflict_driven_clause_learning_with_adding_init_clause_cost\<^sub>W_ops =
  conflict_driven_clause_learning_with_adding_init_clause_cost\<^sub>W_no_state
    state_eq state
    \<comment> \<open>functions for the state:\<close>
      \<comment> \<open>access functions:\<close>
    trail init_clss learned_clss conflicting
      \<comment> \<open>changing state:\<close>
    cons_trail tl_trail add_learned_cls remove_cls
    update_conflicting

      \<comment> \<open>get state:\<close>
    init_state
      \<comment> \<open>Adding a clause:\<close>
    update_weight_information is_improving_int conflicting_clauses weight
  for
    state_eq :: "'st \<Rightarrow> 'st \<Rightarrow> bool" (infix "\<sim>" 50) and
    state :: "'st \<Rightarrow> ('v, 'v clause) ann_lits \<times> 'v clauses \<times> 'v clauses \<times>  'v clause option \<times>
      'a \<times> 'b" and
    trail :: "'st \<Rightarrow> ('v, 'v clause) ann_lits" and
    init_clss :: "'st \<Rightarrow> 'v clauses" and
    learned_clss :: "'st \<Rightarrow> 'v clauses" and
    conflicting :: "'st \<Rightarrow> 'v clause option" and

    cons_trail :: "('v, 'v clause) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    tl_trail :: "'st \<Rightarrow> 'st" and
    add_learned_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    remove_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_conflicting :: "'v clause option \<Rightarrow> 'st \<Rightarrow> 'st" and

    init_state :: "'v clauses \<Rightarrow> 'st" and
    update_weight_information :: "('v, 'v clause) ann_lits \<Rightarrow> 'st \<Rightarrow> 'st" and
    is_improving_int :: "('v, 'v clause) ann_lits \<Rightarrow> 'v clauses \<Rightarrow> 'a \<Rightarrow> bool" and
    conflicting_clauses :: "'v clauses \<Rightarrow> 'a \<Rightarrow> 'v clauses" and
    weight :: \<open>'st \<Rightarrow> 'a\<close> +
  assumes
    state_prop':
      \<open>state S = (trail S, init_clss S, learned_clss S, conflicting S, weight S, additional_info' S)\<close>
    and
    update_weight_information:
       \<open>state S = (M, N, U, C, w, other) \<Longrightarrow>
          \<exists>w'. state (update_weight_information T S) = (M, N, U, C, w', other)\<close> and
    atms_of_conflicting_clss:
      \<open>atms_of_mm (conflicting_clss S) \<subseteq> atms_of_mm (init_clss S)\<close> and
    distinct_mset_mset_conflicting_clss:
      \<open>distinct_mset_mset (conflicting_clss S)\<close> and
    conflicting_clss_update_weight_information_mono:
      \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S) \<Longrightarrow> is_improving M S \<Longrightarrow>
        conflicting_clss S \<subseteq># conflicting_clss (update_weight_information M S)\<close>
    and
    conflicting_clss_update_weight_information_in:
      \<open>is_improving M S \<Longrightarrow>
        negate_ann_lits M \<in># conflicting_clss (update_weight_information M S)\<close> and
    is_improving_mono:
      \<open>\<not>is_improving M' S \<Longrightarrow> is_improving M S \<Longrightarrow>
         \<not>is_improving M' (update_weight_information M S)\<close>
begin

sublocale conflict_driven_clause_learning\<^sub>W
  apply unfold_locales
  unfolding additional_info'_def additional_info_def by (auto simp: state_prop')

declare reduce_trail_to_skip_beginning[simp]


lemma state_eq_weight[state_simp, simp]: \<open>S \<sim> T \<Longrightarrow> weight S = weight T\<close>
  apply (drule state_eq_state)
  apply (subst (asm) state_prop')
  apply (subst (asm) state_prop')
  by simp


lemma conflicting_clause_state_eq[state_simp, simp]: \<open>S \<sim> T \<Longrightarrow> conflicting_clss S = conflicting_clss T\<close>
  unfolding conflicting_clss_def by auto

lemma
  weight_cons_trail[simp]:
    \<open>weight (cons_trail L S) = weight S\<close> and
  weight_update_conflicting[simp]:
    \<open>weight (update_conflicting C S) = weight S\<close> and
  weight_tl_trail[simp]:
    \<open>weight (tl_trail S) = weight S\<close> and
  weight_add_learned_cls[simp]:
    \<open>weight (add_learned_cls D S) = weight S\<close>
  using cons_trail[of S _ _ L] update_conflicting[of S] tl_trail[of S] add_learned_cls[of S]
  by (auto simp: state_prop')

lemma update_weight_information_simp[simp]:
  \<open>trail (update_weight_information C S) = trail S\<close>
  \<open>init_clss (update_weight_information C S) = init_clss S\<close>
  \<open>learned_clss (update_weight_information C S) = learned_clss S\<close>
  \<open>clauses (update_weight_information C S) = clauses S\<close>
  \<open>backtrack_lvl (update_weight_information C S) = backtrack_lvl S\<close>
  \<open>conflicting (update_weight_information C S) = conflicting S\<close>
  using update_weight_information[of S] unfolding clauses_def
  by (subst (asm) state_prop', subst (asm) state_prop'; force)+

lemma
  conflicting_clss_cons_trail[simp]: \<open>conflicting_clss (cons_trail K S) = conflicting_clss S\<close> and
  conflicting_clss_tl_trail[simp]: \<open>conflicting_clss (tl_trail S) = conflicting_clss S\<close> and
  conflicting_clss_add_learned_cls[simp]: \<open>conflicting_clss (add_learned_cls D S) = conflicting_clss S\<close> and
  conflicting_clss_update_conflicting[simp]: \<open>conflicting_clss (update_conflicting E S) = conflicting_clss S\<close>
  unfolding conflicting_clss_def by auto


lemma atms_of_negate_ann_lits[simp]: \<open>atms_of (negate_ann_lits M) = atm_of ` (lits_of_l M)\<close>
  unfolding negate_ann_lits_def lits_of_def atms_of_def by (auto simp: image_image)

lemma distinct_image_mset_not_equal:
  assumes
    LL': \<open>L \<noteq> L'\<close> and
    dist: \<open>distinct_mset (f `# M)\<close> and
    L: \<open>L \<in># M\<close> and
    L': \<open>L' \<in># M\<close> and
    fLL'[simp]: \<open>f L = f L'\<close>
  shows \<open>False\<close>
proof -
  obtain M1 where M1: \<open>M = add_mset L M1\<close>
    using multi_member_split[OF L] by blast
  obtain M2 where M2: \<open>M1 = add_mset L' M2\<close>
    using multi_member_split[of L' M1] LL' L' unfolding M1 by (auto simp: add_mset_eq_add_mset)
  show False
    using dist unfolding M1 M2 by auto
qed

lemma no_dup_distinct_mset[intro!]:
  assumes n_d: \<open>no_dup M\<close>
  shows \<open>distinct_mset (negate_ann_lits M)\<close>
  unfolding negate_ann_lits_def no_dup_def
proof (subst distinct_image_mset_inj)
  show \<open>inj_on (\<lambda>L. - lit_of L) (set_mset (mset M))\<close>
    unfolding inj_on_def Ball_def
  proof (intro allI impI, rule ccontr)
    fix L L'
    assume
      L: \<open>L \<in># mset M\<close> and
      L': \<open>L' \<in># mset M\<close> and
      lit: \<open>- lit_of L = - lit_of L'\<close> and
      LL': \<open>L \<noteq> L'\<close>
    have \<open>atm_of (lit_of L) = atm_of (lit_of L')\<close>
      using lit by auto
    moreover have \<open>atm_of (lit_of L) \<in># (\<lambda>l. atm_of (lit_of l)) `# mset M\<close>
      using L by auto
    moreover have \<open>atm_of (lit_of L') \<in># (\<lambda>l. atm_of (lit_of l)) `# mset M\<close>
      using L' by auto
    ultimately show False
      using assms LL' L L' unfolding distinct_mset_mset_distinct[symmetric] mset_map no_dup_def
      apply - apply (rule distinct_image_mset_not_equal[of L L' \<open>(\<lambda>l. atm_of (lit_of l))\<close>])
      by auto
  qed
next
  show \<open>distinct_mset (mset M)\<close>
    using no_dup_imp_distinct[OF n_d] by simp
qed

lemma in_negate_trial_iff: \<open>L \<in># negate_ann_lits M \<longleftrightarrow> - L \<in> lits_of_l M\<close>
  unfolding negate_ann_lits_def lits_of_def by (auto simp: uminus_lit_swap)

inductive conflict_opt :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S T :: 'st where
conflict_opt_rule:
  \<open>conflict_opt S T\<close>
  if
    \<open>negate_ann_lits (trail S) \<in># conflicting_clss S\<close>
    \<open>conflicting S = None\<close>
    \<open>T \<sim> update_conflicting (Some (negate_ann_lits (trail S))) S\<close>

inductive_cases conflict_optE: \<open>conflict_opt S T\<close>

text \<open>There are two properties related about the trail and the improvements:
  \<^item> \<^term>\<open>optimal_improve\<close> states that there is no smaller improvement at all.
  \<^item> \<^term>\<open>no_smaller_improve\<close> is the corresponding invariant, that holds between two decisions.
\<close>
definition optimal_improve :: "('v, 'v literal multiset) ann_lit list \<Rightarrow> 'st \<Rightarrow> bool" where
  \<open>optimal_improve tr S \<longleftrightarrow> (\<forall>M M'. tr = M' @ M \<longrightarrow> M' \<noteq> [] \<longrightarrow> \<not>is_improving M S)\<close>

definition no_smaller_improve :: "'st \<Rightarrow> bool" where
  \<open>no_smaller_improve S \<longleftrightarrow> (\<forall>M M' K. trail S = M' @ Decided K # M \<longrightarrow> \<not>is_improving M S)\<close>

text \<open>We are \<^emph>\<open>not\<close> requiring that improve is done as early as possible, only that we reduce the
  trail to the minimum model.\<close>
inductive improve :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
improve_rule:
  \<open>improve S T\<close>
  if
    \<open>trail S = M' @ M\<close> and
    \<open>is_improving M S\<close> and
    \<open>optimal_improve M S\<close> and
    \<open>conflicting S = None\<close> and
    \<open>T \<sim> update_weight_information M S\<close>

inductive_cases improveE: \<open>improve S T\<close>

lemma invs_update_weight_information[simp]:
  \<open>no_strange_atm (update_weight_information C S) = (no_strange_atm S)\<close>
  \<open>cdcl\<^sub>W_M_level_inv (update_weight_information C S) = cdcl\<^sub>W_M_level_inv S\<close>
  \<open>distinct_cdcl\<^sub>W_state (update_weight_information C S) = distinct_cdcl\<^sub>W_state S\<close>
  \<open>cdcl\<^sub>W_conflicting (update_weight_information C S) = cdcl\<^sub>W_conflicting S\<close>
  \<open>cdcl\<^sub>W_learned_clause (update_weight_information C S) = cdcl\<^sub>W_learned_clause S\<close>
  unfolding no_strange_atm_def cdcl\<^sub>W_M_level_inv_def distinct_cdcl\<^sub>W_state_def cdcl\<^sub>W_conflicting_def
    cdcl\<^sub>W_learned_clause_def cdcl\<^sub>W_all_struct_inv_def by auto

lemma conflict_opt_cdcl\<^sub>W_all_struct_inv:
  assumes \<open>conflict_opt S T\<close> and
    inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state T)\<close>
  using assms atms_of_conflicting_clss[of T] atms_of_conflicting_clss[of S]
  apply (induction rule: conflict_opt.cases)
  by (auto simp add: cdcl\<^sub>W_restart_mset.no_strange_atm_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
      cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      true_annots_true_cls_def_iff_negation_in_model
      in_negate_trial_iff cdcl\<^sub>W_restart_mset_state cdcl\<^sub>W_restart_mset.clauses_def
      distinct_mset_mset_conflicting_clss abs_state_def
      intro!: true_clss_cls_in)

lemma reduce_trail_to_update_weight_information[simp]:
  \<open>trail (reduce_trail_to M (update_weight_information M' S)) = trail (reduce_trail_to M S)\<close>
  unfolding trail_reduce_trail_to_drop by auto

lemma additional_info_weight_additional_info': \<open>additional_info S = (weight S, additional_info' S)\<close>
  using state_prop[of S] state_prop'[of S] by auto

lemma
  weight_reduce_trail_to[simp]: \<open>weight (reduce_trail_to M S) = weight S\<close> and
  additional_info'_reduce_trail_to[simp]: \<open>additional_info' (reduce_trail_to M S) = additional_info' S\<close>
  using additional_info_reduce_trail_to[of M S] unfolding additional_info_weight_additional_info'
  by auto

lemma conflicting_clss_reduce_trail_to[simp]: \<open>conflicting_clss (reduce_trail_to M S) = conflicting_clss S\<close>
  unfolding conflicting_clss_def by auto

lemma improve_cdcl\<^sub>W_all_struct_inv:
  assumes \<open>improve S T\<close> and
    inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state T)\<close>
  using assms atms_of_conflicting_clss[of T] atms_of_conflicting_clss[of S]
proof (induction rule: improve.cases)
  case (improve_rule M' M T)
  moreover have [simp]: \<open>M' @ a @ Propagated L mark # b = (M' @ a) @ Propagated L mark # b\<close>
    for a L mark b by auto
  moreover
  have \<open>all_decomposition_implies
     (set_mset (init_clss S) \<union> set_mset (conflicting_clss S) \<union> set_mset (learned_clss S))
     (get_all_ann_decomposition (M' @ M)) \<Longrightarrow>
    all_decomposition_implies
     (set_mset (init_clss S) \<union> set_mset (conflicting_clss (update_weight_information M S)) \<union>
      set_mset (learned_clss S))
     (get_all_ann_decomposition (M' @ M))\<close>
      apply (rule all_decomposition_implies_mono)
      using improve_rule(3) conflicting_clss_update_weight_information_mono[of S] inv by auto
    ultimately show ?case
      using conflicting_clss_update_weight_information_mono[of S M]
      by (auto 6 2 simp add: cdcl\<^sub>W_restart_mset.no_strange_atm_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
          cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
          true_annots_true_cls_def_iff_negation_in_model
          in_negate_trial_iff cdcl\<^sub>W_restart_mset_state cdcl\<^sub>W_restart_mset.clauses_def
          image_Un distinct_mset_mset_conflicting_clss abs_state_def
          conflicting_clss_update_weight_information_in
          simp del: append_assoc
          dest: no_dup_appendD consistent_interp_unionD)
qed

lemma exists_lit_max_level_in_negate_ann_lits:
  \<open>negate_ann_lits M \<noteq> {#} \<Longrightarrow> \<exists>L\<in>#negate_ann_lits M. get_level M L = count_decided M\<close>
  by (cases \<open>M\<close>) (auto simp: negate_ann_lits_def)

text \<open>\<^term>\<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant\<close> is too restrictive:
  \<^term>\<open>cdcl\<^sub>W_restart_mset.no_smaller_confl\<close> is needed but does not hold(at least, if cannot
  ensure that conflicts are found as soon as possible).\<close>
lemma improve_no_smaller_conflict:
  assumes \<open>improve S T\<close> and
    \<open>no_smaller_confl S\<close>
  shows \<open>no_smaller_confl T\<close> and \<open>conflict_is_false_with_level T\<close>
  using assms apply (induction rule: improve.induct)
  unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant_def
  by (auto simp: cdcl\<^sub>W_restart_mset_state no_smaller_confl_def cdcl\<^sub>W_restart_mset.clauses_def
      exists_lit_max_level_in_negate_ann_lits)

lemma conflict_opt_no_smaller_conflict:
  assumes \<open>conflict_opt S T\<close> and
    \<open>no_smaller_confl S\<close>
  shows \<open>no_smaller_confl T\<close> and \<open>conflict_is_false_with_level T\<close>
  using assms by (induction rule: conflict_opt.induct)
  (auto simp: cdcl\<^sub>W_restart_mset_state no_smaller_confl_def cdcl\<^sub>W_restart_mset.clauses_def
      exists_lit_max_level_in_negate_ann_lits cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant_def)

fun no_confl_prop_impr where
  \<open>no_confl_prop_impr S \<longleftrightarrow>
    no_step propagate S \<and> no_step conflict S \<and> no_step improve S \<and> no_step conflict_opt S\<close>

inductive cdcl_opt :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> for S :: 'st where
cdcl_conflict: "conflict S S' \<Longrightarrow> cdcl_opt S S'" |
cdcl_propagate: "propagate S S' \<Longrightarrow> cdcl_opt S S'" |
cdcl_improve: "improve S S' \<Longrightarrow> cdcl_opt S S'" |
cdcl_conflict_opt: "conflict_opt S S' \<Longrightarrow> cdcl_opt S S'" |
cdcl_other': "cdcl\<^sub>W_o S S' \<Longrightarrow> cdcl_opt S S'"

inductive cdcl_opt_stgy :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> for S :: 'st where
cdcl_opt_conflict: "conflict S S' \<Longrightarrow> cdcl_opt_stgy S S'" |
cdcl_opt_propagate: "propagate S S' \<Longrightarrow> cdcl_opt_stgy S S'" |
cdcl_opt_improve: "improve S S' \<Longrightarrow> cdcl_opt_stgy S S'" |
cdcl_opt_conflict_opt: "conflict_opt S S' \<Longrightarrow> cdcl_opt_stgy S S'" |
cdcl_opt_other': "cdcl\<^sub>W_o S S' \<Longrightarrow> no_confl_prop_impr S \<Longrightarrow> cdcl_opt_stgy S S'"

lemma conflict_opt_conflict:
  \<open>conflict_opt S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.conflict (abs_state S) (abs_state T)\<close>
  by (induction rule: conflict_opt.cases)
    (auto intro!: cdcl\<^sub>W_restart_mset.conflict_rule[of _ \<open>negate_ann_lits (trail S)\<close>]
      simp: cdcl\<^sub>W_restart_mset.clauses_def cdcl\<^sub>W_restart_mset_state
      true_annots_true_cls_def_iff_negation_in_model abs_state_def
      in_negate_trial_iff)

lemma conflict_conflict:
  \<open>conflict S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.conflict (abs_state S) (abs_state T)\<close>
  by (induction rule: conflict.cases)
    (auto intro!: cdcl\<^sub>W_restart_mset.conflict_rule
      simp: clauses_def cdcl\<^sub>W_restart_mset.clauses_def cdcl\<^sub>W_restart_mset_state
      true_annots_true_cls_def_iff_negation_in_model abs_state_def
      in_negate_trial_iff)


lemma propagate_propagate:
  \<open>propagate S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.propagate (abs_state S) (abs_state T)\<close>
  by (induction rule: propagate.cases)
    (auto intro!: cdcl\<^sub>W_restart_mset.propagate_rule
      simp: clauses_def cdcl\<^sub>W_restart_mset.clauses_def cdcl\<^sub>W_restart_mset_state
      true_annots_true_cls_def_iff_negation_in_model abs_state_def
      in_negate_trial_iff)

lemma decide_decide:
  \<open>decide S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.decide (abs_state S) (abs_state T)\<close>
  by (induction rule: decide.cases)
    (auto intro!: cdcl\<^sub>W_restart_mset.decide_rule
      simp: clauses_def cdcl\<^sub>W_restart_mset.clauses_def cdcl\<^sub>W_restart_mset_state
      true_annots_true_cls_def_iff_negation_in_model abs_state_def
      in_negate_trial_iff)

lemma skip_skip:
  \<open>skip S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.skip (abs_state S) (abs_state T)\<close>
  by (induction rule: skip.cases)
    (auto intro!: cdcl\<^sub>W_restart_mset.skip_rule
      simp: clauses_def cdcl\<^sub>W_restart_mset.clauses_def cdcl\<^sub>W_restart_mset_state
      true_annots_true_cls_def_iff_negation_in_model abs_state_def
      in_negate_trial_iff)

lemma resolve_resolve:
  \<open>resolve S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.resolve (abs_state S) (abs_state T)\<close>
  by (induction rule: resolve.cases)
    (auto intro!: cdcl\<^sub>W_restart_mset.resolve_rule
      simp: clauses_def cdcl\<^sub>W_restart_mset.clauses_def cdcl\<^sub>W_restart_mset_state
      true_annots_true_cls_def_iff_negation_in_model abs_state_def
      in_negate_trial_iff)

lemma backtrack_backtrack:
  \<open>backtrack S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.backtrack (abs_state S) (abs_state T)\<close>
proof (induction rule: backtrack.cases)
  case (backtrack_rule L D K M1 M2 D' i T)
  have H: \<open>set_mset (init_clss S) \<union> set_mset (learned_clss S)
    \<subseteq> set_mset (init_clss S) \<union> set_mset (conflicting_clss S) \<union> set_mset (learned_clss S)\<close>
    by auto
  have [simp]: \<open>cdcl\<^sub>W_restart_mset.reduce_trail_to M1
       (trail S, init_clss S + conflicting_clss S, add_mset D (learned_clss S), None) =
    (M1, init_clss S + conflicting_clss S, add_mset D (learned_clss S), None)\<close> for D
    using backtrack_rule by (auto simp add: cdcl\<^sub>W_restart_mset_reduce_trail_to
        cdcl\<^sub>W_restart_mset_state)
  show ?case
    using true_clss_cls_subset[of \<open>set_mset (init_clss S) \<union> set_mset (learned_clss S)\<close>
      \<open>set_mset (init_clss S) \<union> set_mset (conflicting_clss S) \<union> set_mset (learned_clss S)\<close>
      \<open>add_mset L D'\<close>, OF H] backtrack_rule
    by (auto intro!: cdcl\<^sub>W_restart_mset.backtrack.intros
        simp: cdcl\<^sub>W_restart_mset_state abs_state_def clauses_def cdcl\<^sub>W_restart_mset.clauses_def)
qed

lemma cdcl\<^sub>W_o_cdcl\<^sub>W_o:
  \<open>cdcl\<^sub>W_o S S' \<Longrightarrow> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o (abs_state S) (abs_state S')\<close>
  apply (induction rule: cdcl\<^sub>W_o_all_rules_induct)
     apply (simp add: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o.simps decide_decide; fail)
    apply (blast dest: backtrack_backtrack)
   apply (blast dest: skip_skip)
  by (blast dest: resolve_resolve)

lemma cdcl_opt_stgy_all_struct_inv:
  assumes \<open>cdcl_opt S T\<close> and \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state T)\<close>
  using assms
proof (induction rule: cdcl_opt.cases)
  case (cdcl_conflict S')
  then show ?case
    by (blast dest: conflict_conflict cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy.intros
      intro: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_cdcl\<^sub>W_all_struct_inv)
next
  case (cdcl_propagate S')
  then show ?case
    by (blast dest: propagate_propagate cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy.intros
      intro: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_cdcl\<^sub>W_all_struct_inv)
next
  case (cdcl_improve S')
  then show ?case
    using improve_cdcl\<^sub>W_all_struct_inv by blast
next
  case (cdcl_conflict_opt S')
  then show ?case
    using conflict_opt_cdcl\<^sub>W_all_struct_inv by blast
next
  case (cdcl_other' S')
  then show ?case
    by (meson cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_inv cdcl\<^sub>W_restart_mset.other cdcl\<^sub>W_o_cdcl\<^sub>W_o)
qed

lemma cdcl_opt_stgy_cdcl_opt: \<open>cdcl_opt_stgy S T \<Longrightarrow> cdcl_opt S T\<close>
  by (auto simp: cdcl_opt_stgy.simps intro: cdcl_opt.intros)

lemma rtranclp_cdcl_opt_stgy_cdcl_opt: \<open>cdcl_opt_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl_opt\<^sup>*\<^sup>* S T\<close>
  by (induction rule: rtranclp_induct)
   (auto dest: cdcl_opt_stgy_cdcl_opt)

text \<open>The following does \<^emph>\<open>not\<close> hold, because we cannot guarantee the absence of conflict of
  smaller level after \<^term>\<open>improve\<close> and \<^term>\<open>conflict_opt\<close>.\<close>
lemma cdcl_opt_all_stgy_inv:
  assumes \<open>cdcl_opt S T\<close> and \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (abs_state S)\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (abs_state T)\<close>
  oops

lemma skip_conflict_is_false_with_level:
  assumes \<open>skip S T\<close> and
    struct_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> and
    confl_inv:\<open>conflict_is_false_with_level S\<close>
  shows \<open>conflict_is_false_with_level T\<close>
  using assms
proof induction
  case (skip_rule L C' M D T) note tr_S = this(1) and D = this(2) and T = this(5)
  have conflicting: \<open>cdcl\<^sub>W_conflicting S\<close> and
    lev: "cdcl\<^sub>W_M_level_inv S"
    using struct_inv unfolding cdcl\<^sub>W_conflicting_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_M_level_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by (auto simp: abs_state_def cdcl\<^sub>W_restart_mset_state)
  obtain La where
    "La \<in># D" and
    "get_level (Propagated L C' # M) La = backtrack_lvl S"
    using skip_rule confl_inv by auto
  moreover {
    have "atm_of La \<noteq> atm_of L"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then have La: "La = L" using \<open>La \<in># D\<close> \<open>- L \<notin># D\<close>
        by (auto simp add: atm_of_eq_atm_of)
      have "Propagated L C' # M \<Turnstile>as CNot D"
        using conflicting tr_S D unfolding cdcl\<^sub>W_conflicting_def by auto
      then have "-L \<in> lits_of_l M"
        using \<open>La \<in># D\<close> in_CNot_implies_uminus(2)[of L D "Propagated L C' # M"] unfolding La
        by auto
      then show False using lev tr_S unfolding cdcl\<^sub>W_M_level_inv_def consistent_interp_def by auto
    qed
    then have "get_level (Propagated L C' # M) La = get_level M La" by auto
  }
  ultimately show ?case using D tr_S T by auto
qed

lemma propagate_conflict_is_false_with_level:
  assumes \<open>propagate S T\<close> and
    struct_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> and
    confl_inv:\<open>conflict_is_false_with_level S\<close>
  shows \<open>conflict_is_false_with_level T\<close>
  using assms by (induction rule: propagate.induct) auto

lemma cdcl\<^sub>W_o_conflict_is_false_with_level:
  assumes \<open>cdcl\<^sub>W_o S T\<close> and
    struct_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> and
    confl_inv: \<open>conflict_is_false_with_level S\<close>
  shows \<open>conflict_is_false_with_level T\<close>
  apply (rule cdcl\<^sub>W_o_conflict_is_false_with_level_inv[of S T])
  subgoal using assms by auto
  subgoal using struct_inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_M_level_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by (auto simp: abs_state_def cdcl\<^sub>W_restart_mset_state)
  subgoal using assms by auto
  subgoal using struct_inv unfolding distinct_cdcl\<^sub>W_state_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
       cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
    by (auto simp: abs_state_def cdcl\<^sub>W_restart_mset_state)
  subgoal using struct_inv unfolding cdcl\<^sub>W_conflicting_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
    by (auto simp: abs_state_def cdcl\<^sub>W_restart_mset_state)
  done

lemma cdcl\<^sub>W_o_no_smaller_confl:
  assumes \<open>cdcl\<^sub>W_o S T\<close> and
    struct_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> and
    confl_inv: \<open>no_smaller_confl S\<close> and
    lev: \<open>conflict_is_false_with_level S\<close> and
    n_s: \<open>no_confl_prop_impr S\<close>
  shows \<open>no_smaller_confl T\<close>
  apply (rule cdcl\<^sub>W_o_no_smaller_confl_inv[of S T])
  subgoal using assms by (auto dest!:cdcl\<^sub>W_o_cdcl\<^sub>W_o)[]
  subgoal using n_s by auto
  subgoal using struct_inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_M_level_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by (auto simp: abs_state_def cdcl\<^sub>W_restart_mset_state)
  subgoal using lev by fast
  subgoal using confl_inv unfolding distinct_cdcl\<^sub>W_state_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
       cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def cdcl\<^sub>W_restart_mset.no_smaller_confl_def
    by (auto simp: abs_state_def cdcl\<^sub>W_restart_mset_state clauses_def)
  done

lemma (in conflict_driven_clause_learning\<^sub>W) conflict_conflict_is_false_with_level_all_inv:
  \<open>conflict S T \<Longrightarrow>
  no_smaller_confl S \<Longrightarrow>
  cdcl\<^sub>W_all_struct_inv S \<Longrightarrow>
  conflict_is_false_with_level T\<close>
  by (rule conflict_conflict_is_false_with_level) (auto simp: cdcl\<^sub>W_all_struct_inv_def)

lemma (in conflict_driven_clause_learning\<^sub>W) cdcl\<^sub>W_stgy_ex_lit_of_max_level_all_inv:
  assumes
    "cdcl\<^sub>W_stgy S S'" and
    n_l: "no_smaller_confl S" and
    "conflict_is_false_with_level S" and
    "cdcl\<^sub>W_all_struct_inv S"
  shows "conflict_is_false_with_level S'"
  by (rule cdcl\<^sub>W_stgy_ex_lit_of_max_level) (use assms in \<open>auto simp: cdcl\<^sub>W_all_struct_inv_def\<close>)

lemma (in conflict_driven_clause_learning\<^sub>W)  cdcl\<^sub>W_o_conflict_is_false_with_level_inv_all_inv:
  assumes
    \<open>cdcl\<^sub>W_o S T\<close>
    \<open>cdcl\<^sub>W_all_struct_inv S\<close>
    \<open>conflict_is_false_with_level S\<close>
  shows \<open>conflict_is_false_with_level T\<close>
  by (rule cdcl\<^sub>W_o_conflict_is_false_with_level_inv) (use assms in \<open>auto simp: cdcl\<^sub>W_all_struct_inv_def\<close>)

declare cdcl\<^sub>W_restart_mset.conflict_is_false_with_level_def [simp del]

lemma negate_ann_lits_empty_iff: \<open>negate_ann_lits M \<noteq> {#} \<longleftrightarrow> M \<noteq> []\<close>
  by (auto simp: negate_ann_lits_def)

lemma improve_conflict_is_false_with_level:
  assumes \<open>improve S T\<close> and \<open>conflict_is_false_with_level S\<close>
  shows \<open>conflict_is_false_with_level T\<close>
  using assms
proof induction
  case (improve_rule M' M T)
  then show ?case
    by (cases M) (auto simp: cdcl\<^sub>W_restart_mset.conflict_is_false_with_level_def
        abs_state_def cdcl\<^sub>W_restart_mset_state in_negate_trial_iff Bex_def negate_ann_lits_empty_iff
        intro!: exI[of _ \<open>-lit_of (hd M)\<close>])
qed


declare conflict_is_false_with_level_def[simp del]

lemma trail_trail [simp]:
  \<open>CDCL_W_Abstract_State.trail (abs_state S) = trail S\<close>
  by (auto simp: abs_state_def cdcl\<^sub>W_restart_mset_state)

lemma cdcl\<^sub>W_M_level_inv_cdcl\<^sub>W_M_level_inv[iff]:
  \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (abs_state S) = cdcl\<^sub>W_M_level_inv S\<close>
  by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
      cdcl\<^sub>W_M_level_inv_def cdcl\<^sub>W_restart_mset_state)

lemma cdcl_opt_stgy_no_smaller_confl:
  assumes \<open>cdcl_opt_stgy S T\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> and
    \<open>no_smaller_confl S\<close> and
    \<open>conflict_is_false_with_level S\<close> and
    \<open>no_smaller_improve S\<close>
  shows \<open>no_smaller_confl T\<close>
  using assms
proof (induction rule: cdcl_opt_stgy.cases)
  case (cdcl_opt_conflict S')
  then show ?case
    using conflict_no_smaller_confl_inv by blast
next
  case (cdcl_opt_propagate S')
  then show ?case
    using propagate_no_smaller_confl_inv by blast
next
  case (cdcl_opt_improve S')
  then show ?case
    by (auto simp: no_smaller_confl_def no_smaller_improve_def improve.simps)
next
  case (cdcl_opt_conflict_opt S')
  then show ?case
    by (auto simp: no_smaller_confl_def conflict_opt.simps)
next
  case (cdcl_opt_other' S')
  show ?case
    apply (rule cdcl\<^sub>W_o_no_smaller_confl_inv)
    using cdcl_opt_other' by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
qed

lemma cdcl_opt_stgy_conflict_is_false_with_level:
  assumes \<open>cdcl_opt_stgy S T\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> and
    \<open>no_smaller_confl S\<close> and
    \<open>conflict_is_false_with_level S\<close> and
    \<open>no_smaller_improve S\<close>
  shows \<open>conflict_is_false_with_level T\<close>
  using assms
proof (induction rule: cdcl_opt_stgy.cases)
  case (cdcl_opt_conflict S')
  then show ?case
    using conflict_conflict_is_false_with_level
    by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
next
  case (cdcl_opt_propagate S')
  then show ?case
    using propagate_conflict_is_false_with_level
    by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
next
  case (cdcl_opt_improve S')
  then show ?case
    using improve_conflict_is_false_with_level by blast
next
  case (cdcl_opt_conflict_opt S')
  then show ?case
    using conflict_opt_no_smaller_conflict(2) by blast
next
  case (cdcl_opt_other' S')
  show ?case
    apply (rule cdcl\<^sub>W_o_conflict_is_false_with_level)
    using cdcl_opt_other' by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
qed

lemma decided_cons_eq_append_decide_cons: \<open>Decided L # MM = M' @ Decided K # M \<longleftrightarrow>
  (M' \<noteq> [] \<and> hd M' = Decided L \<and> MM = tl M' @ Decided K # M) \<or>
  (M' = [] \<and> L = K \<and> MM = M)\<close>
  by (cases M') auto

lemma either_all_false_or_earliest_decomposition:
  shows \<open>(\<forall>K K'. L = K' @ K \<longrightarrow> \<not>P K) \<or>
      (\<exists>L' L''. L = L'' @ L' \<and> P L' \<and> (\<forall>K K'. L' = K' @ K \<longrightarrow> K' \<noteq> [] \<longrightarrow> \<not>P K))\<close>
  apply (induction L)
  subgoal by auto
  subgoal for a
    by (metis append_Cons append_Nil list.sel(3) tl_append2)
  done

lemma trail_is_improving_Ex_improve:
  assumes confl: \<open>conflicting S = None\<close> and
    imp: \<open>is_improving (trail S) S\<close>
  shows \<open>Ex (improve S)\<close>
proof -
  let ?M = \<open>trail S\<close>
  obtain M M' where \<open>?M = M' @ M\<close> and \<open>optimal_improve M S\<close> and \<open>is_improving M S\<close>
    using either_all_false_or_earliest_decomposition[where P = \<open>\<lambda>M. is_improving M S\<close> and
        L = \<open>trail S\<close>]
    using imp by (auto simp: optimal_improve_def)
  then show ?thesis
    unfolding Ex_def
    using confl by (auto simp: improve.simps)
qed

lemma cdcl_opt_stgy_no_smaller_improve:
  assumes \<open>cdcl_opt_stgy S T\<close> and
    \<open>no_smaller_improve S\<close> and
    struct_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close>
  shows \<open>no_smaller_improve T\<close>
  using assms
proof induction
  case (cdcl_opt_conflict S')
  then show ?case
    by (auto simp: no_smaller_improve_def elim!: conflictE)
next
  case (cdcl_opt_propagate S')
  then show ?case
    by (auto simp: no_smaller_improve_def propagated_cons_eq_append_decide_cons
        elim!: propagateE)
next
  case (cdcl_opt_improve S')
  then show ?case
    using is_improving_mono[of _ S]
    by (auto simp: no_smaller_improve_def improve.simps)
next
  case (cdcl_opt_conflict_opt S')
  then show ?case
    unfolding conflict_opt.simps no_smaller_improve_def by auto
next
  case (cdcl_opt_other' S') note o = this(1) and no_confl = this(2) and no_impr = this(3)
  then have \<open>no_step improve S\<close>
    by auto
  then have H: \<open>\<not>is_improving (trail S) S\<close> if \<open>conflicting S = None\<close>
    using that by (auto dest!: trail_is_improving_Ex_improve)

  show ?case
    using o
  proof induction
    case (decide S')
    then show ?case
      using no_impr
      by (auto simp: improve.simps decided_cons_eq_append_decide_cons optimal_improve_def
          H no_smaller_improve_def decide.simps)[]
  next
    case (bj S')
    then show ?case
      apply (induction rule: cdcl\<^sub>W_bj.cases)
      subgoal
        apply (cases \<open>trail S\<close>)
        using no_impr
        unfolding cdcl\<^sub>W_o.simps no_smaller_improve_def decide.simps
         apply (auto simp: improve.simps decided_cons_eq_append_decide_cons optimal_improve_def
            elim!: skipE resolveE backtrackE cdcl\<^sub>W_bjE)
        done
      subgoal
        apply (cases \<open>trail S\<close>)
        using no_impr
        unfolding cdcl\<^sub>W_o.simps no_smaller_improve_def decide.simps
         apply (auto simp: improve.simps decided_cons_eq_append_decide_cons optimal_improve_def
            elim!: skipE resolveE backtrackE cdcl\<^sub>W_bjE)
        done
      subgoal
        using no_impr
        unfolding cdcl\<^sub>W_o.simps no_smaller_improve_def decide.simps
        apply (auto simp: improve.simps decided_cons_eq_append_decide_cons optimal_improve_def
            propagated_cons_eq_append_decide_cons elim!: skipE resolveE backtrackE cdcl\<^sub>W_bjE)
        done
      done
  qed
qed

definition cdcl_opt_stgy_inv :: "'st \<Rightarrow> bool" where
  \<open>cdcl_opt_stgy_inv S \<longleftrightarrow> conflict_is_false_with_level S \<and> no_smaller_confl S \<and> no_smaller_improve S\<close>

lemma cdcl_opt_stgy_stgy_inv:
  \<open>cdcl_opt_stgy S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S) \<Longrightarrow>
    cdcl_opt_stgy_inv S \<Longrightarrow> cdcl_opt_stgy_inv T\<close>
  unfolding cdcl_opt_stgy_inv_def
  using cdcl_opt_stgy_conflict_is_false_with_level cdcl_opt_stgy_no_smaller_confl
    cdcl_opt_stgy_no_smaller_improve by blast

lemma learned_clss_learned_clss[simp]:
    \<open>CDCL_W_Abstract_State.learned_clss (abs_state S) = learned_clss S\<close>
  by (auto simp: abs_state_def cdcl\<^sub>W_restart_mset_state)

lemma state_eq_init_clss_abs_state[state_simp, simp]:
  \<open>S \<sim> T \<Longrightarrow> CDCL_W_Abstract_State.init_clss (abs_state S) = CDCL_W_Abstract_State.init_clss (abs_state T)\<close>
  by (auto simp: abs_state_def cdcl\<^sub>W_restart_mset_state)

lemma
  init_clss_abs_state_update_conflicting[simp]:
    \<open>CDCL_W_Abstract_State.init_clss (abs_state (update_conflicting (Some D) S)) =
       CDCL_W_Abstract_State.init_clss (abs_state S)\<close> and
  init_clss_abs_state_cons_trail[simp]:
    \<open>CDCL_W_Abstract_State.init_clss (abs_state (cons_trail K S)) =
      CDCL_W_Abstract_State.init_clss (abs_state S)\<close>
  by (auto simp: abs_state_def cdcl\<^sub>W_restart_mset_state)

lemma cdcl_opt_cdcl\<^sub>W_learned_clauses_entailed_by_init:
  assumes
    \<open>cdcl_opt S T\<close> and
    entailed: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (abs_state S)\<close> and
    all_struct: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (abs_state T)\<close>
  using assms(1)
proof (induction rule: cdcl_opt.cases)
  case (cdcl_conflict S')
  then show ?case
    using entailed
    by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def
        elim!: conflictE)
next
  case (cdcl_propagate S')
  then show ?case
    using entailed
    by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def
        elim!: propagateE)
next
  case (cdcl_improve S')
  moreover have \<open>set_mset (CDCL_W_Abstract_State.init_clss (abs_state S)) \<subseteq>
    set_mset (CDCL_W_Abstract_State.init_clss (abs_state (update_weight_information M S)))\<close>
       if \<open>is_improving M S\<close> for M
    using that conflicting_clss_update_weight_information_mono[OF all_struct]
    by (auto simp: abs_state_def cdcl\<^sub>W_restart_mset_state)
  ultimately show ?case
    using entailed
    by (fastforce simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def
        elim!: improveE intro: true_clss_clss_subsetI)
next
  case (cdcl_other' S') note T = this(1) and o = this(2)
  show ?case
    apply (rule cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed[of \<open>abs_state S\<close>])
    subgoal
      using o unfolding T by (blast dest: cdcl\<^sub>W_o_cdcl\<^sub>W_o cdcl\<^sub>W_restart_mset.other)
    subgoal using all_struct unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def by fast
    subgoal using entailed by fast
    done
next
  case (cdcl_conflict_opt S')
  then show ?case
    using entailed
    by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def
        elim!: conflict_optE)
qed

lemma atms_of_init_clss_conflicting_clss[simp]:
  \<open>atms_of_mm (init_clss S) \<union> atms_of_mm (conflicting_clss S) = atms_of_mm (init_clss S)\<close>
  using atms_of_conflicting_clss[of S] by blast

lemma no_strange_atm_no_strange_atm[simp]:
  \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (abs_state S) = no_strange_atm S\<close>
  using atms_of_conflicting_clss[of S]
  unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def no_strange_atm_def
  by (auto simp: abs_state_def cdcl\<^sub>W_restart_mset_state)

lemma cdcl\<^sub>W_conflicting_cdcl\<^sub>W_conflicting[simp]:
  \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (abs_state S) = cdcl\<^sub>W_conflicting S\<close>
  unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def cdcl\<^sub>W_conflicting_def
  by (auto simp: abs_state_def cdcl\<^sub>W_restart_mset_state)

lemma distinct_cdcl\<^sub>W_state_distinct_cdcl\<^sub>W_state:
  \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (abs_state S) \<Longrightarrow> distinct_cdcl\<^sub>W_state S\<close>
  unfolding cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def distinct_cdcl\<^sub>W_state_def
  by (auto simp: abs_state_def cdcl\<^sub>W_restart_mset_state)


lemma no_step_cdcl_opt_cdcl\<^sub>W: \<open>no_step cdcl_opt S \<Longrightarrow> no_step cdcl\<^sub>W S\<close>
  by (meson cdcl\<^sub>W.cases cdcl_opt.simps)

lemma sim_abs_state_simp: \<open>S \<sim> T \<Longrightarrow> abs_state S = abs_state T\<close>
  by (auto simp: abs_state_def)

lemma cdcl\<^sub>W_same_weight: \<open>cdcl\<^sub>W S U \<Longrightarrow> weight S = weight U\<close>
  by (induction rule: cdcl\<^sub>W.induct)
    (auto simp: improve.simps cdcl\<^sub>W.simps
        propagate.simps sim_abs_state_simp abs_state_def cdcl\<^sub>W_restart_mset_state
        clauses_def conflict.simps cdcl\<^sub>W_o.simps decide.simps cdcl\<^sub>W_bj.simps
	skip.simps resolve.simps backtrack.simps)

lemma cdcl\<^sub>W_all_struct_inv_restart_cdcl\<^sub>W_all_struct_inv:
  \<open>cdcl\<^sub>W_all_struct_inv b \<Longrightarrow> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state b)\<close>
  by (auto simp:
      cdcl\<^sub>W_restart_mset.no_strange_atm_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
      cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      true_annots_true_cls_def_iff_negation_in_model
      in_negate_trial_iff cdcl\<^sub>W_restart_mset_state cdcl\<^sub>W_restart_mset.clauses_def
      distinct_mset_mset_conflicting_clss abs_state_def
      no_strange_atm_def
      cdcl\<^sub>W_M_level_inv_def
      distinct_cdcl\<^sub>W_state_def cdcl\<^sub>W_conflicting_def
      cdcl\<^sub>W_learned_clause_def cdcl\<^sub>W_all_struct_inv_def
      true_annots_true_cls_def_iff_negation_in_model
      in_negate_trial_iff cdcl\<^sub>W_restart_mset_state clauses_def
      distinct_mset_mset_conflicting_clss abs_state_def
      intro: all_decomposition_implies_mono true_clss_cls_subset)


lemma wf_cdcl_opt:
  assumes improve: \<open>\<And>S T. improve S T \<Longrightarrow> (\<nu> (weight T), \<nu> (weight S)) \<in> R\<close> and
    wf_R: \<open>wf R\<close>
  shows \<open>wf {(T, S). cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S) \<and> cdcl_opt S T}\<close>
    (is \<open>wf ?A\<close>)
proof -
  let ?R = \<open>{(T, S). (\<nu> (weight T), \<nu> (weight S)) \<in> R }\<close>

  have \<open>wf {(T, S).  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv S \<and> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W S T}\<close>
    by (rule cdcl\<^sub>W_restart_mset.wf_cdcl\<^sub>W)
  from wf_if_measure_f[OF this, of abs_state]
  have wf: \<open>wf {(T, S).  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S) \<and>
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W (abs_state S) (abs_state T) \<and> weight S = weight T}\<close>
    (is \<open>wf ?CDCL\<close>)
    by (rule wf_subset) (auto simp: cdcl\<^sub>W_all_struct_inv_restart_cdcl\<^sub>W_all_struct_inv)
  have \<open>wf (?R \<union> ?CDCL)\<close>
    apply (rule wf_union_compatible)
    subgoal by (rule wf_if_measure_f[OF wf_R, of \<open>\<lambda>x. \<nu> (weight x)\<close>])
    subgoal by (rule wf)
    subgoal by (auto simp: cdcl\<^sub>W_same_weight)
    done

  moreover have \<open>?A \<subseteq> ?R \<union> ?CDCL\<close>
    by (auto dest: cdcl\<^sub>W.intros cdcl\<^sub>W_restart_mset.W_propagate cdcl\<^sub>W_restart_mset.W_other
          conflict_conflict propagate_propagate decide_decide improve conflict_opt_conflict
          cdcl\<^sub>W_o_cdcl\<^sub>W_o cdcl\<^sub>W_restart_mset.W_conflict W_conflict
	simp: cdcl\<^sub>W_same_weight cdcl_opt.simps
	elim: conflict_optE)
  ultimately show ?thesis
    by (rule wf_subset)
qed

lemma cdcl_opt_stgy_invD:
  assumes \<open>cdcl_opt_stgy_inv S\<close>
  shows \<open>cdcl\<^sub>W_stgy_invariant S\<close>
  using assms unfolding cdcl\<^sub>W_stgy_invariant_def cdcl_opt_stgy_inv_def
  by auto

lemma (in conflict_driven_clause_learning\<^sub>W) no_step_cdcl\<^sub>W_total:
  assumes
    \<open>no_step cdcl\<^sub>W S\<close>
    \<open>conflicting S = None\<close>
    \<open>no_strange_atm S\<close>
  shows \<open>total_over_m (lits_of_l (trail S)) (set_mset (clauses S))\<close>
proof (rule ccontr)
  assume \<open>\<not> ?thesis\<close>
  then obtain L where \<open>L \<in> atms_of_mm (clauses S)\<close> and \<open>undefined_lit  (trail S) (Pos L)\<close>
    by (auto simp: total_over_m_def total_over_set_def
      Decided_Propagated_in_iff_in_lits_of_l)
  then have \<open>Ex (decide S)\<close>
    using decide_rule[of S \<open>Pos L\<close> \<open>cons_trail (Decided (Pos L)) S\<close>] assms
    unfolding no_strange_atm_def clauses_def
    by force
  then show False
    using assms by (auto simp: cdcl\<^sub>W.simps)
qed

lemma [simp]:
  \<open>CDCL_W_Abstract_State.conflicting (abs_state S) = conflicting S\<close>
  \<open>cdcl\<^sub>W_restart_mset.clauses (abs_state S) = clauses S + conflicting_clss S\<close>
  by (auto simp: abs_state_def cdcl\<^sub>W_restart_mset_state clauses_def
    cdcl\<^sub>W_restart_mset.clauses_def)

context
  assumes can_always_improve:
     \<open>\<And>S. trail S \<Turnstile>asm clauses S \<Longrightarrow> no_step conflict_opt S \<Longrightarrow>
       conflicting S = None \<Longrightarrow>
       cdcl\<^sub>W_all_struct_inv S \<Longrightarrow>
       total_over_m (lits_of_l (trail S)) (set_mset (clauses S)) \<Longrightarrow> Ex (improve S)\<close>
begin

lemma
  assumes 
    \<open>no_step cdcl_opt S\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close>
  shows \<open>no_step cdcl\<^sub>W_restart_mset.cdcl\<^sub>W (abs_state S)\<close>
proof -
  have \<open>Ex(cdcl_opt S)\<close> if  \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W (abs_state S) T\<close> for T
    using that
  proof cases
    case W_propagate
    then have \<open>\<exists>T. propagate S T \<or> conflict_opt S T \<close>
      apply (auto simp: propagate.simps cdcl\<^sub>W_restart_mset.propagate.simps
        conflict_opt.simps)
      sorry
      find_theorems conflicting_clss is_improving
    then show ?thesis sorry
  next
    case W_conflict
    then show ?thesis sorry
  next
    case W_other
    then show ?thesis sorry
  qed
  then show ?thesis using assms by blast
qed


lemma no_step_cdcl_opt_stgy:
  assumes
    n_s: \<open>no_step cdcl_opt S\<close> and
    all_struct: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> and
    stgy_inv: \<open>cdcl_opt_stgy_inv S\<close>
  shows \<open>conflicting S = None \<or> conflicting S = Some {#}\<close>
proof (rule ccontr)
  assume \<open>\<not> ?thesis\<close>
  then obtain D where \<open>conflicting S = Some D\<close> and \<open>D \<noteq> {#}\<close>
    by auto
  moreover have \<open>no_step cdcl\<^sub>W_stgy S\<close>
    using n_s by (auto simp: cdcl\<^sub>W_stgy.simps cdcl_opt.simps)
  moreover have le: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause (abs_state S)\<close>
    using all_struct unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def by fast
  ultimately show False
    using cdcl\<^sub>W_restart_mset.conflicting_no_false_can_do_step[of \<open>abs_state S\<close>] all_struct stgy_inv le
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl_opt_stgy_inv_def
    by (auto dest!: distinct_cdcl\<^sub>W_state_distinct_cdcl\<^sub>W_state)
qed

lemma no_step_cdcl_opt_stgy_empty_conflict:
  assumes
    n_s: \<open>no_step cdcl_opt S\<close> and
    all_struct: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> and
    stgy_inv: \<open>cdcl_opt_stgy_inv S\<close>
  shows \<open>conflicting S = Some {#}\<close>
proof (rule ccontr)
  assume H: \<open>\<not> ?thesis\<close>
  have all_struct': \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close>
    by (simp add: all_struct cdcl\<^sub>W_all_struct_inv_restart_cdcl\<^sub>W_all_struct_inv)
  have le: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause (abs_state S)\<close>
    using all_struct
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl_opt_stgy_inv_def
    by auto
  have \<open>conflicting S = None \<or> conflicting S = Some {#}\<close>
    using no_step_cdcl_opt_stgy[OF n_s all_struct' stgy_inv le] .
  then have confl: \<open>conflicting S = None\<close>
    using H by blast
  have \<open>no_step cdcl\<^sub>W_stgy S\<close>
    using n_s cdcl\<^sub>W_stgy.simps cdcl_conflict cdcl_other' cdcl_propagate by blast
  then have entail: \<open>trail S \<Turnstile>asm clauses S\<close>
    using confl cdcl\<^sub>W_stgy_final_state_conclusive2[of S] all_struct stgy_inv le
    unfolding cdcl\<^sub>W_all_struct_inv_def cdcl_opt_stgy_inv_def
    by auto
  have \<open>total_over_m (lits_of_l (trail S)) (set_mset (clauses S))\<close>
    using no_step_cdcl\<^sub>W_total[OF no_step_cdcl_opt_cdcl\<^sub>W confl] all_struct n_s
    unfolding cdcl\<^sub>W_all_struct_inv_def
    by auto
  with can_always_improve entail confl all_struct
  show \<open>False\<close>
    using n_s by (auto simp: cdcl_opt.simps)
qed

end

end








locale conflict_driven_clause_learning\<^sub>W_optimal_weight =
  conflict_driven_clause_learning\<^sub>W
    state_eq
    state
    \<comment> \<open>functions for the state:\<close>
      \<comment> \<open>access functions:\<close>
    trail init_clss learned_clss conflicting
      \<comment> \<open>changing state:\<close>
    cons_trail tl_trail add_learned_cls remove_cls
    update_conflicting

      \<comment> \<open>get state:\<close>
    init_state
  for
    state_eq :: "'st \<Rightarrow> 'st \<Rightarrow> bool" (infix "\<sim>" 50) and
    state :: "'st \<Rightarrow> ('v, 'v clause) ann_lits \<times> 'v clauses \<times> 'v clauses \<times> 'v clause option \<times>
      'v clause option \<times> 'b" and
    trail :: "'st \<Rightarrow> ('v, 'v clause) ann_lits" and
    init_clss :: "'st \<Rightarrow> 'v clauses" and
    learned_clss :: "'st \<Rightarrow> 'v clauses" and
    conflicting :: "'st \<Rightarrow> 'v clause option" and

    cons_trail :: "('v, 'v clause) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    tl_trail :: "'st \<Rightarrow> 'st" and
    add_learned_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    remove_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_conflicting :: "'v clause option \<Rightarrow> 'st \<Rightarrow> 'st" and

    init_state :: "'v clauses \<Rightarrow> 'st" +
  fixes
    \<rho> :: \<open>'v clause \<Rightarrow> nat\<close> and
    update_additional_info :: \<open>'v clause option \<times> 'b \<Rightarrow> 'st \<Rightarrow> 'st\<close>
  assumes
    \<rho>_mono: \<open>\<rho> (add_mset L' M') > \<rho> M'\<close> and
    update_additional_info:
      \<open>state S = (M, N, U, C, K) \<Longrightarrow> state (update_additional_info K' S) = (M, N, U, C, K')\<close>
begin

definition update_weight_information :: \<open>('v, 'v clause) ann_lits \<Rightarrow> 'st \<Rightarrow> 'st\<close> where
  \<open>update_weight_information M S = update_additional_info (Some (lit_of `# mset M), snd (additional_info S)) S\<close>

lemma
  trail_update_additional_info[simp]: \<open>trail (update_additional_info w S) = trail S\<close> and
  init_clss_update_additional_info[simp]:
    \<open>init_clss (update_additional_info w S) = init_clss S\<close> and
  learned_clss_update_additional_info[simp]:
    \<open>learned_clss (update_additional_info w S) = learned_clss S\<close> and
  backtrack_lvl_update_additional_info[simp]:
    \<open>backtrack_lvl (update_additional_info w S) = backtrack_lvl S\<close> and
  conflicting_update_additional_info[simp]:
    \<open>conflicting (update_additional_info w S) = conflicting S\<close> and
  clauses_update_additional_info[simp]:
    \<open>clauses (update_additional_info w S) = clauses S\<close>
  using update_additional_info[of S] unfolding clauses_def
  by (subst (asm) state_prop; subst (asm) state_prop; auto; fail)+

lemma
  trail_update_weight_information[simp]:
    \<open>trail (update_weight_information w S) = trail S\<close> and
  init_clss_update_weight_information[simp]:
    \<open>init_clss (update_weight_information w S) = init_clss S\<close> and
  learned_clss_update_weight_information[simp]:
    \<open>learned_clss (update_weight_information w S) = learned_clss S\<close> and
  backtrack_lvl_update_weight_information[simp]:
    \<open>backtrack_lvl (update_weight_information w S) = backtrack_lvl S\<close> and
  conflicting_update_weight_information[simp]:
    \<open>conflicting (update_weight_information w S) = conflicting S\<close> and
  clauses_update_weight_information[simp]:
    \<open>clauses (update_weight_information w S) = clauses S\<close>
  using update_additional_info[of S] unfolding update_weight_information_def by auto

definition weight where
  \<open>weight S = fst (additional_info S)\<close>

lemma
  additional_info_update_additional_info[simp]:
  "additional_info (update_additional_info w S) = w"
  unfolding additional_info_def using update_additional_info[of S]
  by (cases \<open>state S\<close>; auto; fail)+

lemma
  weight_cons_trail[simp]: \<open>weight (cons_trail L S) = weight S\<close> and
  clss_tl_trail[simp]: "weight (tl_trail S) = weight S" and
  weight_add_learned_cls_unfolded:
    "weight (add_learned_cls U S) = weight S"
    and
  weight_update_conflicting[simp]: "weight (update_conflicting D S) = weight S" and
  weight_remove_cls[simp]:
    "weight (remove_cls C S) = weight S" and
  weight_add_learned_cls[simp]:
    "weight (add_learned_cls C S) = weight S" and
  weight_update_weight_information[simp]:
    "weight (update_weight_information M S) = Some (lit_of `# mset M)"
  by (auto simp: update_weight_information_def weight_def)

abbreviation \<rho>' where
  \<open>\<rho>' w \<equiv> (case w of None \<Rightarrow> \<infinity> | Some w \<Rightarrow> \<rho> w)\<close>

definition is_improving_int :: "('v, 'v clause) ann_lits \<Rightarrow> 'v clauses \<Rightarrow> 'v clause option \<Rightarrow> bool" where
  \<open>is_improving_int M N w \<longleftrightarrow> enat (\<rho> (lit_of `# mset M)) < \<rho>' w \<and> M \<Turnstile>asm N \<and> no_dup M
    \<and> lit_of `# mset M \<in> simple_clss (atms_of_mm N) \<and>
    total_over_m (lits_of_l M) (set_mset N)\<close>

text \<open>Pointwise negation of a clause:\<close>
definition pNeg :: "'a clause \<Rightarrow> 'a clause" where
  \<open>pNeg C = {#-D. D \<in># C#}\<close>

lemma finite_CNot[simp]: \<open>finite (CNot C)\<close>
  by (auto simp: CNot_def)

lemma atms_of_pNeg[simp]: \<open>atms_of (pNeg C) = atms_of C\<close>
  by (auto simp: pNeg_def atms_of_def image_image)

lemma distinct_mset_pNeg_iff[iff]: \<open>distinct_mset (pNeg x) \<longleftrightarrow>  distinct_mset x\<close>
  unfolding pNeg_def
  by (rule distinct_image_mset_inj) (auto simp: inj_on_def)

definition conflicting_clauses :: "'v clauses \<Rightarrow> 'v clause option \<Rightarrow> 'v clauses" where
  \<open>conflicting_clauses M w = {#pNeg C | C \<in># mset_set (simple_clss (atms_of_mm M)). \<rho> C \<ge> \<rho>' w#}\<close>

sublocale conflict_driven_clause_learning_with_adding_init_clause_cost\<^sub>W_no_state
  where
    state = state and
    trail = trail and
    init_clss = init_clss and
    learned_clss = learned_clss and
    conflicting = conflicting and
    cons_trail = cons_trail and
    tl_trail = tl_trail and
    add_learned_cls = add_learned_cls and
    remove_cls = remove_cls and
    update_conflicting = update_conflicting and
    init_state = init_state and
    weight = weight and
    update_weight_information = update_weight_information and
    is_improving_int = is_improving_int and
    conflicting_clauses = conflicting_clauses
  by unfold_locales

(* TODO change as definition of \<open>negate_ann_lits\<close> *)
lemma negate_ann_lits_pNeg_lit_of: \<open>negate_ann_lits = pNeg o image_mset lit_of o mset\<close>
  by (intro ext) (auto simp: negate_ann_lits_def pNeg_def)

lemma state_additional_info':
  \<open>state S = (trail S, init_clss S, learned_clss S, conflicting S, weight S, additional_info' S)\<close>
  unfolding additional_info'_def by (cases \<open>state S\<close>; auto simp: state_prop weight_def)

lemma state_update_weight_information:
  \<open>state S = (M, N, U, C, w, other) \<Longrightarrow>
    \<exists>w'. state (update_weight_information T S) = (M, N, U, C, w', other)\<close>
  unfolding update_weight_information_def by (cases \<open>state S\<close>; auto simp: state_prop weight_def)

lemma conflicting_clss_incl_init_clss: \<open>atms_of_mm (conflicting_clss S) \<subseteq> atms_of_mm (init_clss S)\<close>
  unfolding conflicting_clss_def conflicting_clauses_def
  apply (auto simp: simple_clss_finite)
  by (auto simp: simple_clss_def atms_of_ms_def)

lemma distinct_mset_mset_conflicting_clss: \<open>distinct_mset_mset (conflicting_clss S)\<close>
  unfolding conflicting_clss_def conflicting_clauses_def distinct_mset_set_def
  apply (auto simp: simple_clss_finite)
  by (auto simp: simple_clss_def)

lemma is_improving_conflicting_clss_update_weight_information: \<open>is_improving M S \<Longrightarrow>
       conflicting_clss S \<subseteq># conflicting_clss (update_weight_information M S)\<close>
  by (cases \<open>weight S\<close>) (auto simp: is_improving_int_def conflicting_clss_def conflicting_clauses_def
      simp: multiset_filter_mono2 le_less intro!: image_mset_subseteq_mono
      split: enat.splits)

 lemma conflicting_clss_update_weight_information_in:
  assumes \<open>is_improving M S\<close>
  shows \<open>negate_ann_lits M \<in># conflicting_clss (update_weight_information M S)\<close>
   using assms apply (auto simp: simple_clss_finite
    conflicting_clauses_def conflicting_clss_def is_improving_int_def)
  by (auto simp: is_improving_int_def conflicting_clss_def conflicting_clauses_def
      simp: multiset_filter_mono2 simple_clss_def
      negate_ann_lits_pNeg_lit_of)

lemma atms_of_ms_pNeg[simp]: \<open>atms_of_ms (pNeg ` N) = atms_of_ms N\<close>
  unfolding atms_of_ms_def pNeg_def by (auto simp: image_image atms_of_def)

lemma atms_of_init_clss_conflicting_clss[simp]:
  \<open>atms_of_mm (init_clss S) \<union> atms_of_mm (conflicting_clss S) = atms_of_mm (init_clss S)\<close>
  using conflicting_clss_incl_init_clss[of S] by blast

lemma lit_of_trail_in_simple_clss: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S) \<Longrightarrow>
         lit_of `# mset (trail S) \<in> simple_clss (atms_of_mm (init_clss S))\<close>
  unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def abs_state_def
  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def cdcl\<^sub>W_restart_mset.no_strange_atm_def
  by (auto simp: simple_clss_def cdcl\<^sub>W_restart_mset_state atms_of_def pNeg_def lits_of_def
      dest: no_dup_not_tautology no_dup_distinct)

lemma pNeg_lit_of_trail_in_simple_clss: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S) \<Longrightarrow>
         pNeg (lit_of `# mset (trail S)) \<in> simple_clss (atms_of_mm (init_clss S))\<close>
  unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def abs_state_def
  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def cdcl\<^sub>W_restart_mset.no_strange_atm_def
  by (auto simp: simple_clss_def cdcl\<^sub>W_restart_mset_state atms_of_def pNeg_def lits_of_def
      dest: no_dup_not_tautology_uminus no_dup_distinct_uminus)

lemma is_improving_mono:
  \<open>\<not> is_improving M' S \<Longrightarrow>
       is_improving M S \<Longrightarrow>
       \<not> is_improving M' (update_weight_information M S)\<close>
  by (cases \<open>weight S\<close>) (auto simp: is_improving_int_def)

sublocale conflict_driven_clause_learning_with_adding_init_clause_cost\<^sub>W_ops
  where
    state = state and
    trail = trail and
    init_clss = init_clss and
    learned_clss = learned_clss and
    conflicting = conflicting and
    cons_trail = cons_trail and
    tl_trail = tl_trail and
    add_learned_cls = add_learned_cls and
    remove_cls = remove_cls and
    update_conflicting = update_conflicting and
    init_state = init_state and
    weight = weight and
    update_weight_information = update_weight_information and
    is_improving_int = is_improving_int and
    conflicting_clauses = conflicting_clauses
  apply unfold_locales
  subgoal by (rule state_additional_info'; assumption)
  subgoal by (rule state_update_weight_information; assumption)
  subgoal by (rule conflicting_clss_incl_init_clss; assumption)
  subgoal by (rule distinct_mset_mset_conflicting_clss; assumption)
  subgoal by (rule is_improving_conflicting_clss_update_weight_information; assumption)
  subgoal by (rule conflicting_clss_update_weight_information_in; assumption)
  subgoal by (rule is_improving_mono; assumption)
  done

lemma wf_cdcl_opt: \<open>wf {(T, S). cdcl\<^sub>W_all_struct_inv S \<and> cdcl_opt S T}\<close>
  apply (rule wf_cdcl_opt[of \<rho>' \<open>{(j, i). j < i}\<close>])
  subgoal for S T
    by (cases \<open>weight S\<close>; cases \<open>weight T\<close>)
      (auto simp: improve.simps is_improving_int_def
        split: enat.splits)
  subgoal by (simp add: wf)
  done

lemma no_step_cdcl_opt_stgy_empty_conflict:
  assumes
    n_s: \<open>no_step cdcl_opt S\<close> and
    all_struct: \<open>cdcl\<^sub>W_all_struct_inv S\<close> and
    stgy_inv: \<open>cdcl_opt_stgy_inv S\<close>
  shows \<open>conflicting S = Some {#}\<close>
proof (rule no_step_cdcl_opt_stgy_empty_conflict[OF _ assms])
  fix S
  assume
    ent: \<open>trail S \<Turnstile>asm clauses S\<close> and
    total: \<open>total_over_m (lits_of_l (trail S)) (set_mset (clauses S))\<close> and
    n_s: \<open>no_step conflict_opt S\<close> and
    confl: \<open>conflicting S = None\<close> and
    all_struct: \<open>cdcl\<^sub>W_all_struct_inv S\<close>

  have H: \<open>(lit_of `# mset (trail S)) \<in># mset_set (simple_clss (atms_of_mm (init_clss S)))\<close>
    \<open>(lit_of `# mset (trail S)) \<in> (simple_clss (atms_of_mm (init_clss S)))\<close>
    \<open>no_dup (trail S)\<close>
    apply (subst finite_set_mset_mset_set[OF simple_clss_finite])
    using all_struct by (auto simp: simple_clss_def  cdcl\<^sub>W_all_struct_inv_def
        no_strange_atm_def atms_of_def lits_of_def image_image
        cdcl\<^sub>W_M_level_inv_def clauses_def
      dest: no_dup_not_tautology no_dup_distinct)
  then have \<open>enat (\<rho> (lit_of `# mset (trail S))) < \<rho>' (weight S)\<close>
    using n_s confl
    by (auto simp: conflict_opt.simps conflicting_clss_def
       conflicting_clauses_def clauses_def negate_ann_lits_pNeg_lit_of image_iff
       dest: spec[of _ \<open>(lit_of `# mset (trail S))\<close>])
  moreover have \<open>trail S \<Turnstile>asm init_clss S\<close>
    using ent by (auto simp: clauses_def)
  moreover have \<open>total_over_m (lits_of_l (trail S))  (set_mset (init_clss S))\<close>
    using total all_struct by (auto simp: total_over_m_def total_over_set_def
       cdcl\<^sub>W_all_struct_inv_def clauses_def
        no_strange_atm_def)
  moreover have \<open>optimal_improve (trail S) S\<close>
    using total all_struct \<open>no_dup (trail S)\<close>
    apply (cases \<open>lit_of (hd (trail S))\<close>)
    apply (auto simp: optimal_improve_def is_improving_int_def image_image
        total_over_m_def total_over_set_def neq_Nil_conv cdcl\<^sub>W_all_struct_inv_def lits_of_def
        no_strange_atm_def defined_lit_map clauses_def
      intro!: bexI[of _ \<open> atm_of (lit_of (hd (trail S)))\<close>])
    apply (metis UnCI image_eqI literal.sel(2))
    by (metis UnCI image_eqI literal.sel(1))
  ultimately show \<open>Ex (improve S)\<close>
    using improve.intros[of S \<open>[]\<close> \<open>trail S\<close> \<open>update_weight_information (trail S) S\<close>] total H confl
    by (auto simp: is_improving_int_def)
qed

end

end
