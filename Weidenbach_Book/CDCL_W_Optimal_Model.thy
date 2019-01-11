theory CDCL_W_Optimal_Model
imports CDCL_W_Abstract_State "HOL-Library.Extended_Nat"
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


However, the optimal model is $Q$.
}
\<close>

text \<open>The idea of the proof (explained of the example of the optimising CDCL) is the following:
  \<^enum> We start with a calculus OCDCL on \<^term>\<open>(M, N, U, D, Op)\<close>.
  \<^enum> This extended to a state  \<^term>\<open>(M, N +  all_models_of_higher_cost, U, D, Op)\<close>.
  \<^enum> Each transition step of OCDCL is mapped to a step in CDCL over the abstract state. The
    abstract set of clauses might be unsatisfiable, but we only use it to prove the invariants on
    the state. Only adding clause cannot be mapped to a transition over the abstract state, but adding clauses
    does not break the invariants (as long as the additional clauses do not contain duplicate literals).
  \<^enum> The last proofs are done over CDCLopt.

We abstract about how the optimisation is done in the locale below: We define a calculus \<^term>\<open>cdcl_bab\<close>
(for branch-and-bounds). It is parametrised by how the conflicting clauses are generated and the improvement
criterion.

We later instantiate it with the optimisation calculus from Weidenbach's book.
\<close>

definition negate_ann_lits :: "('v, 'v clause) ann_lits \<Rightarrow> 'v literal multiset" where
  \<open>negate_ann_lits M = (\<lambda>L. - lit_of L) `# (mset M)\<close>

text \<open>Pointwise negation of a clause:\<close>
definition pNeg :: \<open>'v clause \<Rightarrow> 'v clause\<close> where
  \<open>pNeg C = {#-D. D \<in># C#}\<close>

lemma atms_of_pNeg[simp]: \<open>atms_of (pNeg C) = atms_of C\<close>
  by (auto simp: pNeg_def atms_of_def image_image)

lemma negate_ann_lits_pNeg_lit_of: \<open>negate_ann_lits = pNeg o image_mset lit_of o mset\<close>
  by (intro ext) (auto simp: negate_ann_lits_def pNeg_def)

lemma negate_ann_lits_empty_iff: \<open>negate_ann_lits M \<noteq> {#} \<longleftrightarrow> M \<noteq> []\<close>
  by (auto simp: negate_ann_lits_def)

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

lemma exists_lit_max_level_in_negate_ann_lits:
  \<open>negate_ann_lits M \<noteq> {#} \<Longrightarrow> \<exists>L\<in>#negate_ann_lits M. get_level M L = count_decided M\<close>
  by (cases \<open>M\<close>) (auto simp: negate_ann_lits_def)


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
         \<not>is_improving M' (update_weight_information M S)\<close> and
    conflicting_clss_update_weight_information_no_alien:
      \<open>atms_of_mm (conflicting_clss (update_weight_information M S)) \<subseteq> atms_of_mm (init_clss S)\<close>

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

text \<open>We use a slighlty generalised form of backtrack to make conflict clause minimisation possible.\<close>
inductive obacktrack :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
obacktrack_rule: "
  conflicting S = Some (add_mset L D) \<Longrightarrow>
  (Decided K # M1, M2) \<in> set (get_all_ann_decomposition (trail S)) \<Longrightarrow>
  get_level (trail S) L = backtrack_lvl S \<Longrightarrow>
  get_level (trail S) L = get_maximum_level (trail S) (add_mset L D') \<Longrightarrow>
  get_maximum_level (trail S) D' \<equiv> i \<Longrightarrow>
  get_level (trail S) K = i + 1 \<Longrightarrow>
  D' \<subseteq># D \<Longrightarrow>
  clauses S + conflicting_clss S \<Turnstile>pm add_mset L D' \<Longrightarrow>
  T \<sim> cons_trail (Propagated L (add_mset L D'))
        (reduce_trail_to M1
          (add_learned_cls (add_mset L D')
            (update_conflicting None S))) \<Longrightarrow>
  obacktrack S T"

inductive_cases obacktrackE: \<open>obacktrack S T\<close>

inductive ocdcl\<^sub>W_bj :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
skip: "skip S S' \<Longrightarrow> ocdcl\<^sub>W_bj S S'" |
resolve: "resolve S S' \<Longrightarrow> ocdcl\<^sub>W_bj S S'" |
backtrack: "obacktrack S S' \<Longrightarrow> ocdcl\<^sub>W_bj S S'"

inductive_cases cdcl\<^sub>W_bjE: "cdcl\<^sub>W_bj S T"

inductive ocdcl\<^sub>W_o :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
decide: "decide S S' \<Longrightarrow> ocdcl\<^sub>W_o S S'" |
bj: "ocdcl\<^sub>W_bj S S' \<Longrightarrow> ocdcl\<^sub>W_o S S'"

inductive cdcl_bab :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> for S :: 'st where
cdcl_conflict: "conflict S S' \<Longrightarrow> cdcl_bab S S'" |
cdcl_propagate: "propagate S S' \<Longrightarrow> cdcl_bab S S'" |
cdcl_improve: "improve S S' \<Longrightarrow> cdcl_bab S S'" |
cdcl_conflict_opt: "conflict_opt S S' \<Longrightarrow> cdcl_bab S S'" |
cdcl_other': "ocdcl\<^sub>W_o S S' \<Longrightarrow> cdcl_bab S S'"

inductive cdcl_bab_stgy :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> for S :: 'st where
cdcl_bab_conflict: "conflict S S' \<Longrightarrow> cdcl_bab_stgy S S'" |
cdcl_bab_propagate: "propagate S S' \<Longrightarrow> cdcl_bab_stgy S S'" |
cdcl_bab_improve: "improve S S' \<Longrightarrow> cdcl_bab_stgy S S'" |
cdcl_bab_conflict_opt: "conflict_opt S S' \<Longrightarrow> cdcl_bab_stgy S S'" |
cdcl_bab_other': "ocdcl\<^sub>W_o S S' \<Longrightarrow> no_confl_prop_impr S \<Longrightarrow> cdcl_bab_stgy S S'"

inductive_cases ocdcl\<^sub>W_bjE: \<open>ocdcl\<^sub>W_bj S T\<close>

lemma ocdcl\<^sub>W_o_induct[consumes 1, case_names decide skip resolve backtrack]:
  fixes S :: "'st"
  assumes cdcl\<^sub>W_restart: "ocdcl\<^sub>W_o S T" and
    decideH: "\<And>L T. conflicting S = None \<Longrightarrow> undefined_lit (trail S) L  \<Longrightarrow>
      atm_of L \<in> atms_of_mm (init_clss S) \<Longrightarrow>
      T \<sim> cons_trail (Decided L) S \<Longrightarrow>
      P S T" and
    skipH: "\<And>L C' M E T.
      trail S = Propagated L C' # M \<Longrightarrow>
      conflicting S = Some E \<Longrightarrow>
      -L \<notin># E \<Longrightarrow> E \<noteq> {#} \<Longrightarrow>
      T \<sim> tl_trail S \<Longrightarrow>
      P S T" and
    resolveH: "\<And>L E M D T.
      trail S = Propagated L E # M \<Longrightarrow>
      L \<in># E \<Longrightarrow>
      hd_trail S = Propagated L E \<Longrightarrow>
      conflicting S = Some D \<Longrightarrow>
      -L \<in># D \<Longrightarrow>
      get_maximum_level (trail S) ((remove1_mset (-L) D)) = backtrack_lvl S \<Longrightarrow>
      T \<sim> update_conflicting
        (Some (resolve_cls L D E)) (tl_trail S) \<Longrightarrow>
      P S T" and
    backtrackH: "\<And>L D K i M1 M2 T D'.
      conflicting S = Some (add_mset L D) \<Longrightarrow>
      (Decided K # M1, M2) \<in> set (get_all_ann_decomposition (trail S)) \<Longrightarrow>
      get_level (trail S) L = backtrack_lvl S \<Longrightarrow>
      get_level (trail S) L = get_maximum_level (trail S) (add_mset L D') \<Longrightarrow>
      get_maximum_level (trail S) D' \<equiv> i \<Longrightarrow>
      get_level (trail S) K = i+1 \<Longrightarrow>
      D' \<subseteq># D \<Longrightarrow>
      clauses S + conflicting_clss S \<Turnstile>pm add_mset L D' \<Longrightarrow>
      T \<sim> cons_trail (Propagated L (add_mset L D'))
            (reduce_trail_to M1
              (add_learned_cls (add_mset L D')
                (update_conflicting None S))) \<Longrightarrow>
       P S T"
  shows "P S T"
  using cdcl\<^sub>W_restart apply (induct T rule: ocdcl\<^sub>W_o.induct)
  subgoal using assms(2) by (auto elim: decideE; fail)
  subgoal apply (elim ocdcl\<^sub>W_bjE skipE resolveE obacktrackE)
    apply (frule skipH; simp; fail)
    apply (cases "trail S"; auto elim!: resolveE intro!: resolveH; fail)
    apply (frule backtrackH; simp; fail)
    done
  done

lemma cdcl_bab_no_more_init_clss:
  \<open>cdcl_bab S S' \<Longrightarrow> init_clss S = init_clss S'\<close>
  by (induction rule: cdcl_bab.cases)
    (auto simp: improve.simps optimal_improve_def conflict.simps propagate.simps
      conflict_opt.simps ocdcl\<^sub>W_o.simps obacktrack.simps skip.simps resolve.simps ocdcl\<^sub>W_bj.simps
      decide.simps)

lemma rtranclp_cdcl_bab_no_more_init_clss:
  \<open>cdcl_bab\<^sup>*\<^sup>* S S' \<Longrightarrow> init_clss S = init_clss S'\<close>
  by (induction rule: rtranclp_induct)
    (auto dest: cdcl_bab_no_more_init_clss)

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
  \<open>obacktrack S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.backtrack (abs_state S) (abs_state T)\<close>
proof (induction rule: obacktrack.cases)
  case (obacktrack_rule L D K M1 M2 D' i T)
  have H: \<open>set_mset (init_clss S) \<union> set_mset (learned_clss S)
    \<subseteq> set_mset (init_clss S) \<union> set_mset (conflicting_clss S) \<union> set_mset (learned_clss S)\<close>
    by auto
  have [simp]: \<open>cdcl\<^sub>W_restart_mset.reduce_trail_to M1
       (trail S, init_clss S + conflicting_clss S, add_mset D (learned_clss S), None) =
    (M1, init_clss S + conflicting_clss S, add_mset D (learned_clss S), None)\<close> for D
    using obacktrack_rule by (auto simp add: cdcl\<^sub>W_restart_mset_reduce_trail_to
        cdcl\<^sub>W_restart_mset_state)
  show ?case
    using obacktrack_rule
    by (auto intro!: cdcl\<^sub>W_restart_mset.backtrack.intros
        simp: cdcl\<^sub>W_restart_mset_state abs_state_def clauses_def cdcl\<^sub>W_restart_mset.clauses_def
	  ac_simps)
qed

lemma ocdcl\<^sub>W_o_all_rules_induct[consumes 1, case_names decide backtrack skip resolve]:
  fixes S T :: 'st
  assumes
    "ocdcl\<^sub>W_o S T" and
    "\<And>T. decide S T \<Longrightarrow> P S T" and
    "\<And>T. obacktrack S T \<Longrightarrow> P S T" and
    "\<And>T. skip S T \<Longrightarrow> P S T" and
    "\<And>T. resolve S T \<Longrightarrow> P S T"
  shows "P S T"
  using assms by (induct T rule: ocdcl\<^sub>W_o.induct) (auto simp: ocdcl\<^sub>W_bj.simps)

lemma cdcl\<^sub>W_o_cdcl\<^sub>W_o:
  \<open>ocdcl\<^sub>W_o S S' \<Longrightarrow> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o (abs_state S) (abs_state S')\<close>
  apply (induction rule: ocdcl\<^sub>W_o_all_rules_induct)
     apply (simp add: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o.simps decide_decide; fail)
    apply (blast dest: backtrack_backtrack)
   apply (blast dest: skip_skip)
  by (blast dest: resolve_resolve)

lemma cdcl_bab_stgy_all_struct_inv:
  assumes \<open>cdcl_bab S T\<close> and \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state T)\<close>
  using assms
proof (induction rule: cdcl_bab.cases)
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

lemma rtranclp_cdcl_bab_stgy_all_struct_inv:
  assumes \<open>cdcl_bab\<^sup>*\<^sup>* S T\<close> and \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state T)\<close>
  using assms by induction (auto dest: cdcl_bab_stgy_all_struct_inv)

definition cdcl_bab_struct_invs :: \<open>'st \<Rightarrow> bool\<close> where
\<open>cdcl_bab_struct_invs S \<longleftrightarrow>
   atms_of_mm (conflicting_clss S) \<subseteq> atms_of_mm (init_clss S)\<close>

lemma cdcl_bab_cdcl_bab_struct_invs:
  \<open>cdcl_bab S T \<Longrightarrow> cdcl_bab_struct_invs S \<Longrightarrow> cdcl_bab_struct_invs T\<close>
  using conflicting_clss_update_weight_information_no_alien[of _ S] apply -
  by (induction rule: cdcl_bab.induct)
    (force simp: improve.simps optimal_improve_def conflict.simps propagate.simps
           conflict_opt.simps ocdcl\<^sub>W_o.simps obacktrack.simps skip.simps resolve.simps ocdcl\<^sub>W_bj.simps
           decide.simps cdcl_bab_struct_invs_def)+

lemma rtranclp_cdcl_bab_cdcl_bab_struct_invs:
  \<open>cdcl_bab\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl_bab_struct_invs S \<Longrightarrow> cdcl_bab_struct_invs T\<close>
  by (induction rule: rtranclp_induct) (auto dest: cdcl_bab_cdcl_bab_struct_invs)


lemma cdcl_bab_stgy_cdcl_bab: \<open>cdcl_bab_stgy S T \<Longrightarrow> cdcl_bab S T\<close>
  by (auto simp: cdcl_bab_stgy.simps intro: cdcl_bab.intros)

lemma rtranclp_cdcl_bab_stgy_cdcl_bab: \<open>cdcl_bab_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl_bab\<^sup>*\<^sup>* S T\<close>
  by (induction rule: rtranclp_induct)
   (auto dest: cdcl_bab_stgy_cdcl_bab)

text \<open>The following does \<^emph>\<open>not\<close> hold, because we cannot guarantee the absence of conflict of
  smaller level after \<^term>\<open>improve\<close> and \<^term>\<open>conflict_opt\<close>.\<close>
lemma cdcl_bab_all_stgy_inv:
  assumes \<open>cdcl_bab S T\<close> and \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> and
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

lemma (in conflict_driven_clause_learning\<^sub>W) cdcl\<^sub>W_o_conflict_is_false_with_level_inv_all_inv:
  assumes
    \<open>cdcl\<^sub>W_o S T\<close>
    \<open>cdcl\<^sub>W_all_struct_inv S\<close>
    \<open>conflict_is_false_with_level S\<close>
  shows \<open>conflict_is_false_with_level T\<close>
  by (rule cdcl\<^sub>W_o_conflict_is_false_with_level_inv)
    (use assms in \<open>auto simp: cdcl\<^sub>W_all_struct_inv_def\<close>)

declare cdcl\<^sub>W_restart_mset.conflict_is_false_with_level_def [simp del]

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

lemma obacktrack_state_eq_compatible:
  assumes
    bt: "obacktrack S T" and
    SS': "S \<sim> S'" and
    TT': "T \<sim> T'"
  shows "obacktrack S' T'"
proof -
  obtain D L K i M1 M2 D' where
    conf: "conflicting S = Some (add_mset L D)" and
    decomp: "(Decided K # M1, M2) \<in> set (get_all_ann_decomposition (trail S))" and
    lev: "get_level (trail S) L = backtrack_lvl S" and
    max: "get_level (trail S) L = get_maximum_level (trail S) (add_mset L D')" and
    max_D: "get_maximum_level (trail S) D' \<equiv> i" and
    lev_K: "get_level (trail S) K = Suc i" and
    D'_D: \<open>D' \<subseteq># D\<close> and
    NU_DL: \<open>clauses S + conflicting_clss S \<Turnstile>pm add_mset L D'\<close> and
    T: "T \<sim> cons_trail (Propagated L (add_mset L D'))
                (reduce_trail_to M1
                  (add_learned_cls (add_mset L D')
                    (update_conflicting None S)))"
    using bt by (elim obacktrackE) force
  let ?D = \<open>add_mset L D\<close>
  let ?D' = \<open>add_mset L D'\<close>
  have D': "conflicting S' = Some ?D"
    using SS' conf by (cases "conflicting S'") auto

  have T'_S: "T' \<sim> cons_trail (Propagated L ?D')
     (reduce_trail_to M1 (add_learned_cls ?D'
     (update_conflicting None S)))"
    using T TT' state_eq_sym state_eq_trans by blast
  have T': "T' \<sim> cons_trail (Propagated L ?D')
     (reduce_trail_to M1 (add_learned_cls ?D'
     (update_conflicting None S')))"
    apply (rule state_eq_trans[OF T'_S])
    by (auto simp: cons_trail_state_eq reduce_trail_to_state_eq add_learned_cls_state_eq
        update_conflicting_state_eq SS')
  show ?thesis
    apply (rule obacktrack_rule[of _ L D K M1 M2 D' i])
    subgoal by (rule D')
    subgoal using TT' decomp SS' by auto
    subgoal using lev TT'  SS' by auto
    subgoal using max TT' SS' by auto
    subgoal using max_D TT' SS' by auto
    subgoal using lev_K TT' SS' by auto
    subgoal by (rule D'_D)
    subgoal using NU_DL TT' SS' by auto
    subgoal by (rule T')
    done
qed

lemma ocdcl\<^sub>W_o_no_smaller_confl_inv:
  fixes S S' :: "'st"
  assumes
    "ocdcl\<^sub>W_o S S'" and
    n_s: "no_step conflict S" and
    lev: "cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)" and
    max_lev: "conflict_is_false_with_level S" and
    smaller: "no_smaller_confl S"
  shows "no_smaller_confl S'"
  using assms(1,2) unfolding no_smaller_confl_def
proof (induct rule: ocdcl\<^sub>W_o_induct)
  case (decide L T) note confl = this(1) and undef = this(2) and T = this(4)
  have [simp]: "clauses T = clauses S"
    using T undef by auto
  show ?case
  proof (intro allI impI)
    fix M'' K M' Da
    assume "trail T = M'' @ Decided K # M'" and D: "Da \<in># local.clauses T"
    then have "trail S = tl M'' @ Decided K # M'
        \<or> (M'' = [] \<and> Decided K # M' = Decided L # trail S)"
      using T undef by (cases M'') auto
    moreover {
      assume "trail S = tl M'' @ Decided K # M'"
      then have "\<not>M' \<Turnstile>as CNot Da"
        using D T undef confl smaller unfolding no_smaller_confl_def smaller by fastforce
    }
    moreover {
      assume "Decided K # M' = Decided L # trail S"
      then have "\<not>M' \<Turnstile>as CNot Da" using smaller D confl T n_s by (auto simp: conflict.simps)
    }
    ultimately show "\<not>M' \<Turnstile>as CNot Da" by fast
  qed
next
  case resolve
  then show ?case using smaller max_lev unfolding no_smaller_confl_def by auto
next
  case skip
  then show ?case using smaller max_lev unfolding no_smaller_confl_def by auto
next
  case (backtrack L D K i M1 M2 T D') note confl = this(1) and decomp = this(2) and
    T = this(9)
  obtain c where M: "trail S = c @ M2 @ Decided K # M1"
    using decomp by auto

  show ?case
  proof (intro allI impI)
    fix M ia K' M' Da
    assume "trail T = M' @ Decided K' # M"
    then have "M1 = tl M' @ Decided K' # M"
      using T decomp lev by (cases M') (auto simp: cdcl\<^sub>W_M_level_inv_decomp)
    let ?D' = \<open>add_mset L D'\<close>
    let ?S' = "(cons_trail (Propagated L ?D')
                  (reduce_trail_to M1 (add_learned_cls ?D' (update_conflicting None S))))"
    assume D: "Da \<in># clauses T"
    moreover{
      assume "Da \<in># clauses S"
      then have "\<not>M \<Turnstile>as CNot Da" using \<open>M1 = tl M' @ Decided K' # M\<close> M confl smaller
        unfolding no_smaller_confl_def by auto
    }
    moreover {
      assume Da: "Da = add_mset L D'"
      have "\<not>M \<Turnstile>as CNot Da"
      proof (rule ccontr)
        assume "\<not> ?thesis"
        then have "-L \<in> lits_of_l M"
          unfolding Da by (simp add: in_CNot_implies_uminus(2))
        then have "-L \<in> lits_of_l (Propagated L D # M1)"
          using UnI2 \<open>M1 = tl M' @ Decided K' # M\<close>
          by auto
        moreover {
	  have "obacktrack S ?S'"
            using obacktrack_rule[OF backtrack.hyps(1-8) T] obacktrack_state_eq_compatible[of S T S] T
            by force
	  then have \<open>cdcl_bab S ?S'\<close>
	    by (auto dest!: ocdcl\<^sub>W_bj.intros ocdcl\<^sub>W_o.intros intro: cdcl_bab.intros)
	  then have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state ?S')\<close>
	    using cdcl_bab_stgy_all_struct_inv[of S, OF _ lev] by fast
          then have "cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (abs_state ?S')"
            by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
          then have "no_dup (Propagated L D # M1)"
            using decomp lev unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by auto
	}
        ultimately show False
          using Decided_Propagated_in_iff_in_lits_of_l defined_lit_map
          by (auto simp: no_dup_def)
      qed
    }
    ultimately show "\<not>M \<Turnstile>as CNot Da"
      using T decomp lev unfolding cdcl\<^sub>W_M_level_inv_def by fastforce
  qed
qed

lemma cdcl_bab_stgy_no_smaller_confl:
  assumes \<open>cdcl_bab_stgy S T\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> and
    \<open>no_smaller_confl S\<close> and
    \<open>conflict_is_false_with_level S\<close> and
    \<open>no_smaller_improve S\<close>
  shows \<open>no_smaller_confl T\<close>
  using assms
proof (induction rule: cdcl_bab_stgy.cases)
  case (cdcl_bab_conflict S')
  then show ?case
    using conflict_no_smaller_confl_inv by blast
next
  case (cdcl_bab_propagate S')
  then show ?case
    using propagate_no_smaller_confl_inv by blast
next
  case (cdcl_bab_improve S')
  then show ?case
    by (auto simp: no_smaller_confl_def no_smaller_improve_def improve.simps)
next
  case (cdcl_bab_conflict_opt S')
  then show ?case
    by (auto simp: no_smaller_confl_def conflict_opt.simps)
next
  case (cdcl_bab_other' S')
  show ?case
    apply (rule ocdcl\<^sub>W_o_no_smaller_confl_inv)
    using cdcl_bab_other' by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
qed

lemma ocdcl\<^sub>W_o_conflict_is_false_with_level_inv:
  assumes
    "ocdcl\<^sub>W_o S S'" and
    lev: "cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)" and
    confl_inv: "conflict_is_false_with_level S"
  shows "conflict_is_false_with_level S'"
  using assms(1,2)
proof (induct rule: ocdcl\<^sub>W_o_induct)
  case (resolve L C M D T) note tr_S = this(1) and confl = this(4) and LD = this(5) and T = this(7)
  have n_d: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (abs_state S)\<close> and
    conflicting: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (abs_state S)\<close>
    using lev unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by auto
  have uL_not_D: "-L \<notin># remove1_mset (-L) D"
    using n_d confl unfolding cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
    by (cases \<open>-L \<in># D\<close>)
      (auto simp: abs_state_def conflicting.simps
        dest!: multi_member_split)
  moreover {
    have L_not_D: "L \<notin># remove1_mset (-L) D"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then have "L \<in># D"
        by (auto simp: in_remove1_mset_neq)
      moreover have "Propagated L C # M \<Turnstile>as CNot D"
        using conflicting confl tr_S unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
	by (auto simp: abs_state_def conflicting.simps trail.simps)
      ultimately have "-L \<in> lits_of_l (Propagated L C # M)"
        using in_CNot_implies_uminus(2) by blast
      moreover have "no_dup (Propagated L C # M)"
        using lev tr_S unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
	  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by auto
      ultimately show False unfolding lits_of_def
        by (metis imageI insertCI list.simps(15) lit_of.simps(2) lits_of_def no_dup_consistentD)
    qed
  }
  ultimately have g_D: "get_maximum_level (Propagated L C # M) (remove1_mset (-L) D)
      = get_maximum_level M (remove1_mset (-L) D)"
    by (simp add: atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set atms_of_def)
  have lev_L[simp]: "get_level M L = 0"
    using lev unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def tr_S
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      by (auto simp: lits_of_def tr_S)

  have D: "get_maximum_level M (remove1_mset (-L) D) = backtrack_lvl S"
    using resolve.hyps(6) LD unfolding tr_S by (auto simp: get_maximum_level_plus max_def g_D)
  have "get_maximum_level M (remove1_mset L C) \<le> backtrack_lvl S"
    using count_decided_ge_get_maximum_level[of M] lev unfolding tr_S cdcl\<^sub>W_M_level_inv_def by auto
  then have
    "get_maximum_level M (remove1_mset (- L) D \<union># remove1_mset L C) = backtrack_lvl S"
    by (auto simp: get_maximum_level_union_mset get_maximum_level_plus max_def D)
  then show ?case
    using tr_S get_maximum_level_exists_lit_of_max_level[of
      "remove1_mset (- L) D \<union># remove1_mset L C" M] T
    by (auto simp: conflict_is_false_with_level_def)
next
  case (skip L C' M D T) note tr_S = this(1) and D = this(2) and T = this(5)
  then obtain La where
    "La \<in># D" and
    "get_level (Propagated L C' # M) La = backtrack_lvl S"
    using skip confl_inv by (auto simp: conflict_is_false_with_level_def)
  moreover {
    have "atm_of La \<noteq> atm_of L"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then have La: "La = L" using \<open>La \<in># D\<close> \<open>- L \<notin># D\<close>
        by (auto simp add: atm_of_eq_atm_of)
      have n_d: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (abs_state S)\<close> and
        conflicting: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (abs_state S)\<close>
        using lev unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
        by auto
      have "Propagated L C' # M \<Turnstile>as CNot D"
        using conflicting tr_S D unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
	by (auto simp: abs_state_def conflicting.simps trail.simps)
      then have "-L \<in> lits_of_l M"
        using \<open>La \<in># D\<close> in_CNot_implies_uminus(2)[of L D "Propagated L C' # M"] unfolding La
        by auto
      then show False using lev tr_S unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def consistent_interp_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
        by (auto simp: conflict_is_false_with_level_def)
    qed
    then have "get_level (Propagated L C' # M) La = get_level M La" by auto
  }
  ultimately show ?case using D tr_S T by (auto simp: conflict_is_false_with_level_def)
next
  case backtrack
  then show ?case
    by (auto split: if_split_asm simp: cdcl\<^sub>W_M_level_inv_decomp lev conflict_is_false_with_level_def)
qed (auto simp: conflict_is_false_with_level_def)


lemma cdcl_bab_stgy_conflict_is_false_with_level:
  assumes \<open>cdcl_bab_stgy S T\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> and
    \<open>no_smaller_confl S\<close> and
    \<open>conflict_is_false_with_level S\<close> and
    \<open>no_smaller_improve S\<close>
  shows \<open>conflict_is_false_with_level T\<close>
  using assms
proof (induction rule: cdcl_bab_stgy.cases)
  case (cdcl_bab_conflict S')
  then show ?case
    using conflict_conflict_is_false_with_level
    by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
next
  case (cdcl_bab_propagate S')
  then show ?case
    using propagate_conflict_is_false_with_level
    by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
next
  case (cdcl_bab_improve S')
  then show ?case
    using improve_conflict_is_false_with_level by blast
next
  case (cdcl_bab_conflict_opt S')
  then show ?case
    using conflict_opt_no_smaller_conflict(2) by blast
next
  case (cdcl_bab_other' S')
  show ?case
    apply (rule ocdcl\<^sub>W_o_conflict_is_false_with_level_inv)
    using cdcl_bab_other' by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
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

lemma cdcl_bab_stgy_no_smaller_improve:
  assumes \<open>cdcl_bab_stgy S T\<close> and
    \<open>no_smaller_improve S\<close> and
    struct_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close>
  shows \<open>no_smaller_improve T\<close>
  using assms
proof induction
  case (cdcl_bab_conflict S')
  then show ?case
    by (auto simp: no_smaller_improve_def elim!: conflictE)
next
  case (cdcl_bab_propagate S')
  then show ?case
    by (auto simp: no_smaller_improve_def propagated_cons_eq_append_decide_cons
        elim!: propagateE)
next
  case (cdcl_bab_improve S')
  then show ?case
    using is_improving_mono[of _ S]
    by (auto simp: no_smaller_improve_def improve.simps)
next
  case (cdcl_bab_conflict_opt S')
  then show ?case
    unfolding conflict_opt.simps no_smaller_improve_def by auto
next
  case (cdcl_bab_other' S') note o = this(1) and no_confl = this(2) and no_impr = this(3)
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
      apply (induction rule: ocdcl\<^sub>W_bj.cases)
      subgoal
        apply (cases \<open>trail S\<close>)
        using no_impr
        unfolding ocdcl\<^sub>W_o.simps no_smaller_improve_def decide.simps
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
            propagated_cons_eq_append_decide_cons elim!: skipE resolveE obacktrackE cdcl\<^sub>W_bjE)
        done
      done
  qed
qed

definition cdcl_bab_stgy_inv :: "'st \<Rightarrow> bool" where
  \<open>cdcl_bab_stgy_inv S \<longleftrightarrow> conflict_is_false_with_level S \<and> no_smaller_confl S \<and> no_smaller_improve S\<close>

lemma cdcl_bab_stgy_stgy_inv:
  \<open>cdcl_bab_stgy S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S) \<Longrightarrow>
    cdcl_bab_stgy_inv S \<Longrightarrow> cdcl_bab_stgy_inv T\<close>
  unfolding cdcl_bab_stgy_inv_def
  using cdcl_bab_stgy_conflict_is_false_with_level cdcl_bab_stgy_no_smaller_confl
    cdcl_bab_stgy_no_smaller_improve by blast

lemma rtranclp_cdcl_bab_stgy_stgy_inv:
  \<open>cdcl_bab_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S) \<Longrightarrow>
    cdcl_bab_stgy_inv S \<Longrightarrow> cdcl_bab_stgy_inv T\<close>
  apply (induction rule: rtranclp_induct)
  subgoal by auto
  subgoal for T U
    using cdcl_bab_stgy_stgy_inv rtranclp_cdcl_bab_stgy_all_struct_inv
      rtranclp_cdcl_bab_stgy_cdcl_bab by blast
  done

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

lemma cdcl_bab_cdcl\<^sub>W_learned_clauses_entailed_by_init:
  assumes
    \<open>cdcl_bab S T\<close> and
    entailed: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (abs_state S)\<close> and
    all_struct: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (abs_state T)\<close>
  using assms(1)
proof (induction rule: cdcl_bab.cases)
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

lemma conflicting_abs_state_conflicting[simp]:
  \<open>CDCL_W_Abstract_State.conflicting (abs_state S) = conflicting S\<close> and
  clauses_abs_state[simp]:
    \<open>cdcl\<^sub>W_restart_mset.clauses (abs_state S) = clauses S + conflicting_clss S\<close> and
  abs_state_tl_trail[simp]:
    \<open>abs_state (tl_trail S) = CDCL_W_Abstract_State.tl_trail (abs_state S)\<close> and
  abs_state_add_learned_cls[simp]:
    \<open>abs_state (add_learned_cls C S) = CDCL_W_Abstract_State.add_learned_cls C (abs_state S)\<close> and
  abs_state_update_conflicting[simp]:
    \<open>abs_state (update_conflicting D S) = CDCL_W_Abstract_State.update_conflicting D (abs_state S)\<close>
  by (auto simp: conflicting.simps abs_state_def cdcl\<^sub>W_restart_mset.clauses_def
    init_clss.simps learned_clss.simps clauses_def tl_trail.simps
    add_learned_cls.simps update_conflicting.simps)

lemma sim_abs_state_simp: \<open>S \<sim> T \<Longrightarrow> abs_state S = abs_state T\<close>
  by (auto simp: abs_state_def)

lemma abs_state_cons_trail[simp]:
    \<open>abs_state (cons_trail K S) = CDCL_W_Abstract_State.cons_trail K (abs_state S)\<close> and
  abs_state_reduce_trail_to[simp]:
    \<open>abs_state (reduce_trail_to M S) = cdcl\<^sub>W_restart_mset.reduce_trail_to M (abs_state S)\<close>
  subgoal by (auto simp: abs_state_def cons_trail.simps)
  subgoal by (induction rule: reduce_trail_to_induct)
       (auto simp: reduce_trail_to.simps cdcl\<^sub>W_restart_mset.reduce_trail_to.simps)
  done

lemma obacktrack_imp_backtrack:
  \<open>obacktrack S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.backtrack (abs_state S) (abs_state T)\<close>
  apply (auto elim!: obacktrackE simp: cdcl\<^sub>W_restart_mset.backtrack.simps sim_abs_state_simp)
  apply (rule_tac x=L in exI)
  apply (rule_tac x=D in exI)
  apply auto
  apply (rule_tac x=K in exI)
  apply (rule_tac x=M1 in exI)
  apply auto
  apply (rule_tac x=D' in exI)
  apply (auto simp: sim_abs_state_simp)
  done

lemma backtrack_imp_obacktrack:
  \<open>cdcl\<^sub>W_restart_mset.backtrack (abs_state S) T \<Longrightarrow> Ex (obacktrack S)\<close>
  apply (auto simp: cdcl\<^sub>W_restart_mset.backtrack.simps obacktrack.simps)
  apply (rule exI)
  apply (auto simp: cdcl\<^sub>W_restart_mset.backtrack.simps obacktrack.simps)
  apply (rule_tac x=L in exI)
  apply (rule_tac x=D in exI)
  apply auto
  apply (rule_tac x=K in exI)
  apply (rule_tac x=M1 in exI)
  apply auto
  apply (rule_tac x=D' in exI)
  apply (auto simp: sim_abs_state_simp)
  done


lemma cdcl\<^sub>W_same_weight: \<open>cdcl\<^sub>W S U \<Longrightarrow> weight S = weight U\<close>
  by (induction rule: cdcl\<^sub>W.induct)
    (auto simp: improve.simps cdcl\<^sub>W.simps
        propagate.simps sim_abs_state_simp abs_state_def cdcl\<^sub>W_restart_mset_state
        clauses_def conflict.simps cdcl\<^sub>W_o.simps decide.simps cdcl\<^sub>W_bj.simps
	skip.simps resolve.simps backtrack.simps)

lemma ocdcl\<^sub>W_o_same_weight: \<open>ocdcl\<^sub>W_o S U \<Longrightarrow> weight S = weight U\<close>
  by (induction rule: ocdcl\<^sub>W_o.induct)
    (auto simp: improve.simps cdcl\<^sub>W.simps ocdcl\<^sub>W_bj.simps
        propagate.simps sim_abs_state_simp abs_state_def cdcl\<^sub>W_restart_mset_state
        clauses_def conflict.simps cdcl\<^sub>W_o.simps decide.simps cdcl\<^sub>W_bj.simps
	skip.simps resolve.simps obacktrack.simps)

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


lemma wf_cdcl_bab:
  assumes improve: \<open>\<And>S T. improve S T \<Longrightarrow> (\<nu> (weight T), \<nu> (weight S)) \<in> R\<close> and
    wf_R: \<open>wf R\<close>
  shows \<open>wf {(T, S). cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S) \<and> cdcl_bab S T}\<close>
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
          cdcl\<^sub>W_o_cdcl\<^sub>W_o cdcl\<^sub>W_restart_mset.W_conflict W_conflict cdcl\<^sub>W_o.intros cdcl\<^sub>W.intros
	  cdcl\<^sub>W_o_cdcl\<^sub>W_o
	simp: cdcl\<^sub>W_same_weight cdcl_bab.simps ocdcl\<^sub>W_o_same_weight
	elim: conflict_optE)
  ultimately show ?thesis
    by (rule wf_subset)
qed

lemma cdcl_bab_stgy_invD:
  assumes \<open>cdcl_bab_stgy_inv S\<close>
  shows \<open>cdcl\<^sub>W_stgy_invariant S\<close>
  using assms unfolding cdcl\<^sub>W_stgy_invariant_def cdcl_bab_stgy_inv_def
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

lemma (in conflict_driven_clause_learning\<^sub>W) cdcl\<^sub>W_Ex_cdcl\<^sub>W_stgy:
  assumes
    \<open>cdcl\<^sub>W S T\<close>
  shows \<open>Ex(cdcl\<^sub>W_stgy S)\<close>
  using assms by (meson assms cdcl\<^sub>W.simps cdcl\<^sub>W_stgy.simps)

lemma conflict_is_false_with_level_abs_iff:
  \<open>cdcl\<^sub>W_restart_mset.conflict_is_false_with_level (abs_state S) \<longleftrightarrow>
    conflict_is_false_with_level S\<close>
  by (auto simp: cdcl\<^sub>W_restart_mset.conflict_is_false_with_level_def
    conflict_is_false_with_level_def)

lemma decide_abs_state_decide:
  \<open>cdcl\<^sub>W_restart_mset.decide (abs_state S) T \<Longrightarrow> cdcl_bab_struct_invs S \<Longrightarrow> Ex(decide S)\<close>
  apply (cases rule: cdcl\<^sub>W_restart_mset.decide.cases, assumption)
  subgoal for L
    apply (rule exI)
    apply (rule decide.intros[of _ L])
    by (auto simp: cdcl_bab_struct_invs_def abs_state_def cdcl\<^sub>W_restart_mset_state)
  done

context
  assumes can_always_improve:
     \<open>\<And>S. trail S \<Turnstile>asm clauses S \<Longrightarrow> no_step conflict_opt S \<Longrightarrow>
       conflicting S = None \<Longrightarrow>
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S) \<Longrightarrow>
       total_over_m (lits_of_l (trail S)) (set_mset (clauses S)) \<Longrightarrow> Ex (improve S)\<close>
begin

text \<open>The following theorems states a non-obvious (and slightly subtle) property: The fact that there
  is no conflicting cannot be shown without additional assumption. However, the assumption that every
  model leads to an improvements implies that we end up with a conflict.\<close>
lemma no_step_cdcl_bab_cdcl\<^sub>W:
  assumes
    ns: \<open>no_step cdcl_bab S\<close> and
    struct_invs: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close>
  shows \<open>no_step cdcl\<^sub>W_restart_mset.cdcl\<^sub>W (abs_state S)\<close>
proof -
  have ns_confl: \<open>no_step skip S\<close>  \<open>no_step resolve S\<close>  \<open>no_step obacktrack S\<close> and
    ns_nc: \<open>no_step conflict S\<close> \<open>no_step propagate S\<close> \<open>no_step improve S\<close> \<open>no_step conflict_opt S\<close>
      \<open>no_step decide S\<close>
    using ns
    by (auto simp: cdcl_bab.simps ocdcl\<^sub>W_o.simps ocdcl\<^sub>W_bj.simps)
  have alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (abs_state S)\<close>
    using struct_invs unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def by fast+

  have False if st: \<open>\<exists>T. cdcl\<^sub>W_restart_mset.cdcl\<^sub>W (abs_state S) T\<close>
  proof (cases \<open>conflicting S = None\<close>)
    case True
    have \<open>total_over_m (lits_of_l (trail S)) (set_mset (init_clss S))\<close>
      using ns_nc True apply - apply (rule ccontr)
      by (force simp: decide.simps total_over_m_def total_over_set_def
        Decided_Propagated_in_iff_in_lits_of_l)
    then have tot: \<open>total_over_m (lits_of_l (trail S)) (set_mset (clauses S))\<close>
      using alien unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def
      by (auto simp: total_over_set_atm_of total_over_m_def clauses_def
        abs_state_def init_clss.simps learned_clss.simps trail.simps)
    then have \<open>trail S \<Turnstile>asm clauses S\<close>
      using ns_nc True unfolding true_annots_def apply -
      apply clarify
      subgoal for C
        using all_variables_defined_not_imply_cnot[of C \<open>trail S\<close>]
        by (fastforce simp: conflict.simps total_over_set_atm_of
        dest: multi_member_split)
      done
    from can_always_improve[OF this] have \<open>False\<close>
      using ns_nc True struct_invs tot by blast
    then show \<open>?thesis\<close>
      by blast
  next
    case False
    have nss: \<open>no_step cdcl\<^sub>W_restart_mset.skip (abs_state S)\<close>
       \<open>no_step cdcl\<^sub>W_restart_mset.resolve (abs_state S)\<close>
       \<open>no_step cdcl\<^sub>W_restart_mset.backtrack (abs_state S)\<close>
      using ns_confl by (force simp: cdcl\<^sub>W_restart_mset.skip.simps skip.simps
        cdcl\<^sub>W_restart_mset.resolve.simps resolve.simps
	dest: backtrack_imp_obacktrack)+
    then show \<open>?thesis\<close>
      using that False by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W.simps
        cdcl\<^sub>W_restart_mset.propagate.simps cdcl\<^sub>W_restart_mset.conflict.simps
	cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o.simps cdcl\<^sub>W_restart_mset.decide.simps
	cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_bj.simps)
  qed
  then show \<open>?thesis\<close> by blast
qed


lemma no_step_cdcl_bab_stgy:
  assumes
    n_s: \<open>no_step cdcl_bab S\<close> and
    all_struct: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> and
    stgy_inv: \<open>cdcl_bab_stgy_inv S\<close>
  shows \<open>conflicting S = None \<or> conflicting S = Some {#}\<close>
proof (rule ccontr)
  assume \<open>\<not> ?thesis\<close>
  then obtain D where \<open>conflicting S = Some D\<close> and \<open>D \<noteq> {#}\<close>
    by auto
  moreover have \<open>no_step cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (abs_state S)\<close>
    using no_step_cdcl_bab_cdcl\<^sub>W[OF n_s all_struct]
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_cdcl\<^sub>W by blast
  moreover have le: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause (abs_state S)\<close>
    using all_struct unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def by fast
  ultimately show False
    using cdcl\<^sub>W_restart_mset.conflicting_no_false_can_do_step[of \<open>abs_state S\<close>] all_struct stgy_inv le
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl_bab_stgy_inv_def
    by (force dest: distinct_cdcl\<^sub>W_state_distinct_cdcl\<^sub>W_state
      simp: conflict_is_false_with_level_abs_iff)
qed

lemma no_step_cdcl_bab_stgy_empty_conflict:
  assumes
    n_s: \<open>no_step cdcl_bab S\<close> and
    all_struct: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> and
    stgy_inv: \<open>cdcl_bab_stgy_inv S\<close>
  shows \<open>conflicting S = Some {#}\<close>
proof (rule ccontr)
  assume H: \<open>\<not> ?thesis\<close>
  have all_struct': \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close>
    by (simp add: all_struct cdcl\<^sub>W_all_struct_inv_restart_cdcl\<^sub>W_all_struct_inv)
  have le: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause (abs_state S)\<close>
    using all_struct
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl_bab_stgy_inv_def
    by auto
  have \<open>conflicting S = None \<or> conflicting S = Some {#}\<close>
    using no_step_cdcl_bab_stgy[OF n_s all_struct' stgy_inv] .
  then have confl: \<open>conflicting S = None\<close>
    using H by blast
  have \<open>no_step cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (abs_state S)\<close>
    using no_step_cdcl_bab_cdcl\<^sub>W[OF n_s all_struct]
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_cdcl\<^sub>W by blast
  then have entail: \<open>trail S \<Turnstile>asm clauses S\<close>
    using confl cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_final_state_conclusive2[of \<open>abs_state S\<close>]
      all_struct stgy_inv le
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl_bab_stgy_inv_def
    by (auto simp: conflict_is_false_with_level_abs_iff)
  have \<open>total_over_m (lits_of_l (trail S)) (set_mset (clauses S))\<close>
    using cdcl\<^sub>W_restart_mset.no_step_cdcl\<^sub>W_total[OF no_step_cdcl_bab_cdcl\<^sub>W, of S] all_struct n_s confl
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by auto
  with can_always_improve entail confl all_struct
  show \<open>False\<close>
    using n_s by (auto simp: cdcl_bab.simps)
qed

lemma cdcl_bab_no_conflicting_clss_cdcl\<^sub>W:
  assumes \<open>cdcl_bab S T\<close> and \<open>conflicting_clss T = {#}\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W (abs_state S) (abs_state T) \<and> conflicting_clss S = {#}\<close>
  using assms
  by (auto simp: cdcl_bab.simps conflict_opt.simps improve.simps ocdcl\<^sub>W_o.simps
      ocdcl\<^sub>W_bj.simps
    dest: conflict_conflict propagate_propagate decide_decide skip_skip resolve_resolve
      backtrack_backtrack
    intro: cdcl\<^sub>W_restart_mset.W_conflict cdcl\<^sub>W_restart_mset.W_propagate cdcl\<^sub>W_restart_mset.W_other
    dest: conflicting_clss_update_weight_information_in
    elim: conflictE propagateE decideE skipE resolveE improveE obacktrackE)


lemma rtranclp_cdcl_bab_no_conflicting_clss_cdcl\<^sub>W:
  assumes \<open>cdcl_bab\<^sup>*\<^sup>* S T\<close> and \<open>conflicting_clss T = {#}\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W\<^sup>*\<^sup>* (abs_state S) (abs_state T) \<and> conflicting_clss S = {#}\<close>
  using assms
  by (induction rule: rtranclp_induct)
     (fastforce dest: cdcl_bab_no_conflicting_clss_cdcl\<^sub>W)+

lemma conflict_abs_ex_conflict_no_conflicting:
  assumes \<open>cdcl\<^sub>W_restart_mset.conflict (abs_state S) T\<close> and \<open>conflicting_clss S = {#}\<close>
  shows \<open>\<exists>T. conflict S T\<close>
  using assms by (auto simp: conflict.simps cdcl\<^sub>W_restart_mset.conflict.simps abs_state_def
    cdcl\<^sub>W_restart_mset_state clauses_def cdcl\<^sub>W_restart_mset.clauses_def)

lemma propagate_abs_ex_propagate_no_conflicting:
  assumes \<open>cdcl\<^sub>W_restart_mset.propagate (abs_state S) T\<close> and \<open>conflicting_clss S = {#}\<close>
  shows \<open>\<exists>T. propagate S T\<close>
  using assms by (auto simp: propagate.simps cdcl\<^sub>W_restart_mset.propagate.simps abs_state_def
    cdcl\<^sub>W_restart_mset_state clauses_def cdcl\<^sub>W_restart_mset.clauses_def)

lemma cdcl_bab_stgy_no_conflicting_clss_cdcl\<^sub>W_stgy:
  assumes \<open>cdcl_bab_stgy S T\<close> and \<open>conflicting_clss T = {#}\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (abs_state S) (abs_state T)\<close>
proof -
  have \<open>conflicting_clss S = {#}\<close>
    using cdcl_bab_no_conflicting_clss_cdcl\<^sub>W[of S T] assms
    by (auto dest: cdcl_bab_stgy_cdcl_bab)
  then show ?thesis
    using assms
    apply (auto 7 5 simp: cdcl_bab_stgy.simps conflict_opt.simps ocdcl\<^sub>W_o.simps
	ocdcl\<^sub>W_bj.simps
      dest!: conflict_conflict propagate_propagate decide_decide skip_skip resolve_resolve
	backtrack_backtrack
      dest!: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy.intros cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o.intros
      dest: conflicting_clss_update_weight_information_in
	conflict_abs_ex_conflict_no_conflicting
	propagate_abs_ex_propagate_no_conflicting
      elim: improveE)
      apply (rule cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy.intros(3))
      apply (auto dest: 
	conflict_abs_ex_conflict_no_conflicting
	propagate_abs_ex_propagate_no_conflicting)
      apply (rule cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy.intros(3))
      apply (auto dest: 
	conflict_abs_ex_conflict_no_conflicting
	propagate_abs_ex_propagate_no_conflicting)
      apply (rule cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy.intros(3))
      apply (auto dest: 
	conflict_abs_ex_conflict_no_conflicting
	propagate_abs_ex_propagate_no_conflicting)
      apply (rule cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy.intros(3))
      apply (auto dest: 
	conflict_abs_ex_conflict_no_conflicting
	propagate_abs_ex_propagate_no_conflicting)
      done
qed

lemma rtranclp_cdcl_bab_stgy_no_conflicting_clss_cdcl\<^sub>W_stgy:
  assumes \<open>cdcl_bab_stgy\<^sup>*\<^sup>* S T\<close> and \<open>conflicting_clss T = {#}\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (abs_state S) (abs_state T)\<close>
  using assms apply (induction rule: rtranclp_induct)
  subgoal by auto
  subgoal for T U
    using cdcl_bab_no_conflicting_clss_cdcl\<^sub>W[of T U, OF cdcl_bab_stgy_cdcl_bab]
    by (auto dest: cdcl_bab_stgy_no_conflicting_clss_cdcl\<^sub>W_stgy)
  done


lemma full_cdcl_bab_stgy_no_conflicting_clss_unsat:
  assumes
    full: \<open>full cdcl_bab_stgy S T\<close> and
    all_struct: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> and
    stgy_inv: \<open>cdcl_bab_stgy_inv S\<close> and
    ent_init: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (abs_state S)\<close> and
    [simp]: \<open>conflicting_clss T = {#}\<close>
  shows \<open>unsatisfiable (set_mset (init_clss S))\<close>
proof -
  have ns: "no_step cdcl_bab_stgy T" and
    st: "cdcl_bab_stgy\<^sup>*\<^sup>* S T" and
    st': "cdcl_bab\<^sup>*\<^sup>* S T" and
    ns': \<open>no_step cdcl_bab T\<close>
    using full unfolding full_def apply (blast dest: rtranclp_cdcl_bab_stgy_cdcl_bab)+
    using full unfolding full_def
    by (metis cdcl_bab.simps cdcl_bab_conflict cdcl_bab_conflict_opt cdcl_bab_improve
      cdcl_bab_other' cdcl_bab_propagate no_confl_prop_impr.elims(3))
  have struct_T: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state T)\<close>
    using rtranclp_cdcl_bab_stgy_all_struct_inv[OF st' all_struct] .
  have [simp]: \<open>conflicting_clss S = {#}\<close>
    using rtranclp_cdcl_bab_no_conflicting_clss_cdcl\<^sub>W[OF st'] by auto
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (abs_state S) (abs_state T)\<close>
    using rtranclp_cdcl_bab_stgy_no_conflicting_clss_cdcl\<^sub>W_stgy[OF st] by auto
  then have \<open>full cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (abs_state S) (abs_state T)\<close>
    using no_step_cdcl_bab_cdcl\<^sub>W[OF ns' struct_T] unfolding full_def
    by (auto dest: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_cdcl\<^sub>W)
  moreover have \<open>cdcl\<^sub>W_restart_mset.no_smaller_confl (state_butlast S)\<close>
    using stgy_inv ent_init
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def conflict_is_false_with_level_abs_iff
      cdcl_bab_stgy_inv_def conflict_is_false_with_level_abs_iff
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant_def
    by (auto simp: abs_state_def cdcl\<^sub>W_restart_mset_state cdcl_bab_stgy_inv_def
      no_smaller_confl_def cdcl\<^sub>W_restart_mset.no_smaller_confl_def clauses_def
      cdcl\<^sub>W_restart_mset.clauses_def)
  ultimately have "conflicting T = Some {#} \<and> unsatisfiable (set_mset (init_clss S))
    \<or> conflicting T = None \<and> trail T \<Turnstile>asm init_clss S"
    using cdcl\<^sub>W_restart_mset.full_cdcl\<^sub>W_stgy_inv_normal_form[of \<open>abs_state S\<close> \<open>abs_state T\<close>] all_struct
      stgy_inv ent_init
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def conflict_is_false_with_level_abs_iff
      cdcl_bab_stgy_inv_def conflict_is_false_with_level_abs_iff
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant_def
    by (auto simp: abs_state_def cdcl\<^sub>W_restart_mset_state cdcl_bab_stgy_inv_def)
  moreover have \<open>cdcl_bab_stgy_inv T\<close>
    using rtranclp_cdcl_bab_stgy_stgy_inv[OF st all_struct stgy_inv] .
  ultimately show \<open>?thesis\<close>
    using no_step_cdcl_bab_stgy_empty_conflict[OF ns' struct_T] by auto

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
      \<open>state S = (M, N, U, C, K) \<Longrightarrow> state (update_additional_info K' S) = (M, N, U, C, K')\<close> and
    weight_init_state:
      \<open>\<And>N :: 'v clauses. fst (additional_info (init_state N)) = None\<close>
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

lemma distinct_mset_pNeg_iff[iff]: \<open>distinct_mset (pNeg x) \<longleftrightarrow> distinct_mset x\<close>
  unfolding pNeg_def
  by (rule distinct_image_mset_inj) (auto simp: inj_on_def)

definition conflicting_clauses :: "'v clauses \<Rightarrow> 'v clause option \<Rightarrow> 'v clauses" where
  \<open>conflicting_clauses M w = {#pNeg C | C \<in># mset_set (simple_clss (atms_of_mm M)).
      atms_of C = atms_of_mm M \<and> \<rho> C \<ge> \<rho>' w#}\<close>

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

lemma state_additional_info':
  \<open>state S = (trail S, init_clss S, learned_clss S, conflicting S, weight S, additional_info' S)\<close>
  unfolding additional_info'_def by (cases \<open>state S\<close>; auto simp: state_prop weight_def)

lemma state_update_weight_information:
  \<open>state S = (M, N, U, C, w, other) \<Longrightarrow>
    \<exists>w'. state (update_weight_information T S) = (M, N, U, C, w', other)\<close>
  unfolding update_weight_information_def by (cases \<open>state S\<close>; auto simp: state_prop weight_def)

lemma conflicting_clss_incl_init_clss:
  \<open>atms_of_mm (conflicting_clss S) \<subseteq> atms_of_mm (init_clss S)\<close>
  unfolding conflicting_clss_def conflicting_clauses_def
  apply (auto simp: simple_clss_finite)
  by (auto simp: simple_clss_def atms_of_ms_def split: if_splits)

lemma distinct_mset_mset_conflicting_clss: \<open>distinct_mset_mset (conflicting_clss S)\<close>
  unfolding conflicting_clss_def conflicting_clauses_def distinct_mset_set_def
  apply (auto simp: simple_clss_finite)
  by (auto simp: simple_clss_def)

lemma is_improving_conflicting_clss_update_weight_information: \<open>is_improving M S \<Longrightarrow>
       conflicting_clss S \<subseteq># conflicting_clss (update_weight_information M S)\<close>
  by (cases \<open>weight S\<close>) (auto simp: is_improving_int_def conflicting_clss_def conflicting_clauses_def
      simp: multiset_filter_mono2 le_less intro!: image_mset_subseteq_mono
      split: enat.splits)

lemma total_over_m_atms_incl:
  assumes \<open>total_over_m (lit_of ` set M) (set_mset N)\<close>
  shows
    \<open>x \<in> atms_of_mm N \<Longrightarrow> x \<in> atms_of (lit_of `# mset M)\<close>
  by (metis neg_lit_in_atms_of pos_lit_in_atms_of set_image_mset set_mset_mset
    total_over_m_def total_over_set_def assms)

lemma conflicting_clss_update_weight_information_in:
  assumes \<open>is_improving M S\<close>
  shows \<open>negate_ann_lits M \<in># conflicting_clss (update_weight_information M S)\<close>
  using assms apply (auto simp: simple_clss_finite
    conflicting_clauses_def conflicting_clss_def is_improving_int_def)
  by (auto simp: is_improving_int_def conflicting_clss_def conflicting_clauses_def
      simp: multiset_filter_mono2 simple_clss_def lits_of_def
      negate_ann_lits_pNeg_lit_of image_iff dest: total_over_m_atms_incl)

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

lemma conflict_clss_update_weight_no_alien:
  \<open>atms_of_mm (conflicting_clss (update_weight_information M S))
    \<subseteq> atms_of_mm (init_clss S)\<close>
  apply (auto simp: conflicting_clss_def conflicting_clauses_def atms_of_ms_def
    cdcl\<^sub>W_restart_mset_state simple_clss_finite)
  done

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
  subgoal by (rule conflict_clss_update_weight_no_alien)
  done

lemma wf_cdcl_bab: \<open>wf {(T, S). cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S) \<and> cdcl_bab S T}\<close>
  apply (rule wf_cdcl_bab[of \<rho>' \<open>{(j, i). j < i}\<close>])
  subgoal for S T
    by (cases \<open>weight S\<close>; cases \<open>weight T\<close>)
      (auto simp: improve.simps is_improving_int_def
        split: enat.splits)
  subgoal by (simp add: wf)
  done

lemma can_always_improve:
  assumes
    ent: \<open>trail S \<Turnstile>asm clauses S\<close> and
    total: \<open>total_over_m (lits_of_l (trail S)) (set_mset (clauses S))\<close> and
    n_s: \<open>no_step conflict_opt S\<close> and
    confl: \<open>conflicting S = None\<close> and
    all_struct: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close>
   shows \<open>Ex (improve S)\<close>
proof -
  have H: \<open>(lit_of `# mset (trail S)) \<in># mset_set (simple_clss (atms_of_mm (init_clss S)))\<close>
    \<open>(lit_of `# mset (trail S)) \<in> (simple_clss (atms_of_mm (init_clss S)))\<close>
    \<open>no_dup (trail S)\<close>
    apply (subst finite_set_mset_mset_set[OF simple_clss_finite])
    using all_struct by (auto simp: simple_clss_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
        no_strange_atm_def atms_of_def lits_of_def image_image
        cdcl\<^sub>W_M_level_inv_def clauses_def
      dest: no_dup_not_tautology no_dup_distinct)
  then have \<open>enat (\<rho> (lit_of `# mset (trail S))) < \<rho>' (weight S)\<close>
    using n_s confl total
    by (auto simp: conflict_opt.simps conflicting_clss_def lits_of_def
         conflicting_clauses_def clauses_def negate_ann_lits_pNeg_lit_of image_iff
         simple_clss_def subset_iff
       dest!: spec[of _ \<open>(lit_of `# mset (trail S))\<close>] dest: total_over_m_atms_incl)
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
        total_over_m_def total_over_set_def neq_Nil_conv cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def lits_of_def
        no_strange_atm_def defined_lit_map clauses_def
      intro!: bexI[of _ \<open>atm_of (lit_of (hd (trail S)))\<close>])
    apply (metis UnCI image_eqI literal.sel(2))
    by (metis UnCI image_eqI literal.sel(1))
  ultimately show \<open>Ex (improve S)\<close>
    using improve.intros[of S \<open>[]\<close> \<open>trail S\<close> \<open>update_weight_information (trail S) S\<close>] total H confl
    by (auto simp: is_improving_int_def)
qed

lemma no_step_cdcl_bab_stgy_empty_conflict:
  assumes
    n_s: \<open>no_step cdcl_bab S\<close> and
    all_struct: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> and
    stgy_inv: \<open>cdcl_bab_stgy_inv S\<close>
  shows \<open>conflicting S = Some {#}\<close>
  by (rule no_step_cdcl_bab_stgy_empty_conflict[OF can_always_improve assms])


lemma cdcl_bab_larger_still_larger:
  assumes
    \<open>cdcl_bab S T\<close>
  shows \<open>\<rho>' (weight S) \<ge> \<rho>' (weight T)\<close>
  using assms apply (cases rule: cdcl_bab.cases)
  by (auto simp: conflict.simps decide.simps propagate.simps improve.simps is_improving_int_def
    conflict_opt.simps ocdcl\<^sub>W_o.simps ocdcl\<^sub>W_bj.simps skip.simps resolve.simps obacktrack.simps)

lemma obacktrack_model_still_model:
  assumes
    \<open>obacktrack S T\<close> and
    all_struct: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> and
    ent: \<open>set_mset I \<Turnstile>sm clauses S\<close>  \<open>set_mset I \<Turnstile>sm conflicting_clss S\<close> and
    dist: \<open>distinct_mset I\<close> and
    cons: \<open>consistent_interp (set_mset I)\<close> and
    tot: \<open>atms_of I = atms_of_mm (init_clss S)\<close> and
    opt_struct: \<open>cdcl_bab_struct_invs S\<close> and
    le: \<open>\<rho> I < \<rho>' (weight T)\<close>
  shows
    \<open>set_mset I \<Turnstile>sm clauses T \<and> set_mset I \<Turnstile>sm conflicting_clss T\<close>
  using assms(1)
proof (cases rule: obacktrack.cases)
  case (obacktrack_rule L D K M1 M2 D' i) note confl = this(1) and DD' = this(7) and
    clss_L_D' = this(8) and T = this(9)
  have H: \<open>total_over_m I (set_mset (clauses S + conflicting_clss S) \<union> {add_mset L D'}) \<Longrightarrow>
      consistent_interp I \<Longrightarrow>
      I \<Turnstile>sm clauses S + conflicting_clss S \<Longrightarrow> I \<Turnstile> add_mset L D'\<close> for I
    using clss_L_D'
    unfolding true_clss_cls_def
    by blast
  have alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (abs_state S)\<close>
    using all_struct unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast+
  have \<open>total_over_m (set_mset I) (set_mset (init_clss S))\<close>
    using tot[symmetric]
    by (auto simp: total_over_m_def total_over_set_def atm_iff_pos_or_neg_lit)

  then have 1: \<open>total_over_m (set_mset I) (set_mset (clauses S + conflicting_clss S) \<union> {add_mset L D'})\<close>
    using alien T confl tot DD' opt_struct
    unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def total_over_m_def total_over_set_def
    apply (auto simp: cdcl\<^sub>W_restart_mset_state abs_state_def atms_of_def clauses_def
      cdcl_bab_struct_invs_def dest: multi_member_split)
    by blast
  have 2: \<open>set_mset I \<Turnstile>sm conflicting_clss S\<close>
    unfolding true_clss_def
  proof
    fix C
    assume \<open>C \<in># conflicting_clss S\<close>
    then obtain x where
      [simp]: \<open>C = pNeg x\<close> and
      x: \<open>x \<in> simple_clss (atms_of_mm (init_clss S))\<close> and
      atm: \<open>atms_of x = atms_of_mm (init_clss S)\<close> and
      \<open>\<rho>' (weight S) \<le> enat (\<rho> x)\<close>
      unfolding conflicting_clss_def conflicting_clauses_def
      by (auto simp: simple_clss_finite)
    then have \<open>x \<noteq> I\<close>
      using le T
      by (auto simp: )
    then have \<open>set_mset x \<noteq> set_mset I\<close>
      using distinct_set_mset_eq_iff[of x I] x dist
      by (auto simp: simple_clss_def)
    then have \<open>\<exists>a. ((a \<in># x \<and> a \<notin># I) \<or> (a \<in># I \<and> a \<notin># x))\<close>
      by auto
    then obtain L where
      \<open>L \<in># x\<close> and
      \<open>-L \<in># I\<close>
      apply clarify
      apply (case_tac a)
      using atm[symmetric] tot[symmetric] that[of _] that[of \<open>- _\<close>]
      atm_iff_pos_or_neg_lit[of a I] atm_iff_pos_or_neg_lit[of a x]
      by (metis (full_types) assms(6) atm atm_iff_pos_or_neg_lit uminus_Pos uminus_of_uminus_id)+
    then show \<open>set_mset I \<Turnstile> C\<close>
      by (auto simp: simple_clss_finite pNeg_def dest!: multi_member_split)
  qed
  have \<open>set_mset I \<Turnstile> add_mset L D'\<close>
    using H[OF 1 cons] 2 ent by auto
  then show ?thesis
    using ent obacktrack_rule 2 by auto
qed


lemma improve_model_still_model:
  assumes
    \<open>improve S T\<close> and
    all_struct: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> and
    ent: \<open>set_mset I \<Turnstile>sm clauses S\<close>  \<open>set_mset I \<Turnstile>sm conflicting_clss S\<close> and
    dist: \<open>distinct_mset I\<close> and
    cons: \<open>consistent_interp (set_mset I)\<close> and
    tot: \<open>atms_of I = atms_of_mm (init_clss S)\<close> and
    opt_struct: \<open>cdcl_bab_struct_invs S\<close> and
    le: \<open>\<rho> I < \<rho>' (weight T)\<close>
  shows
    \<open>set_mset I \<Turnstile>sm clauses T \<and> set_mset I \<Turnstile>sm conflicting_clss T\<close>
  using assms(1)
proof (cases rule: improve.cases)
  case (improve_rule M M') note confl = this(4) and T = this(5)
  have alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (abs_state S)\<close>
    using all_struct unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast+
  have \<open>total_over_m (set_mset I) (set_mset (init_clss S))\<close>
    using tot[symmetric]
    by (auto simp: total_over_m_def total_over_set_def atm_iff_pos_or_neg_lit)

  have 2: \<open>set_mset I \<Turnstile>sm conflicting_clss T\<close>
    unfolding true_clss_def
  proof
    fix C
    assume \<open>C \<in># conflicting_clss T\<close>
    then obtain x where
      [simp]: \<open>C = pNeg x\<close> and
      x: \<open>x \<in> simple_clss (atms_of_mm (init_clss T))\<close> and
      atm: \<open>atms_of x = atms_of_mm (init_clss T)\<close> and
      \<open>\<rho>' (weight T) \<le> enat (\<rho> x)\<close>
      unfolding conflicting_clss_def conflicting_clauses_def
      by (auto simp: simple_clss_finite)
    then have \<open>x \<noteq> I\<close>
      using cdcl_bab_larger_still_larger[of S T]  cdcl_bab.intros(3)[OF assms(1)]
      using le T
      apply (simp add: )
      by (smt le_less_trans less_irrefl)
    then have \<open>set_mset x \<noteq> set_mset I\<close>
      using distinct_set_mset_eq_iff[of x I] x dist
      by (auto simp: simple_clss_def)
    then have \<open>\<exists>a. ((a \<in># x \<and> a \<notin># I) \<or> (a \<in># I \<and> a \<notin># x))\<close>
      by auto
    then obtain L where
      \<open>L \<in># x\<close> and
      \<open>-L \<in># I\<close>
      apply clarify
      apply (case_tac a)
      using atm[symmetric] tot[symmetric] that[of _] that[of \<open>- _\<close>]
      atm_iff_pos_or_neg_lit[of a I] atm_iff_pos_or_neg_lit[of a x]
      cdcl_bab_no_more_init_clss[OF cdcl_bab.intros(3)[OF assms(1)]]
      by (metis (full_types) assms(6) atm atm_iff_pos_or_neg_lit uminus_Pos uminus_of_uminus_id)+
    then show \<open>set_mset I \<Turnstile> C\<close>
      by (auto simp: simple_clss_finite pNeg_def dest!: multi_member_split)
  qed
  then show ?thesis
    using ent improve_rule 2 T by auto
qed

lemma cdcl_bab_still_model:
  assumes
    \<open>cdcl_bab S T\<close> and
    all_struct: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> and
    ent: \<open>set_mset I \<Turnstile>sm clauses S\<close> \<open>set_mset I \<Turnstile>sm conflicting_clss S\<close> and
    dist: \<open>distinct_mset I\<close> and
    cons: \<open>consistent_interp (set_mset I)\<close> and
    tot: \<open>atms_of I = atms_of_mm (init_clss S)\<close> and
    opt_struct: \<open>cdcl_bab_struct_invs S\<close>
  shows
    \<open>(set_mset I \<Turnstile>sm clauses T \<and> set_mset I \<Turnstile>sm conflicting_clss T) \<or> \<rho> I \<ge> \<rho>' (weight T)\<close>
  using assms
proof (cases rule: cdcl_bab.cases)
  case cdcl_conflict
  then show ?thesis
    using ent by (auto simp: conflict.simps)
next
  case cdcl_propagate
  then show ?thesis
    using ent by (auto simp: propagate.simps)
next
  case cdcl_conflict_opt
  then show ?thesis
    using ent by (auto simp: conflict_opt.simps)
next
  case cdcl_improve
  from improve_model_still_model[OF this all_struct ent dist cons tot opt_struct]
  show ?thesis
    by (auto simp: improve.simps)
next
  case cdcl_other'
  then show ?thesis
  proof (induction rule: ocdcl\<^sub>W_o_all_rules_induct)
    case (decide T)
    then show ?case
      using ent by (auto simp: decide.simps)
  next
    case (skip T)
    then show ?case
      using ent by (auto simp: skip.simps)
  next
    case (resolve T)
    then show ?case
      using ent by (auto simp: resolve.simps)
  next
    case (backtrack T)
    from obacktrack_model_still_model[OF this all_struct ent dist cons tot opt_struct]
    show ?case
      by auto
  qed
qed

lemma rtranclp_cdcl_bab_still_model:
  assumes
    st: \<open>cdcl_bab\<^sup>*\<^sup>* S T\<close> and
    all_struct: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> and
    ent: \<open>(set_mset I \<Turnstile>sm clauses S \<and> set_mset I \<Turnstile>sm conflicting_clss S) \<or> \<rho> I \<ge> \<rho>' (weight S)\<close> and
    dist: \<open>distinct_mset I\<close> and
    cons: \<open>consistent_interp (set_mset I)\<close> and
    tot: \<open>atms_of I = atms_of_mm (init_clss S)\<close> and
    opt_struct: \<open>cdcl_bab_struct_invs S\<close>
  shows
    \<open>(set_mset I \<Turnstile>sm clauses T \<and> set_mset I \<Turnstile>sm conflicting_clss T) \<or> \<rho> I \<ge> \<rho>' (weight T)\<close>
  using st
proof (induction rule: rtranclp_induct)
  case base
  then show ?case
    using ent by auto
next
  case (step T U) note star = this(1) and st = this(2) and IH = this(3)
  have 1: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state T)\<close>
    using rtranclp_cdcl_bab_stgy_all_struct_inv[OF star all_struct] .

  have 2: \<open>cdcl_bab_struct_invs T\<close>
    using rtranclp_cdcl_bab_cdcl_bab_struct_invs[OF star opt_struct] .
  have 3: \<open>atms_of I = atms_of_mm (init_clss T)\<close>
    using tot rtranclp_cdcl_bab_no_more_init_clss[OF star] by auto
  show ?case
    using cdcl_bab_still_model[OF st 1 _ _ dist cons 3 2] IH
      cdcl_bab_larger_still_larger[OF st]
    by auto
qed

lemma full_cdcl_bab_stgy_larger_or_equal_weight:
  assumes
    st: \<open>full cdcl_bab_stgy S T\<close> and
    all_struct: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> and
    ent: \<open>(set_mset I \<Turnstile>sm clauses S \<and> set_mset I \<Turnstile>sm conflicting_clss S) \<or> \<rho> I \<ge> \<rho>' (weight S)\<close> and
    dist: \<open>distinct_mset I\<close> and
    cons: \<open>consistent_interp (set_mset I)\<close> and
    tot: \<open>atms_of I = atms_of_mm (init_clss S)\<close> and
    opt_struct: \<open>cdcl_bab_struct_invs S\<close> and
    stgy_inv: \<open>cdcl_bab_stgy_inv S\<close>
  shows
    \<open>\<rho> I \<ge> \<rho>' (weight T)\<close> and
    \<open>unsatisfiable (set_mset (clauses T + conflicting_clss T))\<close>
proof -
  have ns: \<open>no_step cdcl_bab_stgy T\<close> and
    st: \<open>cdcl_bab_stgy\<^sup>*\<^sup>* S T\<close> and
    st': \<open>cdcl_bab\<^sup>*\<^sup>* S T\<close>
    using st unfolding full_def by (auto intro: rtranclp_cdcl_bab_stgy_cdcl_bab)
  have ns': \<open>no_step cdcl_bab T\<close>
    by (meson cdcl_bab.cases cdcl_bab_stgy.simps no_confl_prop_impr.elims(3) ns)
  have struct_T: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state T)\<close>
    using rtranclp_cdcl_bab_stgy_all_struct_inv[OF st' all_struct] .
  have stgy_T: \<open>cdcl_bab_stgy_inv T\<close>
    using rtranclp_cdcl_bab_stgy_stgy_inv[OF st all_struct stgy_inv] .
  have confl: \<open>conflicting T = Some {#}\<close>
    using no_step_cdcl_bab_stgy_empty_conflict[OF ns' struct_T stgy_T] .

  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause (abs_state T)\<close> and
    alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (abs_state T)\<close>
    using struct_T unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def by fast+
  then have ent': \<open>set_mset (clauses T + conflicting_clss T) \<Turnstile>p {#}\<close>
    using confl unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def
    by auto
  have atms_eq: \<open>atms_of I \<union> atms_of_mm (conflicting_clss T) = atms_of_mm (init_clss T)\<close>
    using tot[symmetric] atms_of_conflicting_clss[of T] alien
    unfolding rtranclp_cdcl_bab_no_more_init_clss[OF st'] cdcl\<^sub>W_restart_mset.no_strange_atm_def
    by (auto simp: clauses_def total_over_m_def total_over_set_def atm_iff_pos_or_neg_lit
      abs_state_def cdcl\<^sub>W_restart_mset_state)

  have \<open>\<not> (set_mset I \<Turnstile>sm clauses T + conflicting_clss T)\<close>
  proof
    assume ent'': \<open>set_mset I \<Turnstile>sm clauses T + conflicting_clss T\<close>
    moreover have \<open>total_over_m (set_mset I) (set_mset (clauses T + conflicting_clss T))\<close>
      using tot[symmetric] atms_of_conflicting_clss[of T] alien
      unfolding rtranclp_cdcl_bab_no_more_init_clss[OF st'] cdcl\<^sub>W_restart_mset.no_strange_atm_def
      by (auto simp: clauses_def total_over_m_def total_over_set_def atm_iff_pos_or_neg_lit
        abs_state_def cdcl\<^sub>W_restart_mset_state atms_eq)
    then show \<open>False\<close>
      using ent' cons ent''
      unfolding true_clss_cls_def by auto
  qed
  then show \<open>\<rho>' (weight T) \<le> enat (\<rho> I)\<close>
    using rtranclp_cdcl_bab_still_model[OF st' all_struct ent dist cons tot opt_struct]
    by auto

  show \<open>unsatisfiable (set_mset (clauses T + conflicting_clss T))\<close>
  proof
    assume \<open>satisfiable (set_mset (clauses T + conflicting_clss T))\<close>
    then obtain I where
      ent'': \<open>I \<Turnstile>sm clauses T + conflicting_clss T\<close> and
      tot: \<open>total_over_m I (set_mset (clauses T + conflicting_clss T))\<close> and
      \<open>consistent_interp I\<close>
      unfolding satisfiable_def
      by blast
    then show \<open>False\<close>
      using ent' cons ent''
      unfolding true_clss_cls_def by auto
  qed
qed


lemma full_cdcl_bab_stgy_unsat:
  assumes
    st: \<open>full cdcl_bab_stgy S T\<close> and
    all_struct: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> and
    opt_struct: \<open>cdcl_bab_struct_invs S\<close> and
    stgy_inv: \<open>cdcl_bab_stgy_inv S\<close>
  shows
    \<open>unsatisfiable (set_mset (clauses T + conflicting_clss T))\<close>
proof -
  have ns: \<open>no_step cdcl_bab_stgy T\<close> and
    st: \<open>cdcl_bab_stgy\<^sup>*\<^sup>* S T\<close> and
    st': \<open>cdcl_bab\<^sup>*\<^sup>* S T\<close>
    using st unfolding full_def by (auto intro: rtranclp_cdcl_bab_stgy_cdcl_bab)
  have ns': \<open>no_step cdcl_bab T\<close>
    by (meson cdcl_bab.cases cdcl_bab_stgy.simps no_confl_prop_impr.elims(3) ns)
  have struct_T: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state T)\<close>
    using rtranclp_cdcl_bab_stgy_all_struct_inv[OF st' all_struct] .
  have stgy_T: \<open>cdcl_bab_stgy_inv T\<close>
    using rtranclp_cdcl_bab_stgy_stgy_inv[OF st all_struct stgy_inv] .
  have confl: \<open>conflicting T = Some {#}\<close>
    using no_step_cdcl_bab_stgy_empty_conflict[OF ns' struct_T stgy_T] .

  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause (abs_state T)\<close> and
    alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (abs_state T)\<close>
    using struct_T unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def by fast+
  then have ent': \<open>set_mset (clauses T + conflicting_clss T) \<Turnstile>p {#}\<close>
    using confl unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def
    by auto

  show \<open>unsatisfiable (set_mset (clauses T + conflicting_clss T))\<close>
  proof
    assume \<open>satisfiable (set_mset (clauses T + conflicting_clss T))\<close>
    then obtain I where
      ent'': \<open>I \<Turnstile>sm clauses T + conflicting_clss T\<close> and
      tot: \<open>total_over_m I (set_mset (clauses T + conflicting_clss T))\<close> and
      \<open>consistent_interp I\<close>
      unfolding satisfiable_def
      by blast
    then show \<open>False\<close>
      using ent' 
      unfolding true_clss_cls_def by auto
  qed
qed

text \<open>First part of \cwref{theo:prop:cdclmmcorrect}{Theorem 2.15.6}\<close>
lemma full_cdcl_bab_stgy_no_conflicting_clause_unsat:
  assumes
    st: \<open>full cdcl_bab_stgy S T\<close> and
    all_struct: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> and
    opt_struct: \<open>cdcl_bab_struct_invs S\<close> and
    stgy_inv: \<open>cdcl_bab_stgy_inv S\<close> and
    [simp]: \<open>weight T = None\<close> and
    ent: \<open>cdcl\<^sub>W_learned_clauses_entailed_by_init S\<close>
  shows \<open>unsatisfiable (set_mset (init_clss S))\<close>
proof -
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (abs_state S)\<close> and
    \<open>conflicting_clss T = {#}\<close>
    using ent
    by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def
      cdcl\<^sub>W_learned_clauses_entailed_by_init_def abs_state_def cdcl\<^sub>W_restart_mset_state
      conflicting_clss_def conflicting_clauses_def)
  then show ?thesis
    using full_cdcl_bab_stgy_no_conflicting_clss_unsat[OF _ st all_struct
     stgy_inv] by (auto simp: can_always_improve)
qed

definition annotation_is_model where
  \<open>annotation_is_model S \<longleftrightarrow>
     (weight S \<noteq> None \<longrightarrow> set_mset (the (weight S)) \<Turnstile>sm init_clss S)\<close>

lemma cdcl_bab_annotation_is_model:
  \<open>cdcl_bab S T \<Longrightarrow> annotation_is_model S \<Longrightarrow> annotation_is_model T\<close>
  by (cases rule: cdcl_bab.cases, assumption)
    (auto simp: conflict.simps annotation_is_model_def
      conflict_opt.simps ocdcl\<^sub>W_o.simps ocdcl\<^sub>W_bj.simps obacktrack.simps
      skip.simps resolve.simps decide.simps true_annots_true_cls lits_of_def
      propagate.simps improve.simps is_improving_int_def)

lemma rtranclp_cdcl_bab_annotation_is_model:
  \<open>cdcl_bab\<^sup>*\<^sup>* S T \<Longrightarrow> annotation_is_model S \<Longrightarrow> annotation_is_model T\<close>
  by (induction rule: rtranclp_induct)
    (auto simp: cdcl_bab_annotation_is_model)

lemma weight_init_state2[simp]: \<open>weight (init_state S) = None\<close> and
  conflicting_clss_init_state[simp]:
    \<open>conflicting_clss (init_state N) = {#}\<close>
  unfolding weight_def
  conflicting_clss_def conflicting_clauses_def
  by (auto simp: weight_init_state)

text \<open>\cwref{theo:prop:cdclmmcorrect}{Theorem 2.15.6}\<close>
theorem full_cdcl_bab_stgy_no_conflicting_clause_from_init_state:
  assumes
    st: \<open>full cdcl_bab_stgy (init_state N) T\<close> and
    dist: \<open>distinct_mset_mset N\<close> and
    annot: \<open>annotation_is_model S\<close>
  shows
    \<open>weight T = None \<Longrightarrow> unsatisfiable (set_mset N)\<close> and
    \<open>weight T \<noteq> None \<Longrightarrow> set_mset (the (weight T)) \<Turnstile>sm N\<close> and
    \<open>distinct_mset I \<Longrightarrow> consistent_interp (set_mset I) \<Longrightarrow> atms_of I = atms_of_mm N \<Longrightarrow>
      set_mset I \<Turnstile>sm N \<Longrightarrow> \<rho> I \<ge> \<rho>' (weight T)\<close>
proof -
  let ?S = \<open>init_state N\<close>
  have \<open>distinct_mset C\<close> if \<open>C \<in># N\<close> for C
    using dist that by (auto simp: distinct_mset_set_def dest: multi_member_split)
  then have dist: \<open>distinct_mset_mset (N)\<close>
    by (auto simp: distinct_mset_set_def)
  then have [simp]: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv ([], N, {#}, None)\<close>
    unfolding init_state.simps[symmetric]
    by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
  moreover have [simp]: \<open>cdcl_bab_struct_invs ?S\<close>
    by (auto simp: cdcl_bab_struct_invs_def conflicting_clss_def conflicting_clauses_def)
  moreover have [simp]: \<open>cdcl_bab_stgy_inv ?S\<close>
    by (auto simp: cdcl_bab_stgy_inv_def conflict_is_false_with_level_def
      no_smaller_improve_def)
  moreover have ent: \<open>cdcl\<^sub>W_learned_clauses_entailed_by_init ?S\<close>
    by (auto simp: cdcl\<^sub>W_learned_clauses_entailed_by_init_def)
  moreover have [simp]: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state (init_state N))\<close>
    unfolding CDCL_W_Abstract_State.init_state.simps abs_state_def
    by auto
  ultimately show \<open>weight T = None \<Longrightarrow> unsatisfiable (set_mset N)\<close>
    using full_cdcl_bab_stgy_no_conflicting_clause_unsat[OF st]
    by auto
  have \<open>annotation_is_model ?S\<close>
    by (auto simp: annotation_is_model_def)
  then have \<open>annotation_is_model T\<close>
    using rtranclp_cdcl_bab_annotation_is_model[of ?S T] st
    unfolding full_def by (blast dest: rtranclp_cdcl_bab_stgy_cdcl_bab)
  moreover have \<open>init_clss T = N\<close>
    using rtranclp_cdcl_bab_no_more_init_clss[of ?S T] st
    unfolding full_def by (auto dest: rtranclp_cdcl_bab_stgy_cdcl_bab)
  ultimately show \<open>weight T \<noteq> None \<Longrightarrow> set_mset (the (weight T)) \<Turnstile>sm N\<close>
    by (auto simp: annotation_is_model_def)

  show \<open>distinct_mset I \<Longrightarrow> consistent_interp (set_mset I) \<Longrightarrow> atms_of I = atms_of_mm N \<Longrightarrow>
      set_mset I \<Turnstile>sm N \<Longrightarrow> \<rho> I \<ge> \<rho>' (weight T)\<close>
    using full_cdcl_bab_stgy_larger_or_equal_weight[of ?S T I] st unfolding full_def
    by auto
qed



end


locale optimal_encoding_opt = conflict_driven_clause_learning\<^sub>W_optimal_weight
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
    \<rho>
    update_additional_info
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

    init_state :: "'v clauses \<Rightarrow> 'st" and
    \<rho> :: \<open>'v clause \<Rightarrow> nat\<close> and
    update_additional_info :: \<open>'v clause option \<times> 'b \<Rightarrow> 'st \<Rightarrow> 'st\<close> +
  fixes \<Sigma> \<Sigma>' :: \<open>'v set\<close> and
    new_vars :: \<open>'v \<Rightarrow> 'v \<times> 'v \<times> 'v\<close>
begin

abbreviation replacement_pos :: \<open>'v \<Rightarrow> 'v\<close> ("(_)\<^sup>\<mapsto>\<^sup>+" 100) where
  \<open>replacement_pos A \<equiv> (fst(new_vars A))\<close>

abbreviation replacement_neg :: \<open>'v \<Rightarrow> 'v\<close> ("(_)\<^sup>\<mapsto>\<^sup>-" 100) where
  \<open>replacement_neg A \<equiv> (fst(snd(new_vars A)))\<close>


abbreviation additional_atm :: \<open>'v \<Rightarrow> 'v\<close> where
  \<open>additional_atm A \<equiv>  (snd(snd(new_vars A)))\<close>
abbreviation additional_var :: \<open>'v \<Rightarrow> 'v literal\<close> where
  \<open>additional_var A \<equiv> Pos (additional_atm A)\<close>


fun encode_lit where
  \<open>encode_lit (Pos A) = (if A \<in> \<Sigma>' then Pos (replacement_pos A) else Pos A)\<close> |
  \<open>encode_lit (Neg A) = (if A \<in> \<Sigma>' then Pos (replacement_neg A) else Neg A)\<close>

lemma encode_lit_alt_def:
  \<open>encode_lit A = (if atm_of A \<in> \<Sigma>'
    then Pos (if is_pos A then replacement_pos (atm_of A) else replacement_neg (atm_of A))
    else A)\<close>
  by (cases A) auto
  
definition encode_clause :: \<open>'v clause \<Rightarrow> 'v clause\<close> where
  \<open>encode_clause C = encode_lit `# C\<close>

lemma encode_clause_simp[simp]:
  \<open>encode_clause {#} = {#}\<close>
  \<open>encode_clause (add_mset A C) = add_mset (encode_lit A) (encode_clause C)\<close>
  \<open>encode_clause (C + D) = encode_clause C + encode_clause D\<close>
  by (auto simp: encode_clause_def)

definition encode_clauses :: \<open>'v clauses \<Rightarrow> 'v clauses\<close> where
  \<open>encode_clauses C = encode_clause `# C\<close>

definition additional_constraint :: \<open>'v \<Rightarrow> 'v clauses\<close> where
  \<open>additional_constraint A =
     {#{#Neg (A\<^sup>\<mapsto>\<^sup>+), Pos A#},
       {#Neg (A\<^sup>\<mapsto>\<^sup>+), additional_var A#},
       {#-additional_var A, -Pos A, Pos (A\<^sup>\<mapsto>\<^sup>+)#},
       {#Neg (A\<^sup>\<mapsto>\<^sup>-), Neg A#},
       {#Neg (A\<^sup>\<mapsto>\<^sup>-), additional_var A#},
       {#-additional_var A, -Neg A, Pos (A\<^sup>\<mapsto>\<^sup>-)#}#}\<close>

definition additional_constraints :: \<open>'v clauses\<close> where
  \<open>additional_constraints = \<Union>#(additional_constraint `# (mset_set \<Sigma>'))\<close>

definition preprocessed_clss :: \<open>'v clauses \<Rightarrow> 'v clauses\<close> where
  \<open>preprocessed_clss N = encode_clauses N + additional_constraints\<close>

definition postp :: \<open>'v partial_interp \<Rightarrow> 'v partial_interp\<close> where
  \<open>postp I =
     {A \<in> I. atm_of A \<notin> \<Sigma>'} \<union> {A \<in> I. atm_of A \<in> \<Sigma>' \<and> additional_var (atm_of A) \<in> I}\<close>

lemma preprocess_clss_model_additional_variables:
  assumes \<open>I \<Turnstile>sm preprocessed_clss N\<close> and
    \<open>A \<in> \<Sigma>'\<close> and
    \<open>finite \<Sigma>'\<close> and
    cons: \<open>consistent_interp I\<close>
  shows
    \<open>Pos (A\<^sup>\<mapsto>\<^sup>+) \<in>I \<longleftrightarrow> (additional_var A \<in> I \<and> Pos A \<in> I)\<close> (is ?A) and
    \<open>Pos (A\<^sup>\<mapsto>\<^sup>-) \<in>I \<longleftrightarrow> (additional_var A \<in> I \<and> Neg A \<in> I)\<close> (is ?B)
proof -
  have H: \<open>A \<in> I \<Longrightarrow> -A \<notin> I\<close> for A
    using assms cons by (auto simp: consistent_interp_def)
  show ?A ?B
    using assms H[of \<open>Pos A\<close>] H[of \<open>Neg A\<close>] H[of \<open>Pos (A\<^sup>\<mapsto>\<^sup>+)\<close>]  H[of \<open>Neg (A\<^sup>\<mapsto>\<^sup>+)\<close>]
      H[of \<open>Neg (additional_atm A)\<close>] H[of \<open>Pos (additional_atm A)\<close>]
       H[of \<open>Pos (A\<^sup>\<mapsto>\<^sup>-)\<close>]  H[of \<open>Neg (A\<^sup>\<mapsto>\<^sup>-)\<close>]
    multi_member_split[of A \<open>mset_set \<Sigma>'\<close>]
    by (auto simp: preprocessed_clss_def additional_constraints_def true_clss_def
      additional_constraint_def ball_Un)
qed

lemma encode_clause_iff:
  assumes
    \<open>\<And>A. A \<in> \<Sigma>' \<Longrightarrow> Pos A \<in> I \<longleftrightarrow> Pos (replacement_pos A) \<in> I\<close>
    \<open>\<And>A. A \<in> \<Sigma>' \<Longrightarrow> Neg A \<in> I \<longleftrightarrow> Pos (replacement_neg A) \<in> I\<close>
  shows \<open>I \<Turnstile> encode_clause C \<longleftrightarrow> I \<Turnstile> C\<close>
  using assms
  apply (induction C)
  subgoal by auto
  subgoal for A C
    by (cases A)
      (auto simp: encode_clause_def encode_lit_alt_def split: if_splits)
  done

lemma encode_clauses_iff:
  assumes
    \<open>\<And>A. A \<in> \<Sigma>' \<Longrightarrow> Pos A \<in> I \<longleftrightarrow> Pos (replacement_pos A) \<in> I\<close>
    \<open>\<And>A. A \<in> \<Sigma>' \<Longrightarrow> Neg A \<in> I \<longleftrightarrow> Pos (replacement_neg A) \<in> I\<close>
  shows \<open>I \<Turnstile>m encode_clauses C \<longleftrightarrow> I \<Turnstile>m C\<close>
  using encode_clause_iff[OF assms]
  by (auto simp: encode_clauses_def true_cls_mset_def)


end


locale optimal_encoding = optimal_encoding_opt
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
    \<rho>
    update_additional_info
    \<Sigma> \<Sigma>'
    new_vars
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

    init_state :: "'v clauses \<Rightarrow> 'st" and
    \<rho> :: \<open>'v clause \<Rightarrow> nat\<close> and
    update_additional_info :: \<open>'v clause option \<times> 'b \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    \<Sigma> \<Sigma>' :: \<open>'v set\<close> and
    new_vars :: \<open>'v \<Rightarrow> 'v \<times> 'v \<times> 'v\<close> +
  assumes
    finite_\<Sigma>:
      \<open>finite \<Sigma>'\<close> and
    \<Sigma>'_\<Sigma>:
      \<open>\<Sigma>' \<subseteq> \<Sigma>\<close> and
    new_vars_pos:
      \<open>A \<in> \<Sigma>' \<Longrightarrow> (replacement_pos A) \<notin> \<Sigma>\<close> and
    new_vars_neg:
      \<open>A \<in> \<Sigma>' \<Longrightarrow> (replacement_neg A) \<notin> \<Sigma>\<close> and
    new_vars_addition_var:
      \<open>A \<in> \<Sigma>' \<Longrightarrow> additional_atm A \<notin> \<Sigma>\<close> and
    new_vars_dist:
      \<open>A \<in> \<Sigma>' \<Longrightarrow> B \<in> \<Sigma>' \<Longrightarrow> A \<noteq> B \<Longrightarrow> replacement_pos A \<noteq> replacement_pos B\<close>
      \<open>A \<in> \<Sigma>' \<Longrightarrow> B \<in> \<Sigma>' \<Longrightarrow> replacement_pos A \<noteq> replacement_neg B\<close>
      \<open>A \<in> \<Sigma>' \<Longrightarrow> B \<in> \<Sigma>' \<Longrightarrow> A \<noteq> B \<Longrightarrow> replacement_neg A \<noteq> replacement_neg B\<close>
      \<open>A \<in> \<Sigma>' \<Longrightarrow> B \<in> \<Sigma>' \<Longrightarrow> replacement_pos A \<noteq> additional_atm B\<close>
      \<open>A \<in> \<Sigma>' \<Longrightarrow> B \<in> \<Sigma>' \<Longrightarrow> replacement_neg A \<noteq> additional_atm B\<close>
      \<open>A \<in> \<Sigma>' \<Longrightarrow> B \<in> \<Sigma>' \<Longrightarrow> A \<noteq> B \<Longrightarrow> additional_atm A \<noteq> additional_atm B\<close>
begin

lemma consistent_interp_postp:
  \<open>consistent_interp I \<Longrightarrow> consistent_interp (postp I)\<close>
  by (auto simp: consistent_interp_def postp_def)

text \<open>The reverse of the previous theorem does not hold due to the filtering on the variables of
  \<^term>\<open>\<Sigma>'\<close>. One example of version that holds:\<close>
lemma
  assumes \<open>A \<in> \<Sigma>'\<close>
  shows \<open>consistent_interp (postp {Pos A , Neg A})\<close> and
    \<open>\<not>consistent_interp {Pos A, Neg A}\<close>
  using assms \<Sigma>'_\<Sigma>
  using new_vars_addition_var
  by (auto simp: consistent_interp_def postp_def uminus_lit_swap)

text \<open>Some more restricted version of the reverse hold, like:\<close>
lemma consistent_interp_postp_iff:
  \<open>atm_of ` I \<subseteq> \<Sigma> - \<Sigma>' \<Longrightarrow> consistent_interp I \<longleftrightarrow> consistent_interp (postp I)\<close>
  by (auto simp: consistent_interp_def postp_def)

lemma satisfiable_preprocessed_clss:
  assumes \<Sigma>: \<open>atms_of_mm N = \<Sigma>\<close> and
    sat: \<open>satisfiable (set_mset N)\<close>
  shows \<open>satisfiable (set_mset (preprocessed_clss N))\<close>
proof -
  obtain I where
    I_N: \<open>I \<Turnstile>sm N\<close> and
    cons: \<open>consistent_interp I\<close> and
    \<open>total_over_m I (set_mset N)\<close> and
    atm: \<open>atm_of ` I = atms_of_mm N\<close>
    using sat unfolding satisfiable_def_min by auto

  let ?I = \<open>I
     \<union> (Pos o replacement_pos) ` {A \<in> \<Sigma>'. Pos A \<in> I}
       \<union> (Neg o replacement_pos) ` {A \<in> \<Sigma>'. Neg A \<in> I}
    \<union> (Pos o replacement_neg) ` {A \<in> \<Sigma>'. Neg A \<in> I}
       \<union> (Neg o replacement_neg) ` {A \<in> \<Sigma>'. Pos A \<in> I}
    \<union> additional_var ` \<Sigma>'\<close>
  have [iff]: \<open>Pos (A\<^sup>\<mapsto>\<^sup>-) \<notin> I\<close> \<open>Pos (A\<^sup>\<mapsto>\<^sup>+) \<notin> I\<close> \<open>additional_var A \<notin> I\<close> \<open>Neg (additional_atm A) \<notin> I\<close>
     \<open>Neg (A\<^sup>\<mapsto>\<^sup>-) \<notin> I\<close> \<open>Neg (A\<^sup>\<mapsto>\<^sup>+) \<notin> I\<close>  if \<open>A \<in> \<Sigma>'\<close> for A
    using atm new_vars_neg[of A] new_vars_pos[of A] that new_vars_addition_var[of A]
    unfolding \<Sigma> by force+
  have [iff]: \<open>A\<^sup>\<mapsto>\<^sup>- \<noteq> x\<^sup>\<mapsto>\<^sup>+\<close> \<open>A\<^sup>\<mapsto>\<^sup>+ \<noteq> x\<^sup>\<mapsto>\<^sup>-\<close>
      \<open>A\<^sup>\<mapsto>\<^sup>- \<noteq> additional_atm x\<close>
      \<open>A\<^sup>\<mapsto>\<^sup>+ \<noteq> additional_atm x\<close>
      \<open>additional_atm x \<noteq> A\<^sup>\<mapsto>\<^sup>-\<close>
      \<open>additional_atm x \<noteq> A\<^sup>\<mapsto>\<^sup>+\<close>
      \<open>A\<^sup>\<mapsto>\<^sup>- = x\<^sup>\<mapsto>\<^sup>- \<longleftrightarrow> A = x\<close>
      \<open>A\<^sup>\<mapsto>\<^sup>+ = x\<^sup>\<mapsto>\<^sup>+ \<longleftrightarrow> A = x\<close>
      if \<open>A \<in> \<Sigma>'\<close>  \<open>x \<in> \<Sigma>'\<close> for A x
    using \<Sigma>'_\<Sigma> new_vars_pos new_vars_neg new_vars_dist[of A x] new_vars_dist[of x A]
      new_vars_addition_var that
    by (cases \<open>A = x\<close>; auto simp: comp_def)+

  have tot: \<open>Neg A \<in> I \<or> Pos A \<in> I\<close> if \<open>A \<in> \<Sigma>'\<close> for A
    using that atm \<Sigma>'_\<Sigma> unfolding \<Sigma> atms_of_s_def[symmetric]
    by fastforce
  have [iff]: \<open>additional_var A \<notin> I\<close> \<open>Pos (replacement_pos A) \<notin> I\<close> \<open>Neg (replacement_pos A) \<notin> I\<close>
    \<open>Pos (replacement_neg A) \<notin> I\<close> \<open>Neg (replacement_neg A) \<notin> I\<close> if \<open>A \<in> \<Sigma>'\<close> for A
    using that atm \<Sigma>'_\<Sigma> unfolding \<Sigma> atms_of_s_def[symmetric]
    by simp_all
  have \<open>?I \<Turnstile>m additional_constraint A\<close> if \<open>A \<in> \<Sigma>'\<close> for A
    using that tot[OF that] unfolding true_cls_mset_def additional_constraint_def
    by (auto simp: additional_constraints_def 
          additional_constraint_def finite_\<Sigma> comp_def)
  then have \<open>?I \<Turnstile>m additional_constraints\<close>
    by (auto simp: additional_constraints_def true_cls_mset_def finite_\<Sigma>)
  moreover have \<open>?I \<Turnstile>m encode_clauses N\<close>
    apply (subst encode_clauses_iff)
    subgoal for A using \<Sigma>'_\<Sigma> new_vars_pos new_vars_neg new_vars_addition_var
      by (auto simp: comp_def)
    subgoal for A using \<Sigma>'_\<Sigma> new_vars_pos new_vars_neg
      by (auto simp: comp_def)
    subgoal using I_N by auto
    done
  ultimately have \<open>?I \<Turnstile>m preprocessed_clss N\<close>
    by (auto simp: preprocessed_clss_def)

  moreover have \<open>consistent_interp ?I\<close>
    using cons
    by (auto simp: consistent_interp_def uminus_lit_swap)
  ultimately show ?thesis
    by auto
qed

end

end
