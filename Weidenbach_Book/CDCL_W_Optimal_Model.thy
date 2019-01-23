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
\shortrules{Backtrack}{$(M_1K^{i+1}M_2;N;U;k;D\lor L;O)$}{$(M_1L^{D\vee L};N;U\cup\{D\lor L\};i;
  \top;O)$}

provided $L$ is of level $k$ and $D$ is of level $i$.

\bigskip
\shortrules{Improve}{$(M;N;U;k;\top;O)$}{$(M;N;U;k;\top;M)$}

provided $M\models N$ and $O=\epsilon$ or $\operatorname{cost}(M)<\operatorname{cost}(O)$.
}
{This calculus does not always find the model with minimum cost. Take for example the following
  cost function:
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

\shortrules{conflictOpt}{}{$({\neg P}^{\neg P}Q^{P\lor Q}, N, \{\neg P\}, P \lor \neg Q, (\neg P\,
  Q, 2))$}

\shortrules{resolve}{}{$({\neg P}^{\neg P}, N, \{\neg P\}, P, (\neg P\, Q, 2))$}

\shortrules{resolve}{}{$(\epsilon, N, \{\neg P\}, \bot, (\neg P\, Q, 3))$}


However, the optimal model is $Q$.
}
\<close>

text \<open>
  The idea of the proof (explained of the example of the optimising CDCL) is the following:

  \<^enum> We start with a calculus OCDCL on \<^term>\<open>(M, N, U, D, Op)\<close>.

  \<^enum> This extended to a state \<^term>\<open>(M, N + all_models_of_higher_cost, U, D, Op)\<close>.

  \<^enum> Each transition step of OCDCL is mapped to a step in CDCL over the abstract state. The abstract
    set of clauses might be unsatisfiable, but we only use it to prove the invariants on the
    state. Only adding clause cannot be mapped to a transition over the abstract state, but adding
    clauses does not break the invariants (as long as the additional clauses do not contain
    duplicate literals).

  \<^enum> The last proofs are done over CDCLopt.

We abstract about how the optimisation is done in the locale below: We define a calculus
\<^term>\<open>cdcl_bab\<close> (for branch-and-bounds). It is parametrised by how the conflicting clauses are
generated and the improvement criterion.

We later instantiate it with the optimisation calculus from Weidenbach's book.
\<close>

definition negate_ann_lits :: "('v, 'v clause) ann_lits \<Rightarrow> 'v literal multiset" where
  \<open>negate_ann_lits M = (\<lambda>L. - lit_of L) `# (mset M)\<close>

text \<open>Pointwise negation of a clause:\<close>
definition pNeg :: \<open>'v clause \<Rightarrow> 'v clause\<close> where
  \<open>pNeg C = {#-D. D \<in># C#}\<close>

lemma pNeg_simps:
  \<open>pNeg (add_mset A C) = add_mset (-A) (pNeg C)\<close>
  \<open>pNeg (C + D) = pNeg C + pNeg D\<close>
  by (auto simp: pNeg_def)

lemma atms_of_pNeg[simp]: \<open>atms_of (pNeg C) = atms_of C\<close>
  by (auto simp: pNeg_def atms_of_def image_image)

lemma negate_ann_lits_pNeg_lit_of: \<open>negate_ann_lits = pNeg o image_mset lit_of o mset\<close>
  by (intro ext) (auto simp: negate_ann_lits_def pNeg_def)

lemma negate_ann_lits_empty_iff: \<open>negate_ann_lits M \<noteq> {#} \<longleftrightarrow> M \<noteq> []\<close>
  by (auto simp: negate_ann_lits_def)

lemma atms_of_negate_ann_lits[simp]: \<open>atms_of (negate_ann_lits M) = atm_of ` (lits_of_l M)\<close>
  unfolding negate_ann_lits_def lits_of_def atms_of_def by (auto simp: image_image)

lemma tautology_pNeg[simp]:
  \<open>tautology (pNeg C) \<longleftrightarrow> tautology C\<close>
  by (auto 5 5 simp: tautology_decomp pNeg_def
      uminus_lit_swap add_mset_eq_add_mset eq_commute[of \<open>Neg _\<close> \<open>- _\<close>]  eq_commute[of \<open>Pos _\<close> \<open>- _\<close>]
    dest!: multi_member_split)

lemma (in -) pNeg_convolution[simp]:
  \<open>pNeg (pNeg C) = C\<close>
  by (auto simp: pNeg_def)

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


lemma conflicting_clause_state_eq[state_simp, simp]:
  \<open>S \<sim> T \<Longrightarrow> conflicting_clss S = conflicting_clss T\<close>
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
  conflicting_clss_add_learned_cls[simp]:
    \<open>conflicting_clss (add_learned_cls D S) = conflicting_clss S\<close> and
  conflicting_clss_update_conflicting[simp]:
    \<open>conflicting_clss (update_conflicting E S) = conflicting_clss S\<close>
  unfolding conflicting_clss_def by auto

inductive conflict_opt :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S T :: 'st where
conflict_opt_rule:
  \<open>conflict_opt S T\<close>
  if
    \<open>negate_ann_lits (trail S) \<in># conflicting_clss S\<close>
    \<open>conflicting S = None\<close>
    \<open>T \<sim> update_conflicting (Some (negate_ann_lits (trail S))) S\<close>

inductive_cases conflict_optE: \<open>conflict_opt S T\<close>

inductive improve :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
improve_rule:
  \<open>improve S T\<close>
  if
    \<open>is_improving (trail S) S\<close> and
    \<open>conflicting S = None\<close> and
    \<open>T \<sim> update_weight_information (trail S) S\<close>

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
  case (improve_rule T)
  moreover
  have \<open>all_decomposition_implies
     (set_mset (init_clss S) \<union> set_mset (conflicting_clss S) \<union> set_mset (learned_clss S))
     (get_all_ann_decomposition (trail S)) \<Longrightarrow>
    all_decomposition_implies
     (set_mset (init_clss S) \<union> set_mset (conflicting_clss (update_weight_information (trail S) S)) \<union>
      set_mset (learned_clss S))
     (get_all_ann_decomposition (trail S))\<close>
      apply (rule all_decomposition_implies_mono)
      using improve_rule conflicting_clss_update_weight_information_mono[of S \<open>trail S\<close>] inv
      by (auto dest: multi_member_split)
    ultimately show ?case
      using conflicting_clss_update_weight_information_mono[of S \<open>trail S\<close>]
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
    no_step propagate S \<and> no_step conflict S\<close>

text \<open>We use a slighlty generalised form of backtrack to make conflict clause minimisation possible.\<close>
inductive obacktrack :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
obacktrack_rule: \<open>
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
  obacktrack S T\<close>

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
    (auto simp: improve.simps conflict.simps propagate.simps
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
    (force simp: improve.simps conflict.simps propagate.simps
      conflict_opt.simps ocdcl\<^sub>W_o.simps obacktrack.simps skip.simps resolve.simps
      ocdcl\<^sub>W_bj.simps decide.simps cdcl_bab_struct_invs_def)+

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
  subgoal using struct_inv unfolding distinct_cdcl\<^sub>W_state_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
    by (auto simp: abs_state_def cdcl\<^sub>W_restart_mset_state)
  subgoal using struct_inv unfolding cdcl\<^sub>W_conflicting_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
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
  subgoal using confl_inv unfolding distinct_cdcl\<^sub>W_state_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
      cdcl\<^sub>W_restart_mset.no_smaller_confl_def
    by (auto simp: abs_state_def cdcl\<^sub>W_restart_mset_state clauses_def)
  done

declare cdcl\<^sub>W_restart_mset.conflict_is_false_with_level_def [simp del]

lemma improve_conflict_is_false_with_level:
  assumes \<open>improve S T\<close> and \<open>conflict_is_false_with_level S\<close>
  shows \<open>conflict_is_false_with_level T\<close>
  using assms
proof induction
  case (improve_rule T)
  then show ?case
    by (auto simp: cdcl\<^sub>W_restart_mset.conflict_is_false_with_level_def
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
    by (auto simp: no_smaller_confl_def improve.simps)
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

  have \<open>resolve S T\<close>
    using resolve.intros[of S L C D T] resolve
    by auto
  then have \<open>cdcl\<^sub>W_restart_mset.resolve (abs_state S) (abs_state T)\<close>
    by (simp add: resolve_resolve)
  moreover have \<open>cdcl\<^sub>W_restart_mset.conflict_is_false_with_level (abs_state S)\<close>
    using confl_inv
    by (auto simp: cdcl\<^sub>W_restart_mset.conflict_is_false_with_level_def
      conflict_is_false_with_level_def abs_state_def cdcl\<^sub>W_restart_mset_state)
  ultimately have \<open>cdcl\<^sub>W_restart_mset.conflict_is_false_with_level (abs_state T)\<close>
    using  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o_conflict_is_false_with_level_inv[of \<open>abs_state S\<close> \<open>abs_state T\<close>]
    lev confl_inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by (auto dest!: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o.intros
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_bj.intros)
  then show \<open>?case\<close>
    by (auto simp: cdcl\<^sub>W_restart_mset.conflict_is_false_with_level_def
      conflict_is_false_with_level_def abs_state_def cdcl\<^sub>W_restart_mset_state)
next
  case (skip L C' M D T) note tr_S = this(1) and D = this(2) and T = this(5)
  have \<open>skip S T\<close>
    using skip.intros[of S L C' M D T] skip
    by auto
  then have \<open>cdcl\<^sub>W_restart_mset.skip (abs_state S) (abs_state T)\<close>
    by (simp add: skip_skip)
  moreover have \<open>cdcl\<^sub>W_restart_mset.conflict_is_false_with_level (abs_state S)\<close>
    using confl_inv
    by (auto simp: cdcl\<^sub>W_restart_mset.conflict_is_false_with_level_def
      conflict_is_false_with_level_def abs_state_def cdcl\<^sub>W_restart_mset_state)
  ultimately have \<open>cdcl\<^sub>W_restart_mset.conflict_is_false_with_level (abs_state T)\<close>
    using  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o_conflict_is_false_with_level_inv[of \<open>abs_state S\<close> \<open>abs_state T\<close>]
    lev confl_inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by (auto dest!: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o.intros
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_bj.intros)
  then show \<open>?case\<close>
    by (auto simp: cdcl\<^sub>W_restart_mset.conflict_is_false_with_level_def
      conflict_is_false_with_level_def abs_state_def cdcl\<^sub>W_restart_mset_state)
next
  case backtrack
  then show ?case
    by (auto split: if_split_asm simp: cdcl\<^sub>W_M_level_inv_decomp lev conflict_is_false_with_level_def)
qed (auto simp: conflict_is_false_with_level_def)


lemma cdcl_bab_stgy_conflict_is_false_with_level:
  assumes \<open>cdcl_bab_stgy S T\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> and
    \<open>no_smaller_confl S\<close> and
    \<open>conflict_is_false_with_level S\<close>
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
  have \<open>is_improving (trail S) S\<close>
    using either_all_false_or_earliest_decomposition[where P = \<open>\<lambda>M. is_improving M S\<close> and
        L = \<open>trail S\<close>]
    using imp by auto
  then show ?thesis
    unfolding Ex_def
    using confl by (auto simp: improve.simps)
qed

definition cdcl_bab_stgy_inv :: "'st \<Rightarrow> bool" where
  \<open>cdcl_bab_stgy_inv S \<longleftrightarrow> conflict_is_false_with_level S \<and> no_smaller_confl S\<close>

lemma cdcl_bab_stgy_invD:
  shows \<open>cdcl_bab_stgy_inv S \<longleftrightarrow> cdcl\<^sub>W_stgy_invariant S\<close>
  unfolding cdcl\<^sub>W_stgy_invariant_def cdcl_bab_stgy_inv_def
  by auto

lemma cdcl_bab_stgy_stgy_inv:
  \<open>cdcl_bab_stgy S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S) \<Longrightarrow>
    cdcl_bab_stgy_inv S \<Longrightarrow> cdcl_bab_stgy_inv T\<close>
  using cdcl\<^sub>W_stgy_cdcl\<^sub>W_stgy_invariant[of S T]
  unfolding cdcl_bab_stgy_inv_def
  using cdcl_bab_stgy_conflict_is_false_with_level cdcl_bab_stgy_no_smaller_confl
  by blast

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

lemma wf_cdcl_bab:
  assumes improve: \<open>\<And>S T. improve S T \<Longrightarrow> (\<nu> (weight T), \<nu> (weight S)) \<in> R\<close> and
    wf_R: \<open>wf R\<close>
  shows \<open>wf {(T, S). cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S) \<and> cdcl_bab S T}\<close>
    (is \<open>wf ?A\<close>)
proof -
  let ?R = \<open>{(T, S). (\<nu> (weight T), \<nu> (weight S)) \<in> R}\<close>

  have \<open>wf {(T, S).  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv S \<and> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W S T}\<close>
    by (rule cdcl\<^sub>W_restart_mset.wf_cdcl\<^sub>W)
  from wf_if_measure_f[OF this, of abs_state]
  have wf: \<open>wf {(T, S).  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S) \<and>
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W (abs_state S) (abs_state T) \<and> weight S = weight T}\<close>
    (is \<open>wf ?CDCL\<close>)
    by (rule wf_subset) auto
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
    by (simp add: all_struct)
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


text \<open>This locales includes only the assumption we make on the weight function.\<close>
locale ocdcl_weight =
  fixes
    \<rho> :: \<open>'v clause \<Rightarrow> nat\<close>
  assumes
    \<rho>_mono: \<open>A \<subseteq># B \<Longrightarrow> \<rho> A \<le> \<rho> B\<close>
begin

lemma \<rho>_empty_simp[simp]: \<open>\<rho> A \<ge> \<rho> {#}\<close> \<open>\<not>\<rho> A < \<rho> {#}\<close>  \<open>\<rho> A \<le> \<rho> {#} \<longleftrightarrow> \<rho> A = \<rho> {#}\<close>
  using \<rho>_mono[of \<open>{#}\<close> A]
  by auto

end


text \<open>This is one of the version of the weight functions used by Christoph Weidenbach.\<close>
locale ocdcl_weight_WB =
  fixes
    \<nu> :: \<open>'v literal \<Rightarrow> nat\<close>
begin

definition \<rho> :: \<open>'v clause \<Rightarrow> nat\<close> where
  \<open>\<rho> M = (\<Sum>A \<in># M. \<nu> A)\<close>

sublocale ocdcl_weight \<rho>
  by (unfold_locales)
    (auto simp: \<rho>_def sum_image_mset_mono)

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
    init_state +
  ocdcl_weight \<rho>
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
    \<rho> :: \<open>'v clause \<Rightarrow> nat\<close>  +
  fixes
    update_additional_info :: \<open>'v clause option \<times> 'b \<Rightarrow> 'st \<Rightarrow> 'st\<close>
  assumes
    update_additional_info:
      \<open>state S = (M, N, U, C, K) \<Longrightarrow> state (update_additional_info K' S) = (M, N, U, C, K')\<close> and
    weight_init_state:
      \<open>\<And>N :: 'v clauses. fst (additional_info (init_state N)) = None\<close>
begin

definition update_weight_information :: \<open>('v, 'v clause) ann_lits \<Rightarrow> 'st \<Rightarrow> 'st\<close> where
  \<open>update_weight_information M S =
    update_additional_info (Some (lit_of `# mset M), snd (additional_info S)) S\<close>

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

abbreviation \<rho>' :: \<open>'v clause option \<Rightarrow> enat\<close> where
  \<open>\<rho>' w \<equiv> (case w of None \<Rightarrow> \<infinity> | Some w \<Rightarrow> \<rho> w)\<close>

definition is_improving_int :: "('v, 'v clause) ann_lits \<Rightarrow> 'v clauses \<Rightarrow> 'v clause option \<Rightarrow> bool" where
  \<open>is_improving_int M N w \<longleftrightarrow> enat (\<rho> (lit_of `# mset M)) < \<rho>' w \<and> M \<Turnstile>asm N \<and> no_dup M
    \<and> lit_of `# mset M \<in> simple_clss (atms_of_mm N) \<and>
    total_over_m (lits_of_l M) (set_mset N)\<close>

lemma distinct_mset_pNeg_iff[iff]: \<open>distinct_mset (pNeg x) \<longleftrightarrow> distinct_mset x\<close>
  unfolding pNeg_def
  by (rule distinct_image_mset_inj) (auto simp: inj_on_def)

definition too_heavy_clauses :: \<open>'v clauses \<Rightarrow> 'v clause option \<Rightarrow> 'v clauses\<close> where
  \<open>too_heavy_clauses M w = {#pNeg C | C \<in># mset_set (simple_clss (atms_of_mm M)). \<rho> C \<ge> \<rho>' w#}\<close>

definition conflicting_clauses :: "'v clauses \<Rightarrow> 'v clause option \<Rightarrow> 'v clauses" where
  \<open>conflicting_clauses M w =
    {#C \<in># mset_set (simple_clss (atms_of_mm M)). too_heavy_clauses M w \<Turnstile>pm C#}\<close>

lemma too_heavy_clauses_conflicting_clauses:
  \<open>C \<in># too_heavy_clauses M w \<Longrightarrow> C \<in># conflicting_clauses M w\<close>
  by (auto simp: conflicting_clauses_def too_heavy_clauses_def simple_clss_finite)
    (auto simp: simple_clss_def)

lemma too_heavy_clauses_contains_itself:
  \<open>M \<in> simple_clss (atms_of_mm N) \<Longrightarrow> pNeg M \<in># too_heavy_clauses N (Some M)\<close>
  by (auto simp: too_heavy_clauses_def simple_clss_finite)

lemma too_heavy_clause_None[simp]: \<open>too_heavy_clauses M None = {#}\<close>
  by (auto simp: too_heavy_clauses_def)

lemma
  atms_too_heavy_clauses_None:
    \<open>atms_of_mm (too_heavy_clauses M None) = {}\<close> and
  atms_too_heavy_clauses_Some:
    \<open>atms_of w \<subseteq> atms_of_mm M  \<Longrightarrow> distinct_mset w \<Longrightarrow> \<not>tautology w \<Longrightarrow>
      atms_of_mm (too_heavy_clauses M (Some w)) = atms_of_mm M\<close>
proof -
  show \<open>atms_of_mm (too_heavy_clauses M None) = {}\<close>
    by (auto simp: too_heavy_clauses_def)
  assume atms: \<open>atms_of w \<subseteq> atms_of_mm M\<close> and
    dist: \<open>distinct_mset w\<close> and
    taut: \<open>\<not>tautology w\<close>
  have \<open>atms_of_mm (too_heavy_clauses M (Some w)) \<subseteq> atms_of_mm M\<close>
    by (auto simp: too_heavy_clauses_def atms_of_ms_def simple_clss_finite)
      (auto simp: simple_clss_def)
  let ?w = \<open>w + Neg `# {#x \<in># mset_set (atms_of_mm M). x \<notin> atms_of w#}\<close>
  have [simp]: \<open>inj_on Neg A\<close> for A
    by (auto simp: inj_on_def)
  have [simp]: \<open>distinct_mset (uminus `# w)\<close>
    by (subst distinct_image_mset_inj)
      (auto simp: dist inj_on_def)
  have \<open>distinct_mset ?w\<close>
    using dist
    by (auto simp: distinct_mset_add distinct_image_mset_inj distinct_mset_mset_set uminus_lit_swap
      disjunct_not_in dest: multi_member_split)
  moreover have \<open>\<not>tautology (w + negs (mset_set {x \<in> atms_of_mm M. x \<notin> atms_of w}))\<close>
    by (auto simp: tautology_union taut uminus_lit_swap dest: multi_member_split)
  ultimately have \<open>?w \<in> (simple_clss (atms_of_mm M))\<close>
    using atms by (auto simp: simple_clss_def)
  moreover have \<open>\<rho> ?w \<ge> \<rho> w\<close>
    by (rule \<rho>_mono) auto
  ultimately have \<open>pNeg ?w \<in># too_heavy_clauses M (Some w)\<close>
    by (auto simp: too_heavy_clauses_def simple_clss_finite)
  then have \<open>atms_of_mm M \<subseteq> atms_of_mm (too_heavy_clauses M (Some w))\<close>
    by (auto dest!: multi_member_split)
  then show \<open>atms_of_mm (too_heavy_clauses M (Some w)) = atms_of_mm M\<close>
    using \<open>atms_of_mm (too_heavy_clauses M (Some w)) \<subseteq> atms_of_mm M\<close> by blast
qed

lemma (in -)true_clss_cls_tautology_iff:
  \<open>{} \<Turnstile>p a \<longleftrightarrow> tautology a\<close> (is \<open>?A \<longleftrightarrow> ?B\<close>)
proof
  assume ?A
  then have H: \<open>total_over_set I (atms_of a) \<Longrightarrow> consistent_interp I \<Longrightarrow> I \<Turnstile> a\<close> for I
    by (auto simp: true_clss_cls_def tautology_decomp add_mset_eq_add_mset
      dest!: multi_member_split)
  show ?B
    unfolding tautology_def
  proof (intro allI impI)
    fix I
    assume tot: \<open>total_over_set I (atms_of a)\<close>
    let ?Iinter = \<open>I \<inter> uminus ` I\<close>
    let ?I = \<open>I - ?Iinter \<union> Pos ` atm_of ` ?Iinter\<close>
    have \<open>total_over_set ?I (atms_of a)\<close>
      using tot by (force simp: total_over_set_def image_image simp flip: uminus_lit_swap
        simp: image_iff)
    moreover have \<open>consistent_interp ?I\<close>
      unfolding consistent_interp_def image_iff
      apply clarify
      subgoal for L
        apply (cases L)
        apply (auto simp: consistent_interp_def uminus_lit_swap image_iff)
	apply (case_tac xa; auto; fail)+
	done
      done
    ultimately have \<open>?I \<Turnstile> a\<close>
      using H[of ?I] by fast
    moreover have \<open>?I \<subseteq> I\<close>
      apply (rule)
      subgoal for x by (cases x; auto; rename_tac xb; case_tac xb; auto)
      done
    ultimately show \<open>I \<Turnstile> a\<close>
      by (blast intro: true_cls_mono_set_mset_l)
  qed
next
  assume ?B
  then show \<open>?A\<close>
    by (auto simp: true_clss_cls_def tautology_decomp add_mset_eq_add_mset
      dest!: multi_member_split)
qed

lemma entails_too_heavy_clauses_too_heavy_clauses:
  assumes
    \<open>consistent_interp I\<close> and
    tot: \<open>total_over_m I (set_mset (too_heavy_clauses M w))\<close> and
    \<open>I \<Turnstile>m too_heavy_clauses M w\<close> and
    w: \<open>w \<noteq> None \<Longrightarrow> atms_of (the w) \<subseteq> atms_of_mm M\<close>
      \<open>w \<noteq> None \<Longrightarrow> \<not>tautology (the w)\<close>
      \<open>w \<noteq> None \<Longrightarrow> distinct_mset (the w)\<close>
  shows \<open>I \<Turnstile>m conflicting_clauses M w\<close>
proof (cases w)
  case None
  have [simp]: \<open>{x \<in> simple_clss (atms_of_mm M). tautology x} = {}\<close>
    by (auto dest: simple_clssE)
  show ?thesis
    using None by (auto simp: conflicting_clauses_def true_clss_cls_tautology_iff
      simple_clss_finite)
next
  case w': (Some w')
  have \<open>x \<in># mset_set (simple_clss (atms_of_mm M)) \<Longrightarrow> total_over_set I (atms_of x)\<close> for x
    using tot w atms_too_heavy_clauses_Some[of w' M] unfolding w'
    by (auto simp: total_over_m_def simple_clss_finite total_over_set_alt_def
      dest!: simple_clssE)
  then show ?thesis
    using assms
    by (subst true_cls_mset_def)
      (auto simp: conflicting_clauses_def true_clss_cls_def
        dest!: spec[of _ I])
qed

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

lemma too_heavy_clauses_mono:
  \<open>\<rho> a > \<rho> (lit_of `# mset M) \<Longrightarrow> too_heavy_clauses N (Some a) \<subseteq>#
       too_heavy_clauses N (Some (lit_of `# mset M))\<close>
  by (auto simp: too_heavy_clauses_def multiset_filter_mono2
    intro!: multiset_filter_mono image_mset_subseteq_mono)

lemma is_improving_conflicting_clss_update_weight_information: \<open>is_improving M S \<Longrightarrow>
       conflicting_clss S \<subseteq># conflicting_clss (update_weight_information M S)\<close>
  using too_heavy_clauses_mono[of M \<open>the (weight S)\<close> \<open>(init_clss S)\<close>]
    true_clss_cls_subset
  by (cases \<open>weight S\<close>)
    (auto 7 5 simp: is_improving_int_def conflicting_clss_def conflicting_clauses_def
      simp: multiset_filter_mono2 le_less true_clss_cls_tautology_iff simple_clss_finite
      intro!: image_mset_subseteq_mono
      dest: simple_clssE
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
      negate_ann_lits_pNeg_lit_of image_iff dest: total_over_m_atms_incl
      intro!: true_clss_cls_in too_heavy_clauses_contains_itself)

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
  by (auto simp: conflicting_clss_def conflicting_clauses_def atms_of_ms_def
      cdcl\<^sub>W_restart_mset_state simple_clss_finite
    dest: simple_clssE)

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

lemma not_entailed_too_heavy_clauses_ge:
  \<open>C \<in> simple_clss (atms_of_mm N) \<Longrightarrow>
    \<not> too_heavy_clauses N w \<Turnstile>pm
      pNeg C \<Longrightarrow> \<not>\<rho> C \<ge> \<rho>' w\<close>
      using true_clss_cls_in[of \<open>pNeg C\<close> \<open>set_mset (too_heavy_clauses N w)\<close>]
      too_heavy_clauses_contains_itself
  by (auto simp: too_heavy_clauses_def simple_clss_finite
        image_iff)

lemma pNeg_simple_clss_iff[simp]:
  \<open>pNeg C \<in> simple_clss N \<longleftrightarrow> C \<in> simple_clss N\<close>
  by (auto simp: simple_clss_def)

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
    \<open>(lit_of `# mset (trail S)) \<in> simple_clss (atms_of_mm (init_clss S))\<close>
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
         simple_clss_finite subset_iff
       dest!: spec[of _ \<open>(lit_of `# mset (trail S))\<close>] dest: total_over_m_atms_incl
          true_clss_cls_in too_heavy_clauses_contains_itself
	  dest: not_entailed_too_heavy_clauses_ge)
  moreover have \<open>trail S \<Turnstile>asm init_clss S\<close>
    using ent by (auto simp: clauses_def)
  moreover have \<open>total_over_m (lits_of_l (trail S))  (set_mset (init_clss S))\<close>
    using total all_struct by (auto simp: total_over_m_def total_over_set_def
       cdcl\<^sub>W_all_struct_inv_def clauses_def
        no_strange_atm_def)
  ultimately show \<open>Ex (improve S)\<close>
    using improve.intros[of S \<open>update_weight_information (trail S) S\<close>] total H confl
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
    using tot cons ent(2) by auto
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
  case (improve_rule) note confl = this(2) and T = this(3)
  have alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (abs_state S)\<close> and
    lev: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (abs_state S)\<close>
    using all_struct unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast+
  then have atm_trail: \<open>atms_of (lit_of `# mset (trail S)) \<subseteq> atms_of_mm (init_clss S)\<close>
    using alien by (auto simp: no_strange_atm_def lits_of_def atms_of_def)
  have dist2: \<open>distinct_mset (lit_of `# mset (trail S))\<close> and
    taut2: \<open>\<not> tautology (lit_of `# mset (trail S))\<close>
    using lev unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by (auto dest: no_dup_distinct no_dup_not_tautology)
  have tot2: \<open>total_over_m (set_mset I) (set_mset (init_clss S))\<close>
    using tot[symmetric]
    by (auto simp: total_over_m_def total_over_set_def atm_iff_pos_or_neg_lit)

  have 2: \<open>set_mset I \<Turnstile>m too_heavy_clauses (init_clss T) (weight T)\<close>
    unfolding true_cls_mset_def
  proof
    fix C
    assume \<open>C \<in># too_heavy_clauses (init_clss T) (weight T)\<close>
    then obtain x where
      [simp]: \<open>C = pNeg x\<close> and
      x: \<open>x \<in> simple_clss (atms_of_mm (init_clss T))\<close> and
      we: \<open>\<rho>' (weight T) \<le> enat (\<rho> x)\<close>
      unfolding too_heavy_clauses_def
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
    moreover have \<open>\<not>set_mset x \<subseteq> set_mset I\<close>
      using \<rho>_mono[of \<open>x\<close> I] we le T distinct_set_mset_eq_iff[of x I] simple_clssE[OF x] dist
      by (cases \<open>weight S\<close>) auto
    moreover have \<open>x \<noteq> {#}\<close>
      using we le T
      by (cases \<open>weight S\<close>) auto
    ultimately obtain L where
      L_x: \<open>L \<in># x\<close> and
      \<open>L \<notin># I\<close>
      by auto
    moreover have \<open>atms_of x \<subseteq> atms_of I\<close>
      using simple_clssE[OF x] tot T
      atm_iff_pos_or_neg_lit[of a I] atm_iff_pos_or_neg_lit[of a x]
      by (auto dest!: multi_member_split)
    ultimately have \<open>-L \<in># I\<close>
      using tot simple_clssE[OF x] atm_of_notin_atms_of_iff
      by auto
    then show \<open>set_mset I \<Turnstile> C\<close>
      using L_x by (auto simp: simple_clss_finite pNeg_def dest!: multi_member_split)
  qed
  then have \<open>set_mset I \<Turnstile>m conflicting_clauses (init_clss S) (weight (update_weight_information (trail S) S))\<close>
    apply -
    apply (rule entails_too_heavy_clauses_too_heavy_clauses)
    subgoal using cons by auto
    subgoal using tot tot2 dist2 atm_trail taut2
      by (auto simp: total_over_m_def atms_too_heavy_clauses_Some)
    subgoal
      using T by auto
    subgoal
      using atm_trail by auto
    subgoal
      using taut2 by auto
    subgoal
      using dist2 by auto
    done

  then have \<open>set_mset I \<Turnstile>m conflicting_clss (update_weight_information (trail S) S)\<close>
    by (auto simp: update_weight_information_def conflicting_clss_def)
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

lemma weight_init_state2[simp]: \<open>weight (init_state S) = None\<close> and
  conflicting_clss_init_state[simp]:
    \<open>conflicting_clss (init_state N) = {#}\<close>
  unfolding weight_def
  conflicting_clss_def conflicting_clauses_def
  by (auto simp: weight_init_state true_clss_cls_tautology_iff simple_clss_finite
    filter_mset_empty_conv mset_set_empty_iff dest: simple_clssE)

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
      conflicting_clss_def conflicting_clauses_def true_clss_cls_tautology_iff simple_clss_finite
    filter_mset_empty_conv mset_set_empty_iff dest: simple_clssE)
  then show ?thesis
    using full_cdcl_bab_stgy_no_conflicting_clss_unsat[OF _ st all_struct
     stgy_inv] by (auto simp: can_always_improve)
qed

definition annotation_is_model where
  \<open>annotation_is_model S \<longleftrightarrow>
     (weight S \<noteq> None \<longrightarrow> (set_mset (the (weight S)) \<Turnstile>sm init_clss S \<and>
       consistent_interp (set_mset (the (weight S))) \<and>
       atms_of (the (weight S)) \<subseteq> atms_of_mm (init_clss S) \<and>
       total_over_m (set_mset (the (weight S))) (set_mset (init_clss S)) \<and>
       distinct_mset (the (weight S))))\<close>

lemma (in -) distinct_consistent_distinct_atm:
  \<open>distinct M \<Longrightarrow> consistent_interp (set M) \<Longrightarrow> distinct_mset (atm_of `# mset M)\<close>
  by (induction M) (auto simp: atm_of_eq_atm_of)

lemma cdcl_bab_annotation_is_model:
  assumes
    \<open>cdcl_bab S T\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> and
    \<open>annotation_is_model S\<close>
  shows \<open>annotation_is_model T\<close>
proof -
  have [simp]: \<open>atms_of (lit_of `# mset M) = atm_of ` lit_of ` set M\<close> for M
    by (auto simp: atms_of_def)
  have \<open>consistent_interp (lits_of_l (trail S)) \<and>
       atm_of ` (lits_of_l (trail S)) \<subseteq> atms_of_mm (init_clss S) \<and>
       distinct_mset (lit_of `# mset (trail S))\<close>
    using assms(2) by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      abs_state_def cdcl\<^sub>W_restart_mset_state cdcl\<^sub>W_restart_mset.no_strange_atm_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
      dest: no_dup_distinct)
  with assms(1,3)
  show ?thesis
    apply (cases rule: cdcl_bab.cases)
    subgoal
      by (auto simp: conflict.simps annotation_is_model_def)
    subgoal
      by (auto simp: propagate.simps annotation_is_model_def)
    subgoal
      by (force simp: annotation_is_model_def true_annots_true_cls lits_of_def
        improve.simps is_improving_int_def image_Un image_image
      dest!: consistent_interp_unionD intro: distinct_mset_union2)
    subgoal
      by (auto simp:  annotation_is_model_def
        conflict_opt.simps)
    subgoal
      by (auto simp: annotation_is_model_def
        ocdcl\<^sub>W_o.simps ocdcl\<^sub>W_bj.simps obacktrack.simps
        skip.simps resolve.simps decide.simps)
    done
qed

lemma rtranclp_cdcl_bab_annotation_is_model:
  \<open>cdcl_bab\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S) \<Longrightarrow>
     annotation_is_model S \<Longrightarrow> annotation_is_model T\<close>
  by (induction rule: rtranclp_induct)
    (auto simp: cdcl_bab_annotation_is_model rtranclp_cdcl_bab_stgy_all_struct_inv)


text \<open>\cwref{theo:prop:cdclmmcorrect}{Theorem 2.15.6}\<close>
theorem full_cdcl_bab_stgy_no_conflicting_clause_from_init_state:
  assumes
    st: \<open>full cdcl_bab_stgy (init_state N) T\<close> and
    dist: \<open>distinct_mset_mset N\<close>
  shows
    \<open>weight T = None \<Longrightarrow> unsatisfiable (set_mset N)\<close> and
    \<open>weight T \<noteq> None \<Longrightarrow> consistent_interp (set_mset (the (weight T))) \<and>
       atms_of (the (weight T)) \<subseteq> atms_of_mm N \<and> set_mset (the (weight T)) \<Turnstile>sm N \<and>
       total_over_m (set_mset (the (weight T))) (set_mset N) \<and>
       distinct_mset (the (weight T))\<close>  and
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
  moreover have [iff]: \<open>cdcl_bab_struct_invs ?S\<close>
    by (auto simp: cdcl_bab_struct_invs_def)
  moreover have [simp]: \<open>cdcl_bab_stgy_inv ?S\<close>
    by (auto simp: cdcl_bab_stgy_inv_def conflict_is_false_with_level_def)
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
    unfolding full_def by (auto dest: rtranclp_cdcl_bab_stgy_cdcl_bab)
  moreover have \<open>init_clss T = N\<close>
    using rtranclp_cdcl_bab_no_more_init_clss[of ?S T] st
    unfolding full_def by (auto dest: rtranclp_cdcl_bab_stgy_cdcl_bab)
  ultimately show \<open>weight T \<noteq> None \<Longrightarrow>  consistent_interp (set_mset (the (weight T))) \<and>
       atms_of (the (weight T)) \<subseteq> atms_of_mm N \<and> set_mset (the (weight T)) \<Turnstile>sm N \<and>
       total_over_m (set_mset (the (weight T))) (set_mset N) \<and>
       distinct_mset (the (weight T))\<close>
    by (auto simp: annotation_is_model_def)

  show \<open>distinct_mset I \<Longrightarrow> consistent_interp (set_mset I) \<Longrightarrow> atms_of I = atms_of_mm N \<Longrightarrow>
      set_mset I \<Turnstile>sm N \<Longrightarrow> \<rho> I \<ge> \<rho>' (weight T)\<close>
    using full_cdcl_bab_stgy_larger_or_equal_weight[of ?S T I] st unfolding full_def
    by auto
qed

lemma
  fixes P P' Q Q' :: 'v
  defines \<open>N' \<equiv>  {#{#Pos P, Pos Q#}, {#Pos P, Pos Q'#}, {#Pos P', Pos Q#}, {#Pos P', Pos Q'#}#}\<close>
  assumes [simp]: \<open>\<And>M. \<rho> M = (\<Sum> A \<in># M. \<nu> A)\<close> and
    [simp]: \<open>\<nu> (Pos Q) = 1\<close> and
    [simp]: \<open>\<nu> (Neg Q) = 3\<close> and
    [simp]: \<open>\<nu> (Pos P) = 3\<close> and
    [simp]: \<open>\<nu> (Pos Q) = 3\<close> and
    dist[simp]: \<open>P \<noteq> Q\<close> \<open>P \<noteq> P'\<close> \<open>P \<noteq> Q'\<close> \<open>Q \<noteq> Q'\<close> \<open>Q \<noteq> P'\<close> \<open>P' \<noteq> Q'\<close>
  shows \<open>cdcl_bab_stgy\<^sup>*\<^sup>* (init_state N') G\<close>
proof -
  note [simp] = dist[symmetric]
  show ?thesis
    apply (rule converse_rtranclp_into_rtranclp)
    apply (rule cdcl_bab_other')
    apply (rule decide)
    apply (rule decide.intros[of _ \<open>Pos P\<close>, OF _ _ _ state_eq_ref])
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: N'_def)
    subgoal by (auto simp: N'_def propagate.simps conflict.simps improve.simps
      is_improving_int_def conflict_opt.simps)

    apply (rule converse_rtranclp_into_rtranclp)
    apply (rule cdcl_bab_other')
    apply (rule decide)
    apply (rule decide.intros[of _ \<open>Pos Q\<close>, OF _ _ _ state_eq_ref])
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: N'_def)
    subgoal
      by (auto simp: N'_def propagate.simps conflict.simps improve.simps
      is_improving_int_def conflict_opt.simps)

    apply (rule converse_rtranclp_into_rtranclp)
    apply (rule cdcl_bab_other')
    apply (rule decide)
    apply (rule decide.intros[of _ \<open>Pos P'\<close>, OF _ _ _ state_eq_ref])
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: N'_def)
    subgoal
      by (auto simp: N'_def propagate.simps conflict.simps improve.simps
      is_improving_int_def conflict_opt.simps)

    apply (rule converse_rtranclp_into_rtranclp)
    apply (rule cdcl_bab_other')
    apply (rule decide)
    apply (rule decide.intros[of _ \<open>Pos Q'\<close>, OF _ _ _ state_eq_ref])
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: N'_def)
    subgoal
      by (auto simp: N'_def propagate.simps conflict.simps improve.simps
      is_improving_int_def conflict_opt.simps)

    apply (rule converse_rtranclp_into_rtranclp)
    apply (rule cdcl_bab_improve)
    apply (rule improve.intros[of , OF _ _ state_eq_ref])
    subgoal by (auto simp: is_improving_int_def N'_def simple_clss_def
      tautology_decomp true_annot_def)
    subgoal by auto

    apply (rule converse_rtranclp_into_rtranclp)
    apply (rule cdcl_bab_conflict_opt)
    apply (rule conflict_opt.intros[of , OF _ _ state_eq_ref])
    subgoal apply (auto simp: conflicting_clss_def conflicting_clauses_def
      simple_clss_finite too_heavy_clauses_def)
      by (auto simp: simple_clss_def tautology_decomp N'_def negate_ann_lits_def pNeg_def
         too_heavy_clauses_def image_iff intro!: true_clss_cls_in
	 exI[of _ \<open>pNeg {#Neg Q', Neg P', Neg Q, Neg P#}\<close>])
    subgoal by auto
   oops

lemma (in -) distinct_mset_image_mset:
  \<open>distinct_mset (f `# mset xs) \<longleftrightarrow> distinct (map f xs)\<close>
  apply (subst mset_map[symmetric])
  apply (subst distinct_mset_mset_distinct)
  ..

lemma (in -) distinct_mset_atm_ofD:
  \<open>distinct_mset (atm_of `# mset xc) \<Longrightarrow> distinct xc\<close>
  by (induction xc) auto

lemma (in -) atms_of_cong_set_mset:
  \<open>set_mset D = set_mset D' \<Longrightarrow> atms_of D = atms_of D'\<close>
  by (auto simp: atms_of_def)

lemma (in -) true_clss_cls_cong_set_mset:
  \<open>N \<Turnstile>pm D \<Longrightarrow> set_mset D = set_mset D' \<Longrightarrow> N \<Turnstile>pm D'\<close>
  by (auto simp add: true_clss_cls_def true_cls_def atms_of_cong_set_mset[of D D'])

lemma pruned_clause_in_conflicting_clss:
  assumes
    ge: \<open>\<And>M'. total_over_m (set_mset (mset (M @ M'))) (set_mset (init_clss S)) \<Longrightarrow>
      distinct_mset (atm_of `# mset (M @ M')) \<Longrightarrow>
      consistent_interp (set_mset (mset (M @ M'))) \<Longrightarrow> \<rho> (mset (M @ M')) \<ge> \<rho>' (weight S)\<close> and
    atm: \<open>atms_of (mset M) \<subseteq> atms_of_mm (init_clss S)\<close> and
    dist: \<open>distinct M\<close> and
    cons: \<open>consistent_interp (set M)\<close>
  shows \<open>pNeg (mset M) \<in># conflicting_clss S\<close>
proof -
  have 0: \<open>(pNeg o mset o ((@) M))` {M'.
      distinct_mset (atm_of `# mset (M @ M')) \<and> consistent_interp (set_mset (mset (M @ M'))) \<and>
      atms_of_s (set (M @ M')) \<subseteq> (atms_of_mm (init_clss S)) \<and>
      card (atms_of_mm (init_clss S)) = n + card (atms_of (mset (M @ M')))} \<subseteq>
    set_mset (conflicting_clss S)\<close> for n
  proof (induction n)
    case 0
    show ?case
    proof clarify
      fix x :: \<open>'v literal multiset\<close> and xa :: \<open>'v literal multiset\<close> and
        xb :: \<open>'v literal list\<close> and xc :: \<open>'v literal list\<close>
      assume
	dist: \<open>distinct_mset (atm_of `# mset (M @ xc))\<close> and
	cons: \<open>consistent_interp (set_mset (mset (M @ xc)))\<close> and
	atm': \<open>atms_of_s (set (M @ xc)) \<subseteq> atms_of_mm (init_clss S)\<close> and
	0: \<open>card (atms_of_mm (init_clss S)) = 0 + card (atms_of (mset (M @ xc)))\<close>
      have D[dest]:
	\<open>A \<in> set M \<Longrightarrow> A \<notin> set xc\<close>
	\<open>A \<in> set M \<Longrightarrow> -A \<notin> set xc\<close>
	for A
	using dist multi_member_split[of A \<open>mset M\<close>] multi_member_split[of \<open>-A\<close> \<open>mset xc\<close>]
	   multi_member_split[of \<open>-A\<close> \<open>mset M\<close>] multi_member_split[of \<open>A\<close> \<open>mset xc\<close>]
	by (auto simp: atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set)
      have dist2: \<open>distinct xc\<close> \<open>distinct_mset (atm_of `# mset xc)\<close>
	    \<open>distinct_mset (mset M + mset xc)\<close>
	using dist distinct_mset_atm_ofD[OF dist]
	unfolding mset_append[symmetric] distinct_mset_mset_distinct
	by (auto dest: distinct_mset_union2 distinct_mset_atm_ofD)
      have eq: \<open>card (atms_of_s (set M) \<union> atms_of_s (set xc)) =
	card (atms_of_s (set M)) + card (atms_of_s (set xc))\<close>
	by (subst card_Un_Int) auto
      let ?M = \<open>M @ xc\<close>

      have H1: \<open>atms_of_s (set ?M) = atms_of_mm (init_clss S)\<close>
	using eq atm card_mono[OF _ atm'] card_subset_eq[OF _ atm'] 0
	by (auto simp: atms_of_s_def image_Un)
      moreover have tot2: \<open>total_over_m (set ?M) (set_mset (init_clss S))\<close>
	using H1
	by (auto simp: total_over_m_def total_over_set_def lit_in_set_iff_atm)
      moreover have \<open>\<not>tautology (mset ?M)\<close>
	using cons unfolding consistent_interp_tautology[symmetric]
	by auto
      ultimately have \<open>mset ?M \<in> simple_clss (atms_of_mm (init_clss S))\<close>
	using dist atm cons H1 dist2
	by (auto simp: simple_clss_def consistent_interp_tautology atms_of_s_def)
      moreover have tot2: \<open>total_over_m (set ?M) (set_mset (init_clss S))\<close>
	using H1
	by (auto simp: total_over_m_def total_over_set_def lit_in_set_iff_atm)
      ultimately show \<open>(pNeg \<circ> mset \<circ> (@) M) xc \<in># conflicting_clss S\<close>
	using ge[of \<open>xc\<close>] dist 0 cons card_mono[OF _ atm] tot2 cons
	by (auto simp: conflicting_clss_def too_heavy_clauses_def
	     simple_clss_finite
	  intro!: too_heavy_clauses_conflicting_clauses imageI)
    qed
  next
    case (Suc n) note IH = this(1)
    let ?H = \<open>{M'.
      distinct_mset (atm_of `# mset (M @ M')) \<and>
      consistent_interp (set_mset (mset (M @ M'))) \<and>
      atms_of_s (set (M @ M')) \<subseteq> atms_of_mm (init_clss S) \<and>
      card (atms_of_mm (init_clss S)) = n + card (atms_of (mset (M @ M')))}\<close>
    show ?case
    proof clarify
      fix x :: \<open>'v literal multiset\<close> and xa :: \<open>'v literal multiset\<close> and
        xb :: \<open>'v literal list\<close> and xc :: \<open>'v literal list\<close>
      assume
	dist: \<open>distinct_mset (atm_of `# mset (M @ xc))\<close> and
	cons: \<open>consistent_interp (set_mset (mset (M @ xc)))\<close> and
	atm': \<open>atms_of_s (set (M @ xc)) \<subseteq> atms_of_mm (init_clss S)\<close> and
	0: \<open>card (atms_of_mm (init_clss S)) = Suc n + card (atms_of (mset (M @ xc)))\<close>
      then obtain a where
        a: \<open>a \<in> atms_of_mm (init_clss S)\<close> and
	a_notin: \<open>a \<notin> atms_of_s (set (M @ xc))\<close>
	by (metis Suc_n_not_le_n add_Suc_shift atms_of_mmltiset atms_of_s_def le_add2
	  subsetI subset_antisym)
      have dist2: \<open>distinct xc\<close> \<open>distinct_mset (atm_of `# mset xc)\<close>
	    \<open>distinct_mset (mset M + mset xc)\<close>
	using dist distinct_mset_atm_ofD[OF dist]
	unfolding mset_append[symmetric] distinct_mset_mset_distinct
	by (auto dest: distinct_mset_union2 distinct_mset_atm_ofD)
      let ?xc1 = \<open>Pos a # xc\<close>
      let ?xc2 = \<open>Neg a # xc\<close>
      have \<open>?xc1 \<in> ?H\<close>
        using dist cons atm' 0 dist2 a_notin a
        by (auto simp: distinct_mset_add mset_inter_empty_set_mset
	  lit_in_set_iff_atm card_insert_if)
      from set_mp[OF IH imageI[OF this]]
      have 1: \<open>too_heavy_clauses (init_clss S) (weight S) \<Turnstile>pm add_mset (-(Pos a)) (pNeg (mset (M @ xc)))\<close>
        unfolding conflicting_clss_def unfolding conflicting_clauses_def
	by (auto simp: pNeg_simps)
      have \<open>?xc2 \<in> ?H\<close>
        using dist cons atm' 0 dist2 a_notin a
        by (auto simp: distinct_mset_add mset_inter_empty_set_mset
	  lit_in_set_iff_atm card_insert_if)
      from set_mp[OF IH imageI[OF this]]
      have 2: \<open>too_heavy_clauses (init_clss S) (weight S) \<Turnstile>pm add_mset (Pos a) (pNeg (mset (M @ xc)))\<close>
        unfolding conflicting_clss_def unfolding conflicting_clauses_def
	by (auto simp: pNeg_simps)

      have \<open>\<not>tautology (mset (M @ xc))\<close>
	using cons unfolding consistent_interp_tautology[symmetric]
	by auto
      then have \<open>\<not>tautology (pNeg (mset M) + pNeg (mset xc))\<close>
        unfolding mset_append[symmetric] pNeg_simps[symmetric]
	by (auto simp del: mset_append)
      then have \<open>pNeg (mset M) + pNeg (mset xc) \<in> simple_clss (atms_of_mm (init_clss S))\<close>
        using atm' dist2
        by (auto simp: simple_clss_def atms_of_s_def
	  simp flip: pNeg_simps)
      then show \<open>(pNeg \<circ> mset \<circ> (@) M) xc \<in># conflicting_clss S\<close>
        using true_clss_cls_or_true_clss_cls_or_not_true_clss_cls_or[OF 1 2] apply -
        unfolding conflicting_clss_def conflicting_clauses_def
	by (subst (asm) true_clss_cls_remdups_mset[symmetric])
	  (auto simp: simple_clss_finite pNeg_simps intro: true_clss_cls_cong_set_mset
	  simp del: true_clss_cls_remdups_mset)
    qed
  qed
  have \<open>[] \<in> {M'.
     distinct_mset (atm_of `# mset (M @ M')) \<and>
     consistent_interp (set_mset (mset (M @ M'))) \<and>
     atms_of_s (set (M @ M')) \<subseteq> atms_of_mm (init_clss S) \<and>
     card (atms_of_mm (init_clss S)) =
     card (atms_of_mm (init_clss S)) - card (atms_of (mset M)) +
     card (atms_of (mset (M @ M')))}\<close>
    using card_mono[OF _ assms(2)] assms by (auto dest: card_mono distinct_consistent_distinct_atm)

  from set_mp[OF 0 imageI[OF this]]
  show \<open>pNeg (mset M) \<in># conflicting_clss S\<close>
    by auto
qed

text \<open>To make sure that the paper version of the correct, we restrict the previous calculus to exactly
  the rules that are on paper.\<close>
inductive pruning :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> where
pruning_rule:
  \<open>pruning S T\<close>
  if
    \<open>\<And>M'. total_over_m (set_mset (mset (map lit_of (trail S) @ M'))) (set_mset (init_clss S)) \<Longrightarrow>
       distinct_mset (atm_of `# mset (map lit_of (trail S) @ M')) \<Longrightarrow>
       consistent_interp (set_mset (mset (map lit_of (trail S) @ M'))) \<Longrightarrow>
       \<rho>' (weight S) \<le> enat (\<rho> (mset (map lit_of (trail S) @ M')))\<close>
    \<open>conflicting S = None\<close>
    \<open>T \<sim> update_conflicting (Some (negate_ann_lits (trail S))) S\<close>

inductive oconflict_opt :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S T :: 'st where
oconflict_opt_rule:
  \<open>oconflict_opt S T\<close>
  if
    \<open>\<rho> (lit_of `# mset (trail S)) \<ge> \<rho>' (weight S)\<close>
    \<open>conflicting S = None\<close>
    \<open>T \<sim> update_conflicting (Some (negate_ann_lits (trail S))) S\<close>


inductive ocdcl\<^sub>w :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> for S :: 'st where
ocdcl_conflict: "conflict S S' \<Longrightarrow> ocdcl\<^sub>w S S'" |
ocdcl_propagate: "propagate S S' \<Longrightarrow> ocdcl\<^sub>w S S'" |
ocdcl_improve: "improve S S' \<Longrightarrow> ocdcl\<^sub>w S S'" |
ocdcl_conflict_opt: "oconflict_opt S S' \<Longrightarrow> ocdcl\<^sub>w S S'" |
ocdcl_other': "ocdcl\<^sub>W_o S S' \<Longrightarrow> ocdcl\<^sub>w S S'" |
ocdcl_pruning: "pruning S S' \<Longrightarrow> ocdcl\<^sub>w S S'"

inductive ocdcl\<^sub>w_stgy :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> for S :: 'st where
ocdcl\<^sub>w_conflict: "conflict S S' \<Longrightarrow> ocdcl\<^sub>w_stgy S S'" |
ocdcl\<^sub>w_propagate: "propagate S S' \<Longrightarrow> ocdcl\<^sub>w_stgy S S'" |
ocdcl\<^sub>w_improve: "improve S S' \<Longrightarrow> ocdcl\<^sub>w_stgy S S'" |
ocdcl\<^sub>w_conflict_opt: "conflict_opt S S' \<Longrightarrow> ocdcl\<^sub>w_stgy S S'"|
ocdcl\<^sub>W_pruning: "pruning S S' \<Longrightarrow> ocdcl\<^sub>w_stgy S S'" |
ocdcl\<^sub>w_other': "ocdcl\<^sub>W_o S S' \<Longrightarrow> no_confl_prop_impr S \<Longrightarrow> ocdcl\<^sub>w_stgy S S'"

lemma pruning_conflict_opt:
  assumes ocdcl_pruning: \<open>pruning S T\<close> and
    inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close>
  shows \<open>conflict_opt S T\<close>
proof -
  have le:
    \<open>\<And>M'. total_over_m (set_mset (mset (map lit_of (trail S) @ M')))
          (set_mset (init_clss S)) \<Longrightarrow>
         distinct_mset (atm_of `# mset (map lit_of (trail S) @ M')) \<Longrightarrow>
         consistent_interp (set_mset (mset (map lit_of (trail S) @ M'))) \<Longrightarrow>
         \<rho>' (weight S) \<le> enat (\<rho> (mset (map lit_of (trail S) @ M')))\<close>
    using ocdcl_pruning by (auto simp: pruning.simps)
  have alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (abs_state S)\<close> and
    lev: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (abs_state S)\<close>
    using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast+
  have incl: \<open>atms_of (mset (map lit_of (trail S))) \<subseteq> atms_of_mm (init_clss S)\<close>
    using alien unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def
    by (auto simp: abs_state_def cdcl\<^sub>W_restart_mset_state lits_of_def image_image atms_of_def)
  have dist: \<open>distinct (map lit_of (trail S))\<close> and
    cons: \<open>consistent_interp (set (map lit_of (trail S)))\<close>
    using lev unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by (auto simp: abs_state_def cdcl\<^sub>W_restart_mset_state lits_of_def image_image atms_of_def
      dest: no_dup_map_lit_of)
  have \<open>negate_ann_lits (trail S) \<in># conflicting_clss S\<close>
    unfolding negate_ann_lits_pNeg_lit_of comp_def mset_map[symmetric]
    apply (rule pruned_clause_in_conflicting_clss)
    subgoal using le by fast
    subgoal using incl by fast
    subgoal using dist by fast
    subgoal using cons by fast
    done
  then show \<open>conflict_opt S T\<close>
    apply (rule conflict_opt.intros)
    subgoal using ocdcl_pruning by (auto simp: pruning.simps)
    subgoal using ocdcl_pruning by (auto simp: pruning.simps)
    done
qed

lemma ocdcl_conflict_opt_conflict_opt:
  assumes ocdcl_pruning: \<open>oconflict_opt S T\<close> and
    inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close>
  shows \<open>conflict_opt S T\<close>
proof -
  have alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (abs_state S)\<close> and
    lev: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (abs_state S)\<close>
    using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast+
  have incl: \<open>atms_of (lit_of `# mset (trail S)) \<subseteq> atms_of_mm (init_clss S)\<close>
    using alien unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def
    by (auto simp: abs_state_def cdcl\<^sub>W_restart_mset_state lits_of_def image_image atms_of_def)
  have dist: \<open>distinct_mset (lit_of `# mset (trail S))\<close> and
    cons: \<open>consistent_interp (set (map lit_of (trail S)))\<close> and
    tauto: \<open>\<not>tautology (lit_of `# mset (trail S))\<close>
    using lev unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by (auto simp: abs_state_def cdcl\<^sub>W_restart_mset_state lits_of_def image_image atms_of_def
      dest: no_dup_map_lit_of no_dup_distinct no_dup_not_tautology)
  have \<open>lit_of `# mset (trail S) \<in> simple_clss (atms_of_mm (init_clss S))\<close>
    using dist incl tauto by (auto simp: simple_clss_def)
  then have simple: \<open>(lit_of `# mset (trail S))
    \<in> {a. a \<in># mset_set (simple_clss (atms_of_mm (init_clss S))) \<and>
          \<rho>' (weight S) \<le> enat (\<rho> a)}\<close>
    using ocdcl_pruning by (auto simp: simple_clss_finite oconflict_opt.simps)
  have \<open>negate_ann_lits (trail S) \<in># conflicting_clss S\<close>
    unfolding negate_ann_lits_pNeg_lit_of comp_def conflicting_clss_def
    by (rule too_heavy_clauses_conflicting_clauses)
      (use simple in \<open>auto simp: too_heavy_clauses_def oconflict_opt.simps\<close>)
  then show \<open>conflict_opt S T\<close>
    apply (rule conflict_opt.intros)
    subgoal using ocdcl_pruning by (auto simp: oconflict_opt.simps)
    subgoal using ocdcl_pruning by (auto simp: oconflict_opt.simps)
    done
qed

lemma ocdcl\<^sub>w_cdcl_bab:
  assumes \<open>ocdcl\<^sub>w S T\<close> and
    inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close>
  shows \<open>cdcl_bab S T\<close>
  using assms by (cases) (auto intro: cdcl_bab.intros dest: pruning_conflict_opt
    ocdcl_conflict_opt_conflict_opt)


lemma ocdcl\<^sub>w_stgy_cdcl_bab_stgy:
  assumes \<open>ocdcl\<^sub>w_stgy S T\<close> and
    inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close>
  shows \<open>cdcl_bab_stgy S T\<close>
  using assms by (cases) (auto intro: cdcl_bab_stgy.intros dest: pruning_conflict_opt)

lemma rtranclp_ocdcl\<^sub>w_stgy_rtranclp_cdcl_bab_stgy:
  assumes \<open>ocdcl\<^sub>w_stgy\<^sup>*\<^sup>* S T\<close> and
    inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close>
  shows \<open>cdcl_bab_stgy\<^sup>*\<^sup>* S T\<close>
  using assms
  by (induction rule: rtranclp_induct)
    (auto dest: rtranclp_cdcl_bab_stgy_all_struct_inv[OF rtranclp_cdcl_bab_stgy_cdcl_bab]
      ocdcl\<^sub>w_stgy_cdcl_bab_stgy)

lemma no_step_ocdcl\<^sub>w_no_step_cdcl_bab:
  assumes \<open>no_step ocdcl\<^sub>w S\<close> and
    inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close>
  shows \<open>no_step cdcl_bab S\<close>
proof -
  have
    nsc: \<open>no_step conflict S\<close> and
    nsp: \<open>no_step propagate S\<close> and
    nsi: \<open>no_step improve S\<close> and
    nsco: \<open>no_step oconflict_opt S\<close> and
    nso: \<open>no_step ocdcl\<^sub>W_o S\<close>and
    nspr: \<open>no_step pruning S\<close>
    using assms(1) by (auto simp: cdcl_bab.simps ocdcl\<^sub>w.simps)
  have alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (abs_state S)\<close> and
    lev: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (abs_state S)\<close>
    using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast+
  have incl: \<open>atms_of (lit_of `# mset (trail S)) \<subseteq> atms_of_mm (init_clss S)\<close>
    using alien unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def
    by (auto simp: abs_state_def cdcl\<^sub>W_restart_mset_state lits_of_def image_image atms_of_def)
  have dist: \<open>distinct_mset (lit_of `# mset (trail S))\<close> and
    cons: \<open>consistent_interp (set (map lit_of (trail S)))\<close> and
    tauto: \<open>\<not>tautology (lit_of `# mset (trail S))\<close> and
    n_d: \<open>no_dup (trail S)\<close>
    using lev unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by (auto simp: abs_state_def cdcl\<^sub>W_restart_mset_state lits_of_def image_image atms_of_def
      dest: no_dup_map_lit_of no_dup_distinct no_dup_not_tautology)

  have False if \<open>conflict_opt S S'\<close> for S'
  proof -
    have [simp]: \<open>conflicting S = None\<close>
      using that by (auto simp: conflict_opt.simps)
    have 1: \<open>\<not> \<rho>' (weight S) \<le> enat (\<rho> (lit_of `# mset (trail S)))\<close>
      using nsco
      by (auto simp: is_improving_int_def oconflict_opt.simps)
    have 2: \<open>total_over_m (lits_of_l (trail S)) (set_mset (init_clss S))\<close>
    proof (rule ccontr)
      assume \<open>\<not> ?thesis\<close>
      then obtain A where
        \<open>A \<in> atms_of_mm (init_clss S)\<close> and
	\<open>A \<notin> atms_of_s (lits_of_l (trail S))\<close>
	by (auto simp: total_over_m_def total_over_set_def)
      then show \<open>False\<close>
        using decide_rule[of S \<open>Pos A\<close>, OF _ _ _ state_eq_ref] nso
	by (auto simp: Decided_Propagated_in_iff_in_lits_of_l ocdcl\<^sub>W_o.simps)
      qed
    have 3: \<open>trail S \<Turnstile>asm init_clss S\<close>
      unfolding true_annots_def
    proof clarify
      fix C
      assume C: \<open>C \<in># init_clss S\<close>
      have \<open>total_over_m (lits_of_l (trail S)) {C}\<close>
        using 2 C by (auto dest!: multi_member_split)
      moreover have \<open>\<not> trail S \<Turnstile>as CNot C\<close>
        using C nsc conflict_rule[of S C, OF _ _ _ state_eq_ref]
	by (auto simp: clauses_def dest!: multi_member_split)
      ultimately show \<open>trail S \<Turnstile>a C\<close>
        using total_not_CNot[of \<open>lits_of_l (trail S)\<close> C] unfolding true_annots_true_cls true_annot_def
	by auto
    qed
    have 4: \<open>lit_of `# mset (trail S) \<in> simple_clss (atms_of_mm (init_clss S))\<close>
      using tauto cons incl dist by (auto simp: simple_clss_def)
    have imp: \<open>is_improving (trail S) S\<close>
      using 1 2 3 4 incl n_d
      by (auto simp: is_improving_int_def oconflict_opt.simps)

    show \<open>False\<close>
      using trail_is_improving_Ex_improve[of S, OF _ imp] nsi by auto
  qed
  then show ?thesis
    using nsc nsp nsi nsco nso nsp nspr
    by (auto simp: cdcl_bab.simps)
qed

lemma all_struct_init_state_distinct_iff:
  \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state (init_state N)) \<longleftrightarrow>
  distinct_mset_mset N\<close>
      unfolding init_state.simps[symmetric]
    by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
      cdcl\<^sub>W_restart_mset.no_strange_atm_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def
      abs_state_def cdcl\<^sub>W_restart_mset_state)

lemma no_step_ocdcl\<^sub>w_stgy_no_step_cdcl_bab_stgy:
  assumes \<open>no_step ocdcl\<^sub>w_stgy S\<close> and
    inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close>
  shows \<open>no_step cdcl_bab_stgy S\<close>
  using assms no_step_ocdcl\<^sub>w_no_step_cdcl_bab[of S]
  by (auto simp: ocdcl\<^sub>w_stgy.simps ocdcl\<^sub>w.simps
    cdcl_bab.simps cdcl_bab_stgy.simps)

lemma full_ocdcl\<^sub>w_stgy_full_cdcl_bab_stgy:
  assumes \<open>full ocdcl\<^sub>w_stgy S T\<close> and
    inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close>
  shows \<open>full cdcl_bab_stgy S T\<close>
  using assms rtranclp_ocdcl\<^sub>w_stgy_rtranclp_cdcl_bab_stgy[of S T]
    no_step_ocdcl\<^sub>w_stgy_no_step_cdcl_bab_stgy[of T]
  unfolding full_def
  by (auto dest: rtranclp_cdcl_bab_stgy_all_struct_inv[OF rtranclp_cdcl_bab_stgy_cdcl_bab])

corollary full_ocdcl\<^sub>w_stgy_no_conflicting_clause_from_init_state:
  assumes
    st: \<open>full ocdcl\<^sub>w_stgy (init_state N) T\<close> and
    dist: \<open>distinct_mset_mset N\<close>
  shows
    \<open>weight T = None \<Longrightarrow> unsatisfiable (set_mset N)\<close> and
    \<open>weight T \<noteq> None \<Longrightarrow> consistent_interp (set_mset (the (weight T))) \<and>
       atms_of (the (weight T))  \<subseteq> atms_of_mm N \<and> set_mset (the (weight T)) \<Turnstile>sm N \<and>
       distinct_mset (the (weight T))\<close> and
    \<open>distinct_mset I \<Longrightarrow> consistent_interp (set_mset I) \<Longrightarrow> atms_of I = atms_of_mm N \<Longrightarrow>
      set_mset I \<Turnstile>sm N \<Longrightarrow> \<rho> I \<ge> \<rho>' (weight T)\<close>
  using full_cdcl_bab_stgy_no_conflicting_clause_from_init_state[of N T,
    OF full_ocdcl\<^sub>w_stgy_full_cdcl_bab_stgy[OF st] dist] dist
    by (auto simp: all_struct_init_state_distinct_iff)

end


subsection \<open>Encoding of partial SAT into total SAT\<close>
text \<open>
  We here formalise the encoding from a formula to another formula from which we will run derive the
  optimal partial model.

  There are a few difference compared to Dominik Zimmer's current draft:
  \<^item> We work on formula in CNF. So we need more variables and more formulas.

  The intended meaning is the following:
  \<^item> \<^term>\<open>\<Sigma>\<close> is the set of all variables
  \<^item> \<^term>\<open>\<Sigma>\<^sub>w\<close> is the set of all variables with a non-zero weight: These are the variable that are
    replaced during preprocessing, but it does not matter if the weight 0.
\<close>
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
  fixes \<Sigma> \<Sigma>\<^sub>w :: \<open>'v set\<close> and
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
  \<open>encode_lit (Pos A) = (if A \<in> \<Sigma>\<^sub>w then Pos (replacement_pos A) else Pos A)\<close> |
  \<open>encode_lit (Neg A) = (if A \<in> \<Sigma>\<^sub>w then Pos (replacement_neg A) else Neg A)\<close>

lemma encode_lit_alt_def:
  \<open>encode_lit A = (if atm_of A \<in> \<Sigma>\<^sub>w
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

lemma encode_clauses_simp[simp]:
  \<open>encode_clauses {#} = {#}\<close>
  \<open>encode_clauses (add_mset A C) = add_mset (encode_clause A) (encode_clauses C)\<close>
  \<open>encode_clauses (C + D) = encode_clauses C + encode_clauses D\<close>
  by (auto simp: encode_clauses_def)

definition additional_constraint :: \<open>'v \<Rightarrow> 'v clauses\<close> where
  \<open>additional_constraint A =
     {#{#Neg (A\<^sup>\<mapsto>\<^sup>+), Pos A#},
       {#Neg (A\<^sup>\<mapsto>\<^sup>+), additional_var A#},
       {#-additional_var A, -Pos A, Pos (A\<^sup>\<mapsto>\<^sup>+)#},
       {#Neg (A\<^sup>\<mapsto>\<^sup>-), Neg A#},
       {#Neg (A\<^sup>\<mapsto>\<^sup>-), additional_var A#},
       {#-additional_var A, -Neg A, Pos (A\<^sup>\<mapsto>\<^sup>-)#}#}\<close>

definition additional_constraints :: \<open>'v clauses\<close> where
  \<open>additional_constraints = \<Union>#(additional_constraint `# (mset_set \<Sigma>\<^sub>w))\<close>

definition preprocessed_clss :: \<open>'v clauses \<Rightarrow> 'v clauses\<close> where
  \<open>preprocessed_clss N = encode_clauses N + additional_constraints\<close>

lemma size_encode_clauses[simp]: \<open>size (encode_clauses N) = size N\<close>
  by (auto simp: encode_clauses_def)

lemma size_preprocessed_clss:
  \<open>size (preprocessed_clss N) = size N + 6 * card \<Sigma>\<^sub>w\<close>
  by (auto simp: preprocessed_clss_def additional_constraints_def
    additional_constraint_def size_Union_mset_image_mset)

lemma atms_of_mm_additional_constraints: \<open>finite \<Sigma>\<^sub>w \<Longrightarrow>
   atms_of_mm additional_constraints = \<Sigma>\<^sub>w \<union> additional_atm ` \<Sigma>\<^sub>w \<union> replacement_pos ` \<Sigma>\<^sub>w
      \<union> replacement_neg ` \<Sigma>\<^sub>w\<close>
  by (auto simp: additional_constraints_def additional_constraint_def atms_of_ms_def)

lemma atms_of_mm_encode_clause_subset:
  \<open>atms_of_mm (encode_clauses N) \<subseteq> (atms_of_mm N - \<Sigma>\<^sub>w) \<union> replacement_pos ` {A \<in> \<Sigma>\<^sub>w. A \<in> atms_of_mm N}
    \<union> replacement_neg ` {A \<in> \<Sigma>\<^sub>w. A \<in> atms_of_mm N}\<close>
  by (auto simp: encode_clauses_def encode_lit_alt_def atms_of_ms_def atms_of_def
      encode_clause_def split: if_splits
    dest!: multi_member_split[of _ N])

text \<open>In every meaningful application of the theorem below, we have \<open>\<Sigma>\<^sub>w \<subseteq> atms_of_mm N\<close>.\<close>
lemma atms_of_mm_preprocessed_clss_subset: \<open>finite \<Sigma>\<^sub>w \<Longrightarrow>
  atms_of_mm (preprocessed_clss N) \<subseteq> atms_of_mm N \<union> additional_atm ` \<Sigma>\<^sub>w \<union> replacement_pos ` \<Sigma>\<^sub>w
      \<union> replacement_neg ` \<Sigma>\<^sub>w \<union> \<Sigma>\<^sub>w\<close>
  using atms_of_mm_encode_clause_subset[of N]
  by (auto simp: preprocessed_clss_def atms_of_mm_additional_constraints)

lemma atms_of_mm_encode_clause_subset2: \<open>finite \<Sigma>\<^sub>w \<Longrightarrow> \<Sigma>\<^sub>w \<subseteq> atms_of_mm N \<Longrightarrow>
  atms_of_mm N \<subseteq> atms_of_mm (encode_clauses N) \<union> \<Sigma>\<^sub>w\<close>
  by (auto simp: encode_clauses_def encode_lit_alt_def atms_of_ms_def atms_of_def
      encode_clause_def split: if_splits
    dest!: multi_member_split[of _ N])

lemma atms_of_mm_preprocessed_clss_subset2: \<open>finite \<Sigma>\<^sub>w \<Longrightarrow> \<Sigma>\<^sub>w \<subseteq> atms_of_mm N \<Longrightarrow>
  atms_of_mm (preprocessed_clss N) = atms_of_mm N \<union> additional_atm ` \<Sigma>\<^sub>w \<union> replacement_pos ` \<Sigma>\<^sub>w
      \<union> replacement_neg ` \<Sigma>\<^sub>w\<close>
  using atms_of_mm_encode_clause_subset[of N] atms_of_mm_encode_clause_subset2[of N]
  by (auto simp: preprocessed_clss_def atms_of_mm_additional_constraints)

theorem card_atms_of_mm_preprocessed_clss:
  assumes \<open>finite \<Sigma>\<^sub>w\<close> and
    \<open>\<Sigma>\<^sub>w \<subseteq> atms_of_mm N\<close>
  shows \<open>card (atms_of_mm (preprocessed_clss N)) \<le> 4 * card (atms_of_mm N)\<close> (is \<open>?A \<le> ?B\<close>)
proof -
  have \<open>?A = card
     (atms_of_mm N \<union> additional_atm ` \<Sigma>\<^sub>w \<union> replacement_pos ` \<Sigma>\<^sub>w \<union>
      replacement_neg ` \<Sigma>\<^sub>w)\<close> (is \<open>_ = card (?W \<union> ?X \<union> ?Y \<union> ?Z)\<close>)
    using arg_cong[OF atms_of_mm_preprocessed_clss_subset2[of N], of card] assms
    using card_Un_le
    by auto
  also have \<open>... \<le> card (?W \<union> ?X \<union> ?Y) + card ?Z\<close>
    using card_Un_le[of \<open>?W \<union> ?X \<union> ?Y\<close> ?Z] by auto
  also have \<open>... \<le> card (?W \<union> ?X) + card ?Y + card ?Z\<close>
    using card_Un_le[of \<open>?W \<union> ?X\<close> ?Y] by auto
  also have \<open>... \<le> card ?W + card ?X + card ?Y + card ?Z\<close>
    using card_Un_le[of \<open>?W\<close> ?X] by auto
  also have \<open>... \<le>  4 * card (atms_of_mm N)\<close>
    using card_mono[of \<open>atms_of_mm N\<close> \<open>\<Sigma>\<^sub>w\<close>] assms
      card_image_le[of \<Sigma>\<^sub>w additional_atm]
      card_image_le[of \<Sigma>\<^sub>w replacement_pos]
      card_image_le[of \<Sigma>\<^sub>w replacement_neg]
    by auto
  finally show ?thesis .
qed

definition postp :: \<open>'v partial_interp \<Rightarrow> 'v partial_interp\<close> where
  \<open>postp I =
     {A \<in> I. atm_of A \<notin> \<Sigma>\<^sub>w \<and> atm_of A \<in> \<Sigma>} \<union> {A \<in> I. atm_of A \<in> \<Sigma>\<^sub>w \<and> additional_var (atm_of A) \<in> I}\<close>

lemma preprocess_clss_model_additional_variables:
  assumes \<open>I \<Turnstile>sm preprocessed_clss N\<close> and
    \<open>A \<in> \<Sigma>\<^sub>w\<close> and
    \<open>finite \<Sigma>\<^sub>w\<close> and
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
    by (auto simp: preprocessed_clss_def additional_constraints_def true_clss_def
      additional_constraint_def ball_Un)
qed

lemma preprocess_clss_model_additional_variables2:
  assumes
    \<open>atm_of A \<in> \<Sigma> - \<Sigma>\<^sub>w\<close>
  shows
    \<open>A \<in> postp I \<longleftrightarrow> A \<in> I\<close> (is ?A)
proof -
  show ?A
    using assms
    by (auto simp: postp_def)
qed

lemma encode_clause_iff:
  assumes
    \<open>\<And>A. A \<in> \<Sigma>\<^sub>w \<Longrightarrow> Pos A \<in> I \<longleftrightarrow> Pos (replacement_pos A) \<in> I\<close>
    \<open>\<And>A. A \<in> \<Sigma>\<^sub>w \<Longrightarrow> Neg A \<in> I \<longleftrightarrow> Pos (replacement_neg A) \<in> I\<close>
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
    \<open>\<And>A. A \<in> \<Sigma>\<^sub>w \<Longrightarrow> Pos A \<in> I \<longleftrightarrow> Pos (replacement_pos A) \<in> I\<close>
    \<open>\<And>A. A \<in> \<Sigma>\<^sub>w \<Longrightarrow> Neg A \<in> I \<longleftrightarrow> Pos (replacement_neg A) \<in> I\<close>
  shows \<open>I \<Turnstile>m encode_clauses C \<longleftrightarrow> I \<Turnstile>m C\<close>
  using encode_clause_iff[OF assms]
  by (auto simp: encode_clauses_def true_cls_mset_def)


definition \<Sigma>\<^sub>a\<^sub>d\<^sub>d where
  \<open>\<Sigma>\<^sub>a\<^sub>d\<^sub>d = replacement_pos ` \<Sigma>\<^sub>w \<union> replacement_neg ` \<Sigma>\<^sub>w \<union> additional_atm ` \<Sigma>\<^sub>w\<close>


definition upostp :: \<open>'v partial_interp \<Rightarrow> 'v partial_interp\<close> where
  \<open>upostp I =
     Neg ` {A \<in> \<Sigma>. Pos A \<notin> I \<and> Neg A \<notin> I}
     \<union> {A \<in> I. atm_of A \<in> \<Sigma>}
     \<union> Neg ` additional_atm ` {A \<in> \<Sigma>\<^sub>w. Pos A \<notin> I \<and> Neg A \<notin> I}
     \<union> Pos ` additional_atm ` {A \<in> \<Sigma>\<^sub>w. Pos A \<in> I \<or> Neg A \<in> I}
     \<union> Pos ` replacement_pos ` {A \<in> \<Sigma>\<^sub>w. Pos A \<in> I}
     \<union> Neg ` replacement_pos ` {A \<in> \<Sigma>\<^sub>w. Pos A \<notin> I}
     \<union> Pos ` replacement_neg ` {A \<in> \<Sigma>\<^sub>w. Neg A \<in> I}
     \<union> Neg ` replacement_neg ` {A \<in> \<Sigma>\<^sub>w. Neg A \<notin> I}\<close>

lemma atm_of_upostp_subset:
  \<open>atm_of ` (upostp I) \<subseteq>
    atm_of ` I \<union> additional_atm ` \<Sigma>\<^sub>w \<union> replacement_pos ` \<Sigma>\<^sub>w \<union>
    replacement_neg ` \<Sigma>\<^sub>w \<union> \<Sigma>\<close>
  by (auto simp: upostp_def image_Un)

lemma atm_of_upostp_subset2:
  \<open>atm_of ` I \<subseteq> \<Sigma> \<Longrightarrow> atm_of ` I \<union> additional_atm ` \<Sigma>\<^sub>w \<union> replacement_pos ` \<Sigma>\<^sub>w \<union>
    replacement_neg ` \<Sigma>\<^sub>w \<union> \<Sigma> \<subseteq> atm_of ` (upostp I)
    \<close>
  apply (auto simp: upostp_def image_Un image_image)
  apply (metis (mono_tags, lifting) imageI literal.sel(1) mem_Collect_eq)
  apply (metis (mono_tags, lifting) imageI literal.sel mem_Collect_eq)
  done

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
    \<Sigma> \<Sigma>\<^sub>w
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
    \<Sigma> \<Sigma>\<^sub>w :: \<open>'v set\<close> and
    new_vars :: \<open>'v \<Rightarrow> 'v \<times> 'v \<times> 'v\<close> +
  assumes
    finite_\<Sigma>:
      \<open>finite \<Sigma>\<^sub>w\<close> and
    \<Sigma>\<^sub>w_\<Sigma>:
      \<open>\<Sigma>\<^sub>w \<subseteq> \<Sigma>\<close> and
    new_vars_pos:
      \<open>A \<in> \<Sigma>\<^sub>w \<Longrightarrow> replacement_pos A \<notin> \<Sigma>\<close> and
    new_vars_neg:
      \<open>A \<in> \<Sigma>\<^sub>w \<Longrightarrow> replacement_neg A \<notin> \<Sigma>\<close> and
    new_vars_addition_var:
      \<open>A \<in> \<Sigma>\<^sub>w \<Longrightarrow> additional_atm A \<notin> \<Sigma>\<close> and
    new_vars_dist:
      \<open>A \<in> \<Sigma>\<^sub>w \<Longrightarrow> B \<in> \<Sigma>\<^sub>w \<Longrightarrow> A \<noteq> B \<Longrightarrow> replacement_pos A \<noteq> replacement_pos B\<close>
      \<open>A \<in> \<Sigma>\<^sub>w \<Longrightarrow> B \<in> \<Sigma>\<^sub>w \<Longrightarrow> replacement_pos A \<noteq> replacement_neg B\<close>
      \<open>A \<in> \<Sigma>\<^sub>w \<Longrightarrow> B \<in> \<Sigma>\<^sub>w \<Longrightarrow> A \<noteq> B \<Longrightarrow> replacement_neg A \<noteq> replacement_neg B\<close>
      \<open>A \<in> \<Sigma>\<^sub>w \<Longrightarrow> B \<in> \<Sigma>\<^sub>w \<Longrightarrow> replacement_pos A \<noteq> additional_atm B\<close>
      \<open>A \<in> \<Sigma>\<^sub>w \<Longrightarrow> B \<in> \<Sigma>\<^sub>w \<Longrightarrow> replacement_neg A \<noteq> additional_atm B\<close>
      \<open>A \<in> \<Sigma>\<^sub>w \<Longrightarrow> B \<in> \<Sigma>\<^sub>w \<Longrightarrow> A \<noteq> B \<Longrightarrow> additional_atm A \<noteq> additional_atm B\<close> and
    \<Sigma>_no_weight:
      \<open>atm_of C \<in> \<Sigma> - \<Sigma>\<^sub>w \<Longrightarrow> \<rho> (add_mset C M) = \<rho> M\<close>
begin

lemma consistent_interp_postp:
  \<open>consistent_interp I \<Longrightarrow> consistent_interp (postp I)\<close>
  by (auto simp: consistent_interp_def postp_def)

text \<open>The reverse of the previous theorem does not hold due to the filtering on the variables of
  \<^term>\<open>\<Sigma>\<^sub>w\<close>. One example of version that holds:\<close>
lemma
  assumes \<open>A \<in> \<Sigma>\<^sub>w\<close>
  shows \<open>consistent_interp (postp {Pos A , Neg A})\<close> and
    \<open>\<not>consistent_interp {Pos A, Neg A}\<close>
  using assms \<Sigma>\<^sub>w_\<Sigma>
  using new_vars_addition_var
  by (auto simp: consistent_interp_def postp_def uminus_lit_swap)

text \<open>Some more restricted version of the reverse hold, like:\<close>
lemma consistent_interp_postp_iff:
  \<open>atm_of ` I \<subseteq> \<Sigma> - \<Sigma>\<^sub>w \<Longrightarrow> consistent_interp I \<longleftrightarrow> consistent_interp (postp I)\<close>
  by (auto simp: consistent_interp_def postp_def)

lemma new_vars_different_iff[simp]:
  \<open>A \<noteq> x\<^sup>\<mapsto>\<^sup>+\<close>
  \<open>A \<noteq> x\<^sup>\<mapsto>\<^sup>-\<close>
  \<open>x\<^sup>\<mapsto>\<^sup>+ \<noteq> A\<close>
  \<open>x\<^sup>\<mapsto>\<^sup>- \<noteq> A\<close>
  \<open>A\<^sup>\<mapsto>\<^sup>- \<noteq> x\<^sup>\<mapsto>\<^sup>+\<close>
  \<open>A\<^sup>\<mapsto>\<^sup>+ \<noteq> x\<^sup>\<mapsto>\<^sup>-\<close>
  \<open>x \<noteq> additional_atm x\<close>
  \<open>A\<^sup>\<mapsto>\<^sup>- \<noteq> additional_atm x\<close>
  \<open>A\<^sup>\<mapsto>\<^sup>+ \<noteq> additional_atm x\<close>
  \<open>additional_atm x \<noteq> x\<close>
  \<open>additional_atm x \<noteq> A\<^sup>\<mapsto>\<^sup>-\<close>
  \<open>additional_atm x \<noteq> A\<^sup>\<mapsto>\<^sup>+\<close>
  \<open>A\<^sup>\<mapsto>\<^sup>- = x\<^sup>\<mapsto>\<^sup>- \<longleftrightarrow> A = x\<close>
  \<open>A\<^sup>\<mapsto>\<^sup>+ = x\<^sup>\<mapsto>\<^sup>+ \<longleftrightarrow> A = x\<close>
  \<open>additional_atm A = additional_atm x \<longleftrightarrow> A = x\<close>
  \<open>(A\<^sup>\<mapsto>\<^sup>+) \<notin> \<Sigma>\<close>
  \<open>(A\<^sup>\<mapsto>\<^sup>-) \<notin> \<Sigma>\<close>
  \<open>additional_atm A \<notin> \<Sigma>\<close>
  \<open>(A\<^sup>\<mapsto>\<^sup>+) \<notin> \<Sigma>\<^sub>w\<close>
  \<open>(A\<^sup>\<mapsto>\<^sup>-) \<notin> \<Sigma>\<^sub>w\<close>
  \<open>additional_atm A \<notin> \<Sigma>\<^sub>w\<close>
  if \<open>A \<in> \<Sigma>\<^sub>w\<close>  \<open>x \<in> \<Sigma>\<^sub>w\<close> for A x
  using \<Sigma>\<^sub>w_\<Sigma> new_vars_pos[of x] new_vars_pos[of A]  new_vars_neg[of x] new_vars_neg[of A]
    new_vars_neg new_vars_dist[of A x] new_vars_dist[of x A]
    new_vars_addition_var[of x] new_vars_addition_var[of A] that new_vars_addition_var[of x]
  by (cases \<open>A = x\<close>; fastforce simp: comp_def; fail)+

lemma consistent_interp_upostp:
  \<open>consistent_interp I \<Longrightarrow> consistent_interp (upostp I)\<close>
  using \<Sigma>\<^sub>w_\<Sigma>
  using new_vars_addition_var
  by (auto simp: consistent_interp_def upostp_def uminus_lit_swap)

lemma upostp_additional_constraints_logic:
  assumes
    \<open>A \<in> \<Sigma>\<^sub>w\<close>
  shows
    \<open>Pos (A\<^sup>\<mapsto>\<^sup>+) \<in> upostp I \<longleftrightarrow> (additional_var A \<in> upostp I \<and> Pos A \<in> upostp I)\<close> (is ?A) and
    \<open>Pos (A\<^sup>\<mapsto>\<^sup>-) \<in> upostp I \<longleftrightarrow> (additional_var A \<in> upostp I \<and> Neg A \<in> upostp I)\<close> (is ?B)
proof -
  show ?A
  proof
    assume \<open>Pos (A\<^sup>\<mapsto>\<^sup>+) \<in> upostp I\<close>
    then have \<open>Pos (A\<^sup>\<mapsto>\<^sup>+) \<in> (\<lambda>x. Pos (x\<^sup>\<mapsto>\<^sup>+)) ` {A \<in> \<Sigma>\<^sub>w. Pos A \<in> I}\<close>
      using assms
      by (auto simp add: upostp_def image_image)
    then have \<open>Pos A \<in> I\<close>
      using assms
      by auto
    moreover have \<open>additional_var A \<in> upostp I\<close>
      using assms \<open>Pos A \<in> I\<close>
      by (auto simp add: upostp_def image_image)
    moreover have \<open>Pos A \<in> upostp I\<close>
      using \<Sigma>\<^sub>w_\<Sigma> assms \<open>Pos A \<in> I\<close>
      by (auto simp add: upostp_def image_image)
    ultimately show \<open>additional_var A \<in> upostp I \<and> Pos A \<in> upostp I\<close>
      by auto
  next
    assume \<open>additional_var A \<in> upostp I \<and> Pos A \<in> upostp I\<close>
    then have \<open>Pos A \<in> I\<close>
      using assms
      by (auto simp add: upostp_def image_image)
    then show \<open>Pos (A\<^sup>\<mapsto>\<^sup>+) \<in> upostp I\<close>
      using assms
      by (auto simp add: upostp_def image_image)
  qed

  show ?B
    using assms \<Sigma>\<^sub>w_\<Sigma>
    by (auto simp add: upostp_def image_image)
qed

lemma preprocessed_clss_ent_upostp:
  assumes \<Sigma>: \<open>atms_of_mm N = \<Sigma>\<close> and
    sat: \<open>I \<Turnstile>sm N\<close> and
    cons: \<open>consistent_interp I\<close> and
    atm: \<open>atm_of ` I \<subseteq> atms_of_mm N\<close>
  shows \<open>upostp I \<Turnstile>m preprocessed_clss N\<close>
proof -
  have [iff]: \<open>Pos (A\<^sup>\<mapsto>\<^sup>-) \<notin> I\<close> \<open>Pos (A\<^sup>\<mapsto>\<^sup>+) \<notin> I\<close> \<open>additional_var A \<notin> I\<close> \<open>Neg (additional_atm A) \<notin> I\<close>
     \<open>Neg (A\<^sup>\<mapsto>\<^sup>-) \<notin> I\<close> \<open>Neg (A\<^sup>\<mapsto>\<^sup>+) \<notin> I\<close>  if \<open>A \<in> \<Sigma>\<^sub>w\<close> for A
    using atm new_vars_neg[of A] new_vars_pos[of A] that new_vars_addition_var[of A]
    unfolding \<Sigma> by force+
  have enc: \<open>upostp I \<Turnstile>m encode_clauses N\<close>
    unfolding true_cls_mset_def
  proof
    fix C
    assume \<open>C \<in># encode_clauses N\<close>
    then obtain C' where
      \<open>C' \<in># N\<close> and
      \<open>C = encode_clause C'\<close>
      by (auto simp: encode_clauses_def)
    then obtain A where
      \<open>A \<in># C'\<close> and
      \<open>A \<in> I\<close>
      using sat
      by (auto simp: true_cls_def
        dest!: multi_member_split[of _ N])
    moreover have \<open>atm_of A \<in> \<Sigma> - \<Sigma>\<^sub>w \<or> atm_of A \<in> \<Sigma>\<^sub>w\<close>
      using atm \<open>A \<in> I\<close> unfolding \<Sigma> by blast
    ultimately have \<open>encode_lit A \<in> upostp I\<close>
      by (auto simp: encode_lit_alt_def upostp_def)
    then show \<open>upostp I \<Turnstile> C\<close>
      using \<open>A \<in># C'\<close>
      unfolding \<open>C = encode_clause C'\<close>
      by (auto simp: encode_clause_def dest: multi_member_split)
  qed
  have [iff]: \<open>Pos (y\<^sup>\<mapsto>\<^sup>+) \<notin> upostp I \<longleftrightarrow> Neg (y\<^sup>\<mapsto>\<^sup>+) \<in> upostp I\<close>
     \<open>Pos (y\<^sup>\<mapsto>\<^sup>-) \<notin> upostp I \<longleftrightarrow> Neg (y\<^sup>\<mapsto>\<^sup>-) \<in> upostp I\<close>
    \<open>Neg (additional_atm y) \<notin> upostp I \<longleftrightarrow> additional_var y \<in> upostp I\<close>
    if \<open>y \<in> \<Sigma>\<^sub>w\<close> for y
    using that
    by (cases \<open>Pos y \<in> I\<close>; auto simp: upostp_def image_image; fail)+
  have H:
    \<open>Pos y \<notin> upostp I \<longleftrightarrow> Neg y \<in> upostp I\<close>
    if \<open>y \<in> \<Sigma>\<^sub>w\<close> for y
    using that cons \<Sigma>\<^sub>w_\<Sigma> unfolding consistent_interp_def
    using that by (cases \<open>Pos y \<in> I\<close>; auto simp: upostp_def image_image)
  have [dest]: \<open>Neg A \<in> upostp I \<Longrightarrow> Pos A \<notin> upostp I\<close>
     \<open>Pos A \<in> upostp I \<Longrightarrow> Neg A \<notin> upostp I\<close> for A
    using consistent_interp_upostp[OF cons]
    by (auto simp: consistent_interp_def)

  have add: \<open>upostp I \<Turnstile>m additional_constraints\<close>
    using finite_\<Sigma>
    apply (auto simp: additional_constraints_def true_cls_mset_def additional_constraint_def)
    subgoal for y
      using cons upostp_additional_constraints_logic[of y I]
      by (auto simp: image_image)
    subgoal for y
      using cons upostp_additional_constraints_logic[of y I]
      by (auto simp: image_image)
    subgoal for y
      using cons upostp_additional_constraints_logic[of y I] H[of y]
      by (auto simp: image_image)
    subgoal for y
      using cons upostp_additional_constraints_logic[of y I]
      by (auto simp: image_image)
    subgoal for y
      using cons upostp_additional_constraints_logic[of y I]
      by (auto simp: image_image)
    subgoal for y
      using cons upostp_additional_constraints_logic[of y I] H[of y]
      by (auto simp: image_image consistent_interp_def)
    done

  show \<open>upostp I \<Turnstile>m preprocessed_clss N\<close>
    using enc add unfolding preprocessed_clss_def by auto
qed

lemma satisfiable_preprocessed_clss:
  assumes \<Sigma>: \<open>atms_of_mm N = \<Sigma>\<close> and
    sat: \<open>satisfiable (set_mset N)\<close>
  shows \<open>satisfiable (set_mset (preprocessed_clss N))\<close>
  using assms
  apply (subst (asm) satisfiable_def_min)
  apply clarify
  subgoal for I
    using preprocessed_clss_ent_upostp[of N I] consistent_interp_upostp[of I]
    by auto
  done

lemma preprocessed_clss_ent_postp:
  assumes \<Sigma>: \<open>atms_of_mm N = \<Sigma>\<close> and
    sat: \<open>I \<Turnstile>sm preprocessed_clss N\<close> and
    cons: \<open>consistent_interp I\<close>
  shows \<open>postp I \<Turnstile>m N\<close>
proof -
  have enc: \<open>I \<Turnstile>m encode_clauses N\<close> and \<open>I \<Turnstile>m additional_constraints\<close>
    using sat unfolding preprocessed_clss_def
    by auto

  show \<open>postp I \<Turnstile>m N\<close>
    unfolding true_cls_mset_def
  proof
    fix C
    assume \<open>C \<in># N\<close>
    then have \<open>I \<Turnstile> encode_clause C\<close>
      using enc by (auto dest!: multi_member_split)
    then show \<open>postp I \<Turnstile> C\<close>
      unfolding true_cls_def
      using cons finite_\<Sigma> preprocess_clss_model_additional_variables[of I N] sat
        preprocess_clss_model_additional_variables2[of _ I]
        \<Sigma> \<open>C \<in># N\<close> in_m_in_literals
      apply (auto simp: encode_clause_def postp_def encode_lit_alt_def
        split: if_splits
        dest!: multi_member_split[of _ C])
      by blast (*TODO proof*)
  qed
qed

lemma satisfiable_preprocessed_clss_satisfiable:
  assumes \<Sigma>: \<open>atms_of_mm N = \<Sigma>\<close> and
    sat: \<open>satisfiable (set_mset (preprocessed_clss N))\<close>
  shows \<open>satisfiable (set_mset N)\<close>
  using assms apply (subst (asm) satisfiable_def)
  apply clarify
  subgoal for I
    using preprocessed_clss_ent_postp[OF \<Sigma>, of I] consistent_interp_postp[of I]
    by auto
  done

lemma satisfiable_preprocessed_clss_iff:
  assumes \<Sigma>: \<open>atms_of_mm N = \<Sigma>\<close>
  shows \<open>satisfiable (set_mset (preprocessed_clss N)) \<longleftrightarrow> satisfiable (set_mset N)\<close>
  using assms satisfiable_preprocessed_clss satisfiable_preprocessed_clss_satisfiable by blast


abbreviation \<rho>\<^sub>e_filter :: \<open>'v literal multiset \<Rightarrow> 'v literal multiset\<close> where
  \<open>\<rho>\<^sub>e_filter M \<equiv> filter_mset (\<lambda>x. atm_of x \<in> \<Sigma>\<^sub>w \<and> additional_var (atm_of x) \<in># M) M\<close>

definition \<rho>\<^sub>e :: \<open>'v literal multiset \<Rightarrow> nat\<close> where
  \<open>\<rho>\<^sub>e M = \<rho> (\<rho>\<^sub>e_filter M)\<close>

lemma \<rho>\<^sub>e_mono: \<open>A \<subseteq># B \<Longrightarrow> \<rho>\<^sub>e A \<le> \<rho>\<^sub>e B\<close>
  unfolding \<rho>\<^sub>e_def
  apply (rule \<rho>_mono)
  apply (rule filter_mset_mono_subset)
  apply auto
  done

interpretation enc_weight_opt: conflict_driven_clause_learning\<^sub>W_optimal_weight where
    state_eq = state_eq and
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
    \<rho> = \<rho>\<^sub>e and
    update_additional_info = update_additional_info
  apply unfold_locales
  subgoal by (rule \<rho>\<^sub>e_mono)
  subgoal using update_additional_info by fast
  subgoal using weight_init_state by fast
  done

lemma  \<Sigma>_no_weight_\<rho>\<^sub>e: \<open>atm_of C \<in> \<Sigma> - \<Sigma>\<^sub>w \<Longrightarrow> \<rho>\<^sub>e (add_mset C M) = \<rho>\<^sub>e M\<close>
  using \<Sigma>_no_weight[of C \<open>\<rho>\<^sub>e_filter M\<close>]
  apply (auto simp: \<rho>\<^sub>e_def)
  by (metis (no_types, lifting) literal.sel(1) new_vars_addition_var)


lemma \<rho>_cancel_notin_\<Sigma>\<^sub>w:
  \<open>(\<And>x. x \<in># M \<Longrightarrow> atm_of x \<in> \<Sigma> - \<Sigma>\<^sub>w) \<Longrightarrow> \<rho> (M + M') = \<rho> M'\<close>
  by (induction M) (auto simp: \<Sigma>_no_weight)

lemma \<rho>_mono2:
  \<open>(\<And>A. A \<in># M \<Longrightarrow> atm_of A \<in> \<Sigma>) \<Longrightarrow> (\<And>A. A \<in># M' \<Longrightarrow> atm_of A \<in> \<Sigma>) \<Longrightarrow>
     {#A \<in># M. atm_of A \<in> \<Sigma>\<^sub>w#} \<subseteq># {#A \<in># M'. atm_of A \<in> \<Sigma>\<^sub>w#} \<Longrightarrow> \<rho> M \<le> \<rho> M'\<close>
  apply (subst (2) multiset_partition[of _ \<open>\<lambda>A. atm_of A \<notin> \<Sigma>\<^sub>w\<close>])
  apply (subst multiset_partition[of _ \<open>\<lambda>A. atm_of A \<notin> \<Sigma>\<^sub>w\<close>])
  apply (subst \<rho>_cancel_notin_\<Sigma>\<^sub>w)
  subgoal by auto
  apply (subst \<rho>_cancel_notin_\<Sigma>\<^sub>w)
  subgoal by auto
  by (auto intro: \<rho>_mono)

lemma \<rho>\<^sub>e_upostp_\<rho>:
  assumes \<open>finite \<Sigma>\<close> and
    \<open>finite I\<close> and
    I_\<Sigma>: \<open>atm_of ` I \<subseteq> \<Sigma>\<close>
  shows \<open>\<rho>\<^sub>e (mset_set (upostp I)) = \<rho> (mset_set I)\<close> (is \<open>?A = ?B\<close>)
proof -
  have [simp]: \<open>finite I\<close>
    using assms by auto
  have [simp]: \<open>mset_set
        {x \<in> I.
         atm_of x \<in> \<Sigma> \<and>
         atm_of x \<notin> replacement_pos ` \<Sigma>\<^sub>w \<and>
         atm_of x \<notin> replacement_neg ` \<Sigma>\<^sub>w \<and> atm_of x \<notin> additional_atm ` \<Sigma>\<^sub>w} = mset_set I\<close>
    using I_\<Sigma> by auto
  have [simp]: \<open>finite {A \<in> \<Sigma>\<^sub>w. P A}\<close> for P
    by (rule finite_subset[of _ \<Sigma>\<^sub>w])
      (use \<Sigma>\<^sub>w_\<Sigma> finite_\<Sigma> in auto)
  have \<open>?A \<le> ?B\<close>
    using assms \<Sigma>\<^sub>w_\<Sigma> apply -
    unfolding \<rho>\<^sub>e_def filter_filter_mset
    apply (rule \<rho>_mono2)
    subgoal by auto
    subgoal by auto
    apply (rule filter_mset_mono_subset)
    subgoal by  (auto simp: upostp_def)
    subgoal for x
      by (cases \<open>x \<in> I\<close>; cases x) (auto simp: upostp_def)
    done
  moreover have \<open>?B \<le> ?A\<close>
    using assms \<Sigma>\<^sub>w_\<Sigma> apply -
    unfolding \<rho>\<^sub>e_def filter_filter_mset
    apply (rule \<rho>_mono2)
    subgoal by auto
    subgoal by auto
    unfolding filter_filter_mset
    apply (rule filter_mset_mono_subset)
    subgoal by  (auto simp: upostp_def)
    subgoal for x
      by (cases \<open>x \<in> I\<close>; cases x) (auto simp: upostp_def)
    done
  ultimately show ?thesis
    by simp
qed


lemma \<rho>_postp_\<rho>\<^sub>e:
  assumes \<open>finite \<Sigma>\<close> and
    \<open>finite I\<close> and
    I_\<Sigma>: \<open>atm_of ` I \<subseteq> \<Sigma> \<union> \<Sigma>\<^sub>a\<^sub>d\<^sub>d\<close>
  shows \<open>\<rho>\<^sub>e (mset_set I) \<ge> \<rho> (mset_set (postp I))\<close>
proof -
  have [simp]: \<open>finite I\<close>
    using assms by auto
  have [simp]: \<open>finite {A \<in> I. P A}\<close> for P
    apply (rule finite_subset[of _ \<open>Pos ` atm_of ` I \<union> Neg ` atm_of ` I\<close>])
    apply auto
    by (metis image_iff literal.exhaust_sel)

  show ?thesis
    using assms \<Sigma>\<^sub>w_\<Sigma>
    by (auto simp: postp_def \<rho>\<^sub>e_def \<Sigma>\<^sub>a\<^sub>d\<^sub>d_def conj_disj_distribR
      mset_set_Union intro!: \<rho>_mono2)
qed

lemma encode_lit_eq_iff:
  \<open>atm_of x \<in> \<Sigma> \<Longrightarrow> atm_of y \<in> \<Sigma> \<Longrightarrow> encode_lit x = encode_lit y \<longleftrightarrow> x = y\<close>
  by (cases x; cases y) (auto simp: encode_lit_alt_def atm_of_eq_atm_of)

lemma distinct_mset_encode_clause_iff:
  \<open>atms_of N \<subseteq> \<Sigma> \<Longrightarrow> distinct_mset (encode_clause N) \<longleftrightarrow> distinct_mset N\<close>
  by (induction N)
    (auto simp: encode_clause_def encode_lit_eq_iff
    dest!: multi_member_split)

lemma distinct_mset_encodes_clause_iff:
  \<open>atms_of_mm N \<subseteq> \<Sigma> \<Longrightarrow> distinct_mset_mset (encode_clauses N) \<longleftrightarrow> distinct_mset_mset N\<close>
  by (induction N)
    (auto simp: encode_clauses_def distinct_mset_encode_clause_iff)

lemma distinct_additional_constraints[simp]:
  \<open>distinct_mset_mset additional_constraints\<close>
  by (auto simp: additional_constraints_def additional_constraint_def
    distinct_mset_set_def finite_\<Sigma>)

lemma distinct_mset_preprocessed_clss:
  \<open>atms_of_mm N \<subseteq> \<Sigma> \<Longrightarrow> distinct_mset_mset (preprocessed_clss N) \<longleftrightarrow> distinct_mset_mset N\<close>
  by (auto simp: preprocessed_clss_def
    distinct_mset_encodes_clause_iff)

lemma finite_upostp:
  assumes \<open>finite \<Sigma>\<close>
  shows \<open>finite (upostp I)\<close>
proof -
  have \<open>upostp I \<subseteq> Pos ` (\<Sigma> \<union> \<Sigma>\<^sub>w \<union> \<Sigma>\<^sub>a\<^sub>d\<^sub>d) \<union> Neg ` (\<Sigma> \<union> \<Sigma>\<^sub>w \<union> \<Sigma>\<^sub>a\<^sub>d\<^sub>d)\<close>
    apply (auto simp: upostp_def image_Un \<Sigma>\<^sub>a\<^sub>d\<^sub>d_def)
    by (metis image_iff literal.exhaust_sel)
  moreover have \<open>finite (Pos ` (\<Sigma> \<union> \<Sigma>\<^sub>w \<union> \<Sigma>\<^sub>a\<^sub>d\<^sub>d) \<union> Neg ` (\<Sigma> \<union> \<Sigma>\<^sub>w \<union> \<Sigma>\<^sub>a\<^sub>d\<^sub>d))\<close>
    using assms finite_\<Sigma> by (auto simp: \<Sigma>\<^sub>a\<^sub>d\<^sub>d_def)
  ultimately show ?thesis
    by (auto intro: finite_subset)
qed

theorem full_encoding_OCDCL_correctness:
  assumes
    st: \<open>full enc_weight_opt.cdcl_bab_stgy (init_state (preprocessed_clss N)) T\<close> and
    dist: \<open>distinct_mset_mset N\<close> and
    atms: \<open>atms_of_mm N = \<Sigma>\<close>
  shows
    \<open>weight T = None \<Longrightarrow> unsatisfiable (set_mset N)\<close> and
    \<open>weight T \<noteq> None \<Longrightarrow> postp (set_mset (the (weight T))) \<Turnstile>sm N\<close>
    \<open>weight T \<noteq> None \<Longrightarrow> distinct_mset I \<Longrightarrow> consistent_interp (set_mset I) \<Longrightarrow>
      atms_of I \<subseteq> atms_of_mm N \<Longrightarrow> set_mset I \<Turnstile>sm N \<Longrightarrow>
      \<rho> I \<ge> \<rho> (mset_set (postp (set_mset (the (weight T)))))\<close>
proof -
  let ?N = \<open>preprocessed_clss N\<close>
  have \<open>distinct_mset_mset (preprocessed_clss N)\<close>
    by (subst distinct_mset_preprocessed_clss)
      (use dist atms in auto)
  then have
    unsat: \<open>weight T = None \<Longrightarrow> unsatisfiable (set_mset ?N)\<close> and
    model: \<open>weight T \<noteq> None \<Longrightarrow> consistent_interp (set_mset (the (weight T))) \<and>
       atms_of (the (weight T)) \<subseteq> atms_of_mm ?N \<and> set_mset (the (weight T)) \<Turnstile>sm ?N \<and>
       distinct_mset (the (weight T))\<close> and
    opt: \<open>distinct_mset I \<Longrightarrow> consistent_interp (set_mset I) \<Longrightarrow> atms_of I = atms_of_mm ?N \<Longrightarrow>
      set_mset I \<Turnstile>sm ?N \<Longrightarrow> \<rho>\<^sub>e I \<ge> enc_weight_opt.\<rho>' (weight T)\<close>
    for I
    using enc_weight_opt.full_cdcl_bab_stgy_no_conflicting_clause_from_init_state[of \<open>preprocessed_clss N\<close> T, OF st]
    by fast+

  show \<open>unsatisfiable (set_mset N)\<close> if \<open>weight T = None\<close>
    using unsat[OF that] satisfiable_preprocessed_clss[OF atms] by blast
  let ?K = \<open>postp (set_mset (the (weight T)))\<close>
  show \<open>?K \<Turnstile>sm N\<close> if \<open>weight T \<noteq> None\<close>
    using preprocessed_clss_ent_postp[OF atms, of \<open>set_mset (the (weight T))\<close>] model[OF that]
    by auto
  show \<open>\<rho> I \<ge> \<rho> (mset_set ?K)\<close>
     if Some: \<open>weight T \<noteq> None\<close> and
       dist: \<open>distinct_mset I\<close> and
       cons: \<open>consistent_interp (set_mset I)\<close> and
       atm: \<open>atms_of I \<subseteq> atms_of_mm N\<close> and
       I_N: \<open>set_mset I \<Turnstile>sm N\<close>
  proof -
    let ?I = \<open>mset_set (upostp (set_mset I))\<close>
    have Some': \<open>enc_weight_opt.weight T \<noteq> None\<close>
      using Some by auto
    have [simp]: \<open>finite (upostp (set_mset I))\<close>
      by (rule finite_upostp)
        (use atms in auto)
    then have I: \<open>set_mset ?I = upostp (set_mset I)\<close>
      by auto
    have \<open>set_mset ?I \<Turnstile>m ?N\<close>
      unfolding I
      by (rule preprocessed_clss_ent_upostp[OF atms I_N cons])
        (use atm in \<open>auto dest: multi_member_split\<close>)
    moreover have \<open>distinct_mset ?I\<close>
      by (rule distinct_mset_mset_set)
    moreover {
      have A: \<open>atms_of (mset_set (upostp (set_mset I))) = atm_of ` (upostp (set_mset I))\<close>
        \<open>atm_of ` set_mset I = atms_of I\<close>
        by (auto simp: atms_of_def)
      have \<open>atms_of ?I = atms_of_mm ?N\<close>
        apply (subst atms_of_mm_preprocessed_clss_subset2[OF finite_\<Sigma>])
        subgoal using \<Sigma>\<^sub>w_\<Sigma> atms by auto
        subgoal
          using atm_of_upostp_subset[of \<open>set_mset I\<close>] atm_of_upostp_subset2[of \<open>set_mset I\<close>] atm
          unfolding atms A
          by auto
        done
    }
    moreover have \<open>consistent_interp (set_mset ?I)\<close>
      using cons unfolding I by (rule consistent_interp_upostp)
    ultimately have \<open>\<rho>\<^sub>e ?I \<ge> enc_weight_opt.\<rho>' (weight T)\<close>
      using opt[of ?I] by auto
    moreover {
      have \<open>\<rho>\<^sub>e ?I = \<rho> (mset_set (set_mset I))\<close>
        by (rule \<rho>\<^sub>e_upostp_\<rho>)
          (use \<Sigma>\<^sub>w_\<Sigma> atms atm in \<open>auto dest: multi_member_split\<close>)
      then have \<open>\<rho>\<^sub>e ?I = \<rho> I\<close>
        by (subst (asm) distinct_mset_set_mset_ident)
          (use atms dist in auto)
    }
    ultimately have \<open>\<rho> I \<ge> enc_weight_opt.\<rho>' (weight T)\<close>
      using Some'
      by auto
    moreover {
      have \<open>\<rho> (mset_set ?K) \<le> \<rho>\<^sub>e (the (weight T))\<close>
        unfolding \<rho>\<^sub>e_def
        apply (rule \<rho>_mono2)
        subgoal using atms dist model[OF Some] atms \<Sigma>\<^sub>w_\<Sigma> by (auto simp: postp_def)
        subgoal using atms dist model[OF Some] atms \<Sigma>\<^sub>w_\<Sigma> by (auto simp: postp_def)
        subgoal
          unfolding filter_filter_mset
          apply (rule filter_mset_mono_subset)
          subgoal
            apply (subst distinct_subseteq_iff[symmetric])
            using dist model[OF Some]
            by (auto simp: postp_def distinct_mset_mset_set)
          subgoal by (auto simp: postp_def)
          done
        done
       then have \<open>\<rho> (mset_set ?K) \<le> enc_weight_opt.\<rho>' (weight T)\<close>
         using Some by auto
    }
    moreover {
      have \<open>\<rho>\<^sub>e (mset_set ?K) \<le> \<rho>\<^sub>e (mset_set (set_mset (the (weight T))))\<close>
        unfolding \<rho>\<^sub>e_def
        apply (rule \<rho>_mono2)
        subgoal using atms dist model[OF Some] atms \<Sigma>\<^sub>w_\<Sigma> by (auto simp: postp_def)
        subgoal using atms dist model[OF Some] atms \<Sigma>\<^sub>w_\<Sigma> by (auto simp: postp_def)
        subgoal
          unfolding filter_filter_mset
          apply (rule filter_mset_mono_subset)
          by (auto simp: postp_def)
        done
      then have \<open>\<rho>\<^sub>e (mset_set ?K) \<le> enc_weight_opt.\<rho>' (weight T)\<close>
        apply (subst (asm) distinct_mset_set_mset_ident)
         apply (use atms dist model[OF Some] in auto; fail)[]
         using Some' by auto
    }
    moreover have \<open>\<rho>\<^sub>e (mset_set ?K) \<le> \<rho> (mset_set ?K)\<close>
      unfolding \<rho>\<^sub>e_def
      apply (rule \<rho>_mono2)
      subgoal using atms dist model[OF Some] atms \<Sigma>\<^sub>w_\<Sigma> by (auto simp: postp_def)
      subgoal using atms dist model[OF Some] atms \<Sigma>\<^sub>w_\<Sigma> by (auto simp: postp_def)
      subgoal
        unfolding filter_filter_mset
        apply (rule filter_mset_mono_subset)
        by (auto simp: postp_def)
      done
    ultimately show ?thesis
      using Some' by auto
  qed
qed

end


definition weight_on_clauses where
  \<open>weight_on_clauses N\<^sub>S \<rho> I = (\<Sum>C \<in># (filter_mset (\<lambda>C. I \<Turnstile> C) N\<^sub>S). \<rho> C)\<close>

definition bitotal_over_m :: \<open>'v partial_interp \<Rightarrow> 'v clauses \<Rightarrow> bool\<close> where
\<open>bitotal_over_m I N \<longleftrightarrow>
  total_over_m I (set_mset N) \<and>
  atms_of_s I \<subseteq> atms_of_mm N\<close>

text \<open>Partial in the name refers to the fact that not all clauses are soft clauses, not to the fact
  that we consider partial models.\<close>
inductive partial_max_sat :: \<open>'v clauses \<Rightarrow> 'v clauses \<Rightarrow> ('v clause \<Rightarrow> nat) \<Rightarrow>
  'v partial_interp option \<Rightarrow> bool\<close> where
partial_max_sat:
  \<open>partial_max_sat N\<^sub>H N\<^sub>S \<rho> (Some I)\<close>
  if
    \<open>I \<Turnstile>sm N\<^sub>H\<close> and
    \<open>bitotal_over_m I ((N\<^sub>H + N\<^sub>S))\<close> and
    \<open>consistent_interp I\<close> and
    \<open>\<And>I'. consistent_interp I' \<Longrightarrow> bitotal_over_m I' (N\<^sub>H + N\<^sub>S) \<Longrightarrow> I' \<Turnstile>sm N\<^sub>H \<Longrightarrow>
      weight_on_clauses N\<^sub>S \<rho> I' \<le> weight_on_clauses N\<^sub>S \<rho> I\<close> |
partial_max_unsat:
  \<open>partial_max_sat N\<^sub>H N\<^sub>S \<rho> None\<close>
  if
  \<open>unsatisfiable (set_mset N\<^sub>H)\<close>

inductive partial_min_sat :: \<open>'v clauses \<Rightarrow> 'v clauses \<Rightarrow> ('v clause \<Rightarrow> nat) \<Rightarrow>
  'v partial_interp option \<Rightarrow> bool\<close> where
partial_min_sat:
  \<open>partial_min_sat N\<^sub>H N\<^sub>S \<rho> (Some I)\<close>
  if
    \<open>I \<Turnstile>sm N\<^sub>H\<close> and
    \<open>bitotal_over_m I (N\<^sub>H + N\<^sub>S)\<close> and
    \<open>consistent_interp I\<close> and
    \<open>\<And>I'. consistent_interp I' \<Longrightarrow> bitotal_over_m I' (N\<^sub>H + N\<^sub>S) \<Longrightarrow> I' \<Turnstile>sm N\<^sub>H \<Longrightarrow>
      weight_on_clauses N\<^sub>S \<rho> I' \<ge> weight_on_clauses N\<^sub>S \<rho> I\<close> |
partial_min_unsat:
  \<open>partial_min_sat N\<^sub>H N\<^sub>S \<rho> None\<close>
  if
  \<open>unsatisfiable (set_mset N\<^sub>H)\<close>

lemma bitotal_over_m_finite:
  assumes \<open>bitotal_over_m I N\<close>
  shows \<open>finite I\<close>
proof -
  have \<open>I \<subseteq> Pos ` (atms_of_mm N) \<union> Neg ` atms_of_mm N\<close>
    using assms by (force simp: total_over_m_def  bitotal_over_m_def lit_in_set_iff_atm
      atms_of_s_def)
  from finite_subset[OF this] show ?thesis by auto
qed


lemma mset_set_eq_mset_iff: \<open>finite x \<Longrightarrow>  mset_set x = mset xs \<longleftrightarrow> distinct xs \<and> x = set xs\<close>
  apply (auto simp flip: distinct_mset_mset_distinct eq_commute[of _ \<open>mset_set _\<close>]
    simp: distinct_mset_mset_set mset_set_set)
  apply (metis finite_set_mset_mset_set set_mset_mset)
  apply (metis finite_set_mset_mset_set set_mset_mset)
  done

lemma consistent_interp_tuatology_mset_set:
  \<open>finite x \<Longrightarrow> consistent_interp x  \<longleftrightarrow> \<not>tautology (mset_set x)\<close>
  using ex_mset[of \<open>mset_set x\<close>]
  by (auto simp: consistent_interp_tautology eq_commute[of \<open>mset _\<close>] mset_set_eq_mset_iff
      mset_set_set)

lemma
  fixes N\<^sub>H :: \<open>'v clauses\<close>
  assumes \<open>satisfiable (set_mset N\<^sub>H)\<close>
  shows sat_partial_max_sat: \<open>\<exists>I. partial_max_sat N\<^sub>H N\<^sub>S \<rho> (Some I)\<close> and
    sat_partial_min_sat: \<open>\<exists>I. partial_min_sat N\<^sub>H N\<^sub>S \<rho> (Some I)\<close>
proof -
  let ?Is = \<open>{I. bitotal_over_m I ((N\<^sub>H + N\<^sub>S)) \<and>  consistent_interp I \<and>
     I \<Turnstile>sm N\<^sub>H}\<close>
  let ?Is'= \<open>{I. bitotal_over_m I ((N\<^sub>H + N\<^sub>S)) \<and> consistent_interp I \<and>
    I \<Turnstile>sm N\<^sub>H \<and> finite I}\<close>
  have Is: \<open>?Is = ?Is'\<close>
    by (auto simp: atms_of_s_def bitotal_over_m_finite)
  have \<open>?Is' \<subseteq> set_mset ` simple_clss (atms_of_mm (N\<^sub>H + N\<^sub>S))\<close>
    apply rule
    unfolding image_iff
    by (rule_tac x= \<open>mset_set x\<close> in bexI)
      (auto simp: simple_clss_def bitotal_over_m_def image_iff
      atms_of_s_def atms_of_def distinct_mset_mset_set consistent_interp_tuatology_mset_set)
  from finite_subset[OF this] have fin: \<open>finite ?Is\<close> unfolding Is
    by (auto simp: simple_clss_finite)
  then have fin': \<open>finite (weight_on_clauses N\<^sub>S \<rho> ` ?Is)\<close>
    by auto
  define \<rho>I where
    \<open>\<rho>I = Min (weight_on_clauses N\<^sub>S \<rho> ` ?Is)\<close>
  have nempty: \<open>?Is \<noteq> {}\<close>
  proof -
    obtain I where I:
      \<open>total_over_m I (set_mset N\<^sub>H)\<close>
      \<open>I \<Turnstile>sm N\<^sub>H\<close>
      \<open>consistent_interp I\<close>
      \<open>atms_of_s I \<subseteq> atms_of_mm N\<^sub>H\<close>
      using assms unfolding satisfiable_def_min bitotal_over_m_def
      by (auto simp: atms_of_s_def atm_of_def total_over_m_def)
    let ?I = \<open>I \<union> Pos ` {x \<in> atms_of_mm N\<^sub>S. x \<notin> atm_of ` I}\<close>
    have \<open>?I \<in> ?Is\<close>
      using I
      by (auto simp: bitotal_over_m_def total_over_m_alt_def image_iff
        lit_in_set_iff_atm)
        (auto simp: consistent_interp_def uminus_lit_swap)
    then show ?thesis
      by blast
  qed
  have \<open>\<rho>I \<in> weight_on_clauses N\<^sub>S \<rho> ` ?Is\<close>
    unfolding \<rho>I_def
    by (rule Min_in[OF fin']) (use nempty in auto)
  then obtain I :: \<open>'v partial_interp\<close> where
    \<open>weight_on_clauses N\<^sub>S \<rho> I = \<rho>I\<close> and
    \<open>I \<in> ?Is\<close>
    by blast
  then have H: \<open>consistent_interp I' \<Longrightarrow> bitotal_over_m I' (N\<^sub>H + N\<^sub>S) \<Longrightarrow> I' \<Turnstile>sm N\<^sub>H \<Longrightarrow>
      weight_on_clauses N\<^sub>S \<rho> I' \<ge> weight_on_clauses N\<^sub>S \<rho> I\<close> for I'
    using Min_le[OF fin', of \<open>weight_on_clauses N\<^sub>S \<rho> I'\<close>]
    unfolding \<rho>I_def[symmetric]
    by auto
  then have \<open>partial_min_sat N\<^sub>H N\<^sub>S \<rho> (Some I)\<close>
    apply -
    by (rule partial_min_sat)
      (use fin \<open>I \<in> ?Is\<close> in \<open>auto simp: bitotal_over_m_finite\<close>)
  then show \<open>\<exists>I. partial_min_sat N\<^sub>H N\<^sub>S \<rho> (Some I)\<close>
    by fast

  define \<rho>I where
    \<open>\<rho>I = Max (weight_on_clauses N\<^sub>S \<rho> ` ?Is)\<close>
  have \<open>\<rho>I \<in> weight_on_clauses N\<^sub>S \<rho> ` ?Is\<close>
    unfolding \<rho>I_def
    by (rule Max_in[OF fin']) (use nempty in auto)
  then obtain I :: \<open>'v partial_interp\<close> where
    \<open>weight_on_clauses N\<^sub>S \<rho> I = \<rho>I\<close> and
    \<open>I \<in> ?Is\<close>
    by blast
  then have H: \<open>consistent_interp I' \<Longrightarrow> bitotal_over_m I' (N\<^sub>H + N\<^sub>S) \<Longrightarrow> I' \<Turnstile>m N\<^sub>H \<Longrightarrow>
      weight_on_clauses N\<^sub>S \<rho> I' \<le> weight_on_clauses N\<^sub>S \<rho> I\<close> for I'
    using Max_ge[OF fin', of \<open>weight_on_clauses N\<^sub>S \<rho> I'\<close>]
    unfolding \<rho>I_def[symmetric]
    by auto
  then have \<open>partial_max_sat N\<^sub>H N\<^sub>S \<rho> (Some I)\<close>
    apply -
    by (rule partial_max_sat)
      (use fin \<open>I \<in> ?Is\<close> in \<open>auto simp: bitotal_over_m_finite
        consistent_interp_tuatology_mset_set\<close>)
  then show \<open>\<exists>I. partial_max_sat N\<^sub>H N\<^sub>S \<rho> (Some I)\<close>
    by fast
qed

lemma sumset_diff_constant_left:
  assumes \<open>\<And>x. x \<in># A \<Longrightarrow> f x \<le> n\<close>
  shows \<open>(\<Sum>x\<in># A . n - f x) = size A * n - (\<Sum>x\<in># A . f x)\<close>
proof -
  have \<open>size A * n \<ge> (\<Sum>x\<in># A . f x)\<close>
    if \<open>\<And>x. x \<in># A \<Longrightarrow> f x \<le> n\<close> for A
    using that
    by (induction A) (force simp: ac_simps)+
  then show ?thesis
    using assms
    by (induction A) (auto simp: ac_simps)
qed

inductive weight_sat :: \<open>'v clauses \<Rightarrow> ('v literal multiset \<Rightarrow> nat) \<Rightarrow> 'v literal multiset option \<Rightarrow>
  bool\<close> where
weight_sat:
  \<open>weight_sat N \<rho> (Some I)\<close>
  if
    \<open>set_mset I \<Turnstile>sm N\<close> and
    \<open>bitotal_over_m (set_mset I) N\<close> and
    \<open>consistent_interp (set_mset I)\<close> and
    \<open>distinct_mset I\<close>
    \<open>\<And>I'. consistent_interp (set_mset I') \<Longrightarrow> bitotal_over_m (set_mset I') N \<Longrightarrow> distinct_mset I' \<Longrightarrow>
      set_mset I' \<Turnstile>sm N \<Longrightarrow> \<rho> I' \<ge> \<rho> I\<close> |
partial_max_unsat:
  \<open>weight_sat N \<rho> None\<close>
  if
  \<open>unsatisfiable (set_mset N)\<close>

lemma true_cls_mset_empty_iff[simp]: \<open>{} \<Turnstile>m C \<longleftrightarrow> C = {#}\<close>
  by (cases C)  auto

lemma true_cls_mset_restrict:
  \<open>{L \<in> I. atm_of L \<in> atms_of_mm N} \<Turnstile>m N \<longleftrightarrow> I \<Turnstile>m N\<close>
  by (auto simp: true_cls_mset_def true_cls_def
    dest!: multi_member_split)

lemma true_clss_restrict:
  \<open>{L \<in> I. atm_of L \<in> atms_of_mm N} \<Turnstile>sm N \<longleftrightarrow> I \<Turnstile>sm N\<close>
  by (auto simp: true_clss_def true_cls_def
    dest!: multi_member_split)

lemma true_clss_mono_left:
  \<open>I \<Turnstile>s A \<Longrightarrow> I \<subseteq> J \<Longrightarrow> J \<Turnstile>s A\<close>
  by (metis sup.orderE true_clss_union_increase')

lemma sum_mset_mset_set_sum_set:
  \<open>(\<Sum>A \<in># mset_set As. f A) = (\<Sum>A \<in> As. f A)\<close>
  apply (cases \<open>finite As\<close>)
  by (induction As rule: finite_induct) auto

lemma sum_mset_sum_count:
  \<open>(\<Sum>A \<in># As. f A) = (\<Sum>A \<in> set_mset As. count As A * f A)\<close>
proof (induction As)
  case empty
  then show ?case by auto
next
  case (add x As)
  define n where \<open>n = count As x\<close>
  define As' where \<open>As' \<equiv> removeAll_mset x As\<close>
  have As: \<open>As = As' + replicate_mset n x\<close>
    by (auto simp: As'_def n_def intro!: multiset_eqI)
  have [simp]: \<open>set_mset As' - {x} = set_mset As'\<close> \<open>count As' x = 0\<close> \<open>x \<notin># As'\<close>
    unfolding As'_def
    by auto
  have \<open> (\<Sum>A\<in>set_mset As'.
       (if x = A then Suc (count (As' + replicate_mset n x) A)
        else count (As' + replicate_mset n x) A) *
       f A) =
       (\<Sum>A\<in>set_mset As'.
       (count (As' + replicate_mset n x) A) *
       f A)\<close>
    by (rule sum.cong) auto
  then show ?case using add by (auto simp: As sum.insert_remove)
qed

lemma sum_mset_inter_restrict:
  \<open>(\<Sum> x \<in># filter_mset P M. f x) = (\<Sum> x \<in># M. if P x then f x else 0)\<close>
  by (induction M) auto
lemma mset_set_subset_iff:
  \<open>mset_set A \<subseteq># I \<longleftrightarrow> infinite A \<or> A \<subseteq> set_mset I\<close>
  by (metis finite_set_mset finite_set_mset_mset_set mset_set.infinite mset_set_set_mset_subseteq
    set_mset_mono subset_imp_msubset_mset_set subset_mset.bot.extremum subset_mset.dual_order.trans)

lemma partial_max_sat_is_weight_sat:
  fixes additional_atm :: \<open>'v clause \<Rightarrow> 'v\<close> and
    \<rho> :: \<open>'v clause \<Rightarrow> nat\<close> and
    N\<^sub>S :: \<open>'v clauses\<close>
  defines
    \<open>\<rho>' \<equiv> (\<lambda>C. sum_mset
       ((\<lambda>L. if L \<in> Pos ` additional_atm ` set_mset N\<^sub>S
         then count N\<^sub>S (SOME C. L = Pos (additional_atm C) \<and> C \<in># N\<^sub>S)
	   * \<rho> (SOME C. L = Pos (additional_atm C) \<and> C \<in># N\<^sub>S)
	 else 0) `# C))\<close>
  assumes
    add: \<open>\<And>C. C \<in># N\<^sub>S \<Longrightarrow> additional_atm C \<notin> atms_of_mm (N\<^sub>H + N\<^sub>S)\<close>
      \<open>\<And>C D. C \<in># N\<^sub>S \<Longrightarrow> D \<in># N\<^sub>S \<Longrightarrow> additional_atm C = additional_atm D \<longleftrightarrow> C = D\<close> and
    w: \<open>weight_sat (N\<^sub>H + (\<lambda>C. add_mset (Pos (additional_atm C)) C) `# N\<^sub>S) \<rho>' (Some I)\<close>
  shows
    \<open>partial_max_sat N\<^sub>H N\<^sub>S \<rho> (Some {L \<in> set_mset I. atm_of L \<in> atms_of_mm (N\<^sub>H + N\<^sub>S)})\<close>
proof -
  define N where \<open>N \<equiv> N\<^sub>H + (\<lambda>C. add_mset (Pos (additional_atm C)) C) `# N\<^sub>S\<close>
  define cl_of where \<open>cl_of L = (SOME C. L = Pos (additional_atm C) \<and> C \<in># N\<^sub>S)\<close> for L
  from w
  have
    ent: \<open>set_mset I \<Turnstile>sm N\<close> and
    bi: \<open>bitotal_over_m (set_mset I) N\<close> and
    cons: \<open>consistent_interp (set_mset I)\<close> and
    dist: \<open>distinct_mset I\<close> and
    weight: \<open>\<And>I'. consistent_interp (set_mset I') \<Longrightarrow> bitotal_over_m (set_mset I') N \<Longrightarrow>
      distinct_mset I' \<Longrightarrow> set_mset I' \<Turnstile>sm N \<Longrightarrow> \<rho>' I' \<ge> \<rho>' I\<close>
    unfolding N_def[symmetric]
    by (auto simp: weight_sat.simps)
  let ?I = \<open>{L. L \<in># I \<and> atm_of L \<in> atms_of_mm (N\<^sub>H + N\<^sub>S)}\<close>
  have ent': \<open>set_mset I \<Turnstile>sm N\<^sub>H\<close>
    using ent unfolding true_clss_restrict
    by (auto simp: N_def)
  then have ent': \<open>?I \<Turnstile>sm N\<^sub>H\<close>
    apply (subst (asm) true_clss_restrict[symmetric])
    apply (rule true_clss_mono_left, assumption)
    apply auto
    done
  have [simp]: \<open>atms_of_ms ((\<lambda>C. add_mset (Pos (additional_atm C)) C) ` set_mset N\<^sub>S) =
    additional_atm ` set_mset N\<^sub>S \<union> atms_of_ms (set_mset N\<^sub>S)\<close>
    by (auto simp: atms_of_ms_def)
  have bi': \<open>bitotal_over_m ?I (N\<^sub>H + N\<^sub>S)\<close>
    using bi
    by (auto simp: bitotal_over_m_def total_over_m_def total_over_set_def
      atms_of_s_def N_def)
  have cons': \<open>consistent_interp ?I\<close>
    using cons by (auto simp: consistent_interp_def)
  have [simp]: \<open>cl_of (Pos (additional_atm xb)) = xb\<close>
    if \<open>xb \<in># N\<^sub>S\<close> for xb
    using someI[of \<open>\<lambda>C. additional_atm xb = additional_atm C\<close> xb] add that
    unfolding cl_of_def
    by auto

  let ?I = \<open>{L. L \<in># I \<and> atm_of L \<in> atms_of_mm (N\<^sub>H + N\<^sub>S)} \<union> Pos ` additional_atm ` {C \<in> set_mset N\<^sub>S. \<not>set_mset I \<Turnstile> C}
    \<union> Neg ` additional_atm ` {C \<in> set_mset N\<^sub>S. set_mset I \<Turnstile> C}\<close>
  have \<open>consistent_interp ?I\<close>
    using cons add by (auto simp: consistent_interp_def
      bitotal_over_m_def uminus_lit_swap
      dest: add)
  moreover have \<open>bitotal_over_m ?I N\<close>
    using bi
    by (auto simp: N_def bitotal_over_m_def total_over_m_def
      total_over_set_def image_image)
  moreover have \<open>?I \<Turnstile>sm N\<close>
    using ent apply (auto simp: N_def true_clss_def image_image
      dest!: multi_member_split)
      apply (smt atm_of_lit_in_atms_of mem_Collect_eq true_cls_def true_cls_union_increase true_lit_def)
      apply (smt atm_of_lit_in_atms_of mem_Collect_eq true_cls_def true_cls_union_increase true_lit_def)
      apply (smt atm_of_lit_in_atms_of image_iff insert_iff mem_Collect_eq true_cls_def true_cls_union_increase true_lit_def)
      apply (smt atm_of_lit_in_atms_of image_iff insert_iff mem_Collect_eq true_cls_def true_cls_union_increase true_lit_def) 
      done
  moreover have \<open>set_mset (mset_set ?I) = ?I\<close> and fin: \<open>finite ?I\<close>
    by (auto simp: bitotal_over_m_finite)
  moreover have \<open>distinct_mset (mset_set ?I)\<close>
    by (auto simp: distinct_mset_mset_set)
  ultimately have \<open>\<rho>' (mset_set ?I) \<ge> \<rho>' I\<close>
    using weight[of \<open>mset_set ?I\<close>]
    by argo
  moreover have \<open>\<rho>' (mset_set ?I) \<le> \<rho>' I\<close>
    using ent
    by (auto simp: \<rho>'_def sum_mset_inter_restrict[symmetric] mset_set_subset_iff N_def
      intro!: sum_image_mset_mono
      dest!: multi_member_split)
  ultimately have I_I: \<open>\<rho>' (mset_set ?I) = \<rho>' I\<close>
    by linarith

  have min: \<open>weight_on_clauses N\<^sub>S \<rho> I'
      \<le> weight_on_clauses N\<^sub>S \<rho> {L. L \<in># I \<and> atm_of L \<in> atms_of_mm (N\<^sub>H + N\<^sub>S)}\<close>
    if 
      cons: \<open>consistent_interp I'\<close> and
      bit: \<open>bitotal_over_m I' (N\<^sub>H + N\<^sub>S)\<close> and
      I': \<open>I' \<Turnstile>sm N\<^sub>H\<close>
    for I'
  proof -
    let ?I' = \<open>I' \<union> Pos ` additional_atm ` {C \<in> set_mset N\<^sub>S. \<not>I' \<Turnstile> C}
      \<union> Neg ` additional_atm ` {C \<in> set_mset N\<^sub>S. I' \<Turnstile> C}\<close>
    have \<open>consistent_interp ?I'\<close>
      using cons bit add by (auto simp: consistent_interp_def
        bitotal_over_m_def uminus_lit_swap
	dest: add)
    moreover have \<open>bitotal_over_m ?I' N\<close>
      using bit
      by (auto simp: N_def bitotal_over_m_def total_over_m_def
        total_over_set_def image_image)
    moreover have \<open>?I' \<Turnstile>sm N\<close>
      using I' by (auto simp: N_def true_clss_def image_image
        dest!: multi_member_split)
    moreover have \<open>set_mset (mset_set ?I') = ?I'\<close> and fin: \<open>finite ?I'\<close>
      using bit by (auto simp: bitotal_over_m_finite)
    moreover have \<open>distinct_mset (mset_set ?I')\<close>
      by (auto simp: distinct_mset_mset_set)
    ultimately have I'_I: \<open>\<rho>' (mset_set ?I') \<ge> \<rho>' I\<close>
      using weight[of \<open>mset_set ?I'\<close>]
      by argo
    have inj: \<open>inj_on cl_of (I' \<inter> (\<lambda>x. Pos (additional_atm x)) ` set_mset N\<^sub>S)\<close> for I'
      using add by (auto simp: inj_on_def)

    have we: \<open>weight_on_clauses N\<^sub>S \<rho> I' = sum_mset (\<rho> `# N\<^sub>S) -
      sum_mset (\<rho> `# filter_mset (Not \<circ> (\<Turnstile>) I') N\<^sub>S)\<close> for I'
      unfolding weight_on_clauses_def
      apply (subst (3) multiset_partition[of _ \<open>(\<Turnstile>) I'\<close>])
      unfolding image_mset_union sum_mset.union
      by (auto simp: comp_def)
    have H: \<open>sum_mset
       (\<rho> `#
        filter_mset (Not \<circ> (\<Turnstile>) {L. L \<in># I \<and> atm_of L \<in> atms_of_mm (N\<^sub>H + N\<^sub>S)})
         N\<^sub>S) = \<rho>' I\<close>
	unfolding I_I[symmetric] unfolding \<rho>'_def cl_of_def[symmetric]
	  sum_mset_sum_count if_distrib
	apply (auto simp: sum_mset_sum_count image_image simp flip: sum.inter_restrict
	  cong: if_cong)
	apply (subst comm_monoid_add_class.sum.reindex_cong[symmetric, of cl_of, OF _ refl])
	apply ((use inj in auto; fail)+)[2]
	apply (rule sum.cong)
	apply auto[]
	using inj[of \<open>set_mset I\<close>] \<open>set_mset I \<Turnstile>sm N\<close> assms(2)
	apply (auto dest!: multi_member_split simp: N_def image_Int
	  atm_of_lit_in_atms_of true_cls_def)[]
	  using add apply (auto simp: true_cls_def)
	  done
    have \<open>(\<Sum>x\<in>(I' \<union> (\<lambda>x. Pos (additional_atm x)) ` {C. C \<in># N\<^sub>S \<and> \<not> I' \<Turnstile> C} \<union>
         (\<lambda>x. Neg (additional_atm x)) ` {C. C \<in># N\<^sub>S \<and> I' \<Turnstile> C}) \<inter>
        (\<lambda>x. Pos (additional_atm x)) ` set_mset N\<^sub>S.
       count N\<^sub>S (cl_of x) * \<rho> (cl_of x))
    \<le> (\<Sum>A\<in>{a. a \<in># N\<^sub>S \<and> \<not> I' \<Turnstile> a}. count N\<^sub>S A * \<rho> A)\<close>
	apply (subst comm_monoid_add_class.sum.reindex_cong[symmetric, of cl_of, OF _ refl])
	apply ((use inj in auto; fail)+)[2]
	apply (rule ordered_comm_monoid_add_class.sum_mono2)
	using that add by (auto dest:  simp: N_def
	  bitotal_over_m_def)
    then have \<open>sum_mset (\<rho> `# filter_mset (Not \<circ> (\<Turnstile>) I') N\<^sub>S) \<ge> \<rho>' (mset_set ?I')\<close>
      using fin unfolding cl_of_def[symmetric] \<rho>'_def
      by (auto simp: \<rho>'_def
        simp add: sum_mset_sum_count image_image simp flip: sum.inter_restrict)
    then have \<open>\<rho>' I \<le> sum_mset (\<rho> `# filter_mset (Not \<circ> (\<Turnstile>) I') N\<^sub>S)\<close>
      using I'_I by auto
    then show ?thesis
      unfolding we H I_I apply -
      by auto
  qed

  show ?thesis
    apply (rule partial_max_sat.intros)
    subgoal using ent' by auto
    subgoal using bi' by fast
    subgoal using cons' by fast
    subgoal for I'
      by (rule min)
    done
qed

lemma bitotal_over_m_alt_def:
  \<open>bitotal_over_m (set_mset y) N \<longleftrightarrow> atms_of y \<subseteq> atms_of_mm N \<and>
        total_over_m (set_mset y) (set_mset N)\<close>
  by (auto simp: bitotal_over_m_def atms_of_s_def atms_of_def
    atms_of_ms_def dest!: multi_member_split)

lemma bitotal_over_m_alt_def2:
  \<open>bitotal_over_m (set_mset y) N \<longleftrightarrow> 
	atms_of y = atms_of_mm N\<close>
  by (metis atms_of_def atms_of_s_def bitotal_over_m_alt_def equalityI order_refl total_over_m_def
    total_over_set_alt_def)

lemma (in optimal_encoding) full_cdcl_bab_stgy_weight_sat:
  \<open>full cdcl_bab_stgy (init_state N) T \<Longrightarrow> distinct_mset_mset N \<Longrightarrow> weight_sat N \<rho> (weight T)\<close>
  using full_cdcl_bab_stgy_no_conflicting_clause_from_init_state[of N T]
  apply (cases \<open>weight T = None\<close>)
  subgoal
    by (auto intro!: weight_sat.intros(2))
  subgoal premises p
    using p(1-4,6)
    apply (clarsimp simp only:)
    apply (rule weight_sat.intros(1))
    subgoal by auto
    subgoal by (auto simp: bitotal_over_m_alt_def)[]
    subgoal by auto
    subgoal by auto
    subgoal for J I'
      using p(5)[of I']
      by (auto simp: bitotal_over_m_alt_def2)
    done
  done

end
