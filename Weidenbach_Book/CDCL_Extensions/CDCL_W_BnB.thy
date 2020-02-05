theory CDCL_W_BnB
  imports CDCL.CDCL_W_Abstract_State Weidenbach_Book_Base.Explorer
begin

section \<open>CDCL Extensions\<close>

text \<open>
  A counter-example for the original version from the book has been found (see below). There is no
  simple fix, except taking complete models.

  Based on Dominik Zimmer's thesis, we later reduced the problem of finding partial models to
  finding total models. We later switched to the more elegant dual rail encoding (thanks to the
  reviewer).
\<close>

subsection \<open>Optimisations\<close>

notation image_mset (infixr "`#" 90)

text \<open>The initial version was supposed to work on partial models directly. I found a counterexample
while writing the proof:

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
\<^term>\<open>cdcl_bnb\<close> (for branch-and-bounds). It is parametrised by how the conflicting clauses are
generated and the improvement criterion.

We later instantiate it with the optimisation calculus from Weidenbach's book.
\<close>


subsubsection \<open>Helper libraries\<close>

definition model_on :: \<open>'v partial_interp \<Rightarrow> 'v clauses \<Rightarrow> bool\<close> where
\<open>model_on I N \<longleftrightarrow> consistent_interp I \<and> atm_of ` I \<subseteq> atms_of_mm N\<close>


subsubsection \<open>CDCL BNB\<close>

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
    is_improving_int :: "('v, 'v clause) ann_lits \<Rightarrow> ('v, 'v clause) ann_lits \<Rightarrow> 'v clauses \<Rightarrow> 'a \<Rightarrow> bool" and
    conflicting_clauses :: "'v clauses \<Rightarrow> 'a \<Rightarrow> 'v clauses" and
    weight :: \<open>'st \<Rightarrow> 'a\<close>
begin

abbreviation is_improving where
  \<open>is_improving M M' S \<equiv> is_improving_int M M' (init_clss S) (weight S)\<close>

definition additional_info' :: "'st \<Rightarrow> 'b" where
"additional_info' S = (\<lambda>(_, _, _, _, _, D). D) (state S)"

definition conflicting_clss :: \<open>'st \<Rightarrow> 'v literal multiset multiset\<close> where
\<open>conflicting_clss S = conflicting_clauses (init_clss S) (weight S)\<close>

text \<open>While it would more be natural to add an sublocale with the extended version clause set,
  this actually causes a loop in the hierarchy structure (although with different parameters).
  Therefore, adding theorems (e.g. defining an inductive predicate) causes a loop.
\<close>
definition abs_state
  :: "'st \<Rightarrow> ('v, 'v clause) ann_lit list \<times> 'v clauses \<times> 'v clauses \<times> 'v clause option"
where
  \<open>abs_state S = (trail S, init_clss S + conflicting_clss S, learned_clss S,
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
    is_improving_int :: "('v, 'v clause) ann_lits \<Rightarrow> ('v, 'v clause) ann_lits \<Rightarrow> 'v clauses \<Rightarrow>
      'a \<Rightarrow> bool" and
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
      \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S) \<Longrightarrow> is_improving M M' S \<Longrightarrow>
        conflicting_clss S \<subseteq># conflicting_clss (update_weight_information M' S)\<close>
    and
    conflicting_clss_update_weight_information_in:
      \<open>is_improving M M' S \<Longrightarrow> 
        negate_ann_lits M' \<in># conflicting_clss (update_weight_information M' S)\<close>
begin

paragraph \<open>Conversion to CDCL\<close>
sublocale conflict_driven_clause_learning\<^sub>W where
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
  init_state = init_state
  apply unfold_locales
  unfolding additional_info'_def additional_info_def by (auto simp: state_prop')

paragraph \<open>Overall simplification on states\<close>
declare reduce_trail_to_skip_beginning[simp]

lemma state_eq_weight[state_simp, simp]: \<open>S \<sim> T \<Longrightarrow> weight S = weight T\<close>
  apply (drule state_eq_state)
  apply (subst (asm) state_prop')+
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

lemma conflicting_clss_reduce_trail_to[simp]:
  \<open>conflicting_clss (reduce_trail_to M S) = conflicting_clss S\<close>
  unfolding conflicting_clss_def by auto

lemma trail_trail [simp]:
  \<open>CDCL_W_Abstract_State.trail (abs_state S) = trail S\<close>
  by (auto simp: abs_state_def cdcl\<^sub>W_restart_mset_state)

lemma [simp]:
  \<open>CDCL_W_Abstract_State.trail (cdcl\<^sub>W_restart_mset.reduce_trail_to M (abs_state S)) =
     trail (reduce_trail_to M S)\<close>
  by (auto simp: trail_reduce_trail_to_drop
    cdcl\<^sub>W_restart_mset.trail_reduce_trail_to_drop)

lemma abs_state_cons_trail[simp]:
    \<open>abs_state (cons_trail K S) = CDCL_W_Abstract_State.cons_trail K (abs_state S)\<close> and
  abs_state_reduce_trail_to[simp]:
    \<open>abs_state (reduce_trail_to M S) = cdcl\<^sub>W_restart_mset.reduce_trail_to M (abs_state S)\<close>
  subgoal by (auto simp: abs_state_def cons_trail.simps)
  subgoal by (induction rule: reduce_trail_to_induct)
       (auto simp: reduce_trail_to.simps cdcl\<^sub>W_restart_mset.reduce_trail_to.simps)
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


paragraph \<open>CDCL with branch-and-bound\<close>

inductive conflict_opt :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S T :: 'st where
conflict_opt_rule:
  \<open>conflict_opt S T\<close>
  if
    \<open>negate_ann_lits (trail S) \<in># conflicting_clss S\<close>
    \<open>conflicting S = None\<close>
    \<open>T \<sim> update_conflicting (Some (negate_ann_lits (trail S))) S\<close>

inductive_cases conflict_optE: \<open>conflict_opt S T\<close>

inductive improvep :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
improve_rule:
  \<open>improvep S T\<close>
  if
    \<open>is_improving (trail S) M' S\<close> and
    \<open>conflicting S = None\<close> and
    \<open>T \<sim> update_weight_information M' S\<close>

inductive_cases improveE: \<open>improvep S T\<close>

lemma invs_update_weight_information[simp]:
  \<open>no_strange_atm (update_weight_information C S) = (no_strange_atm S)\<close>
  \<open>cdcl\<^sub>W_M_level_inv (update_weight_information C S) = cdcl\<^sub>W_M_level_inv S\<close>
  \<open>distinct_cdcl\<^sub>W_state (update_weight_information C S) = distinct_cdcl\<^sub>W_state S\<close>
  \<open>cdcl\<^sub>W_conflicting (update_weight_information C S) = cdcl\<^sub>W_conflicting S\<close>
  \<open>cdcl\<^sub>W_learned_clause (update_weight_information C S) = cdcl\<^sub>W_learned_clause S\<close>
  unfolding no_strange_atm_def cdcl\<^sub>W_M_level_inv_def distinct_cdcl\<^sub>W_state_def cdcl\<^sub>W_conflicting_def
    cdcl\<^sub>W_learned_clause_alt_def cdcl\<^sub>W_all_struct_inv_def by auto

lemma conflict_opt_cdcl\<^sub>W_all_struct_inv:
  assumes \<open>conflict_opt S T\<close> and
    inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state T)\<close>
  using assms atms_of_conflicting_clss[of T] atms_of_conflicting_clss[of S]
  by (induction rule: conflict_opt.cases)
    (auto simp add: cdcl\<^sub>W_restart_mset.no_strange_atm_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
        cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_alt_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
        true_annots_true_cls_def_iff_negation_in_model
        in_negate_trial_iff cdcl\<^sub>W_restart_mset_state cdcl\<^sub>W_restart_mset.clauses_def
        distinct_mset_mset_conflicting_clss abs_state_def
      intro!: true_clss_cls_in)

lemma improve_cdcl\<^sub>W_all_struct_inv:
  assumes \<open>improvep S T\<close> and
    inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state T)\<close>
  using assms atms_of_conflicting_clss[of T] atms_of_conflicting_clss[of S]
proof (induction rule: improvep.cases)
  case (improve_rule M' T)
  moreover have \<open>all_decomposition_implies
     (set_mset (init_clss S) \<union> set_mset (conflicting_clss S) \<union> set_mset (learned_clss S))
     (get_all_ann_decomposition (trail S)) \<Longrightarrow>
    all_decomposition_implies
     (set_mset (init_clss S) \<union> set_mset (conflicting_clss (update_weight_information M' S)) \<union>
      set_mset (learned_clss S))
     (get_all_ann_decomposition (trail S))\<close>
      apply (rule all_decomposition_implies_mono)
      using improve_rule conflicting_clss_update_weight_information_mono[of S \<open>trail S\<close> M'] inv
      by (auto dest: multi_member_split)
   ultimately show ?case
      using conflicting_clss_update_weight_information_mono[of S \<open>trail S\<close> M']
      by (auto 6 2 simp add: cdcl\<^sub>W_restart_mset.no_strange_atm_def
            cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
            cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
            cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_alt_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
            true_annots_true_cls_def_iff_negation_in_model
            in_negate_trial_iff cdcl\<^sub>W_restart_mset_state cdcl\<^sub>W_restart_mset.clauses_def
            image_Un distinct_mset_mset_conflicting_clss abs_state_def
          simp del: append_assoc
          dest: no_dup_appendD consistent_interp_unionD)
qed

text \<open>\<^term>\<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant\<close> is too restrictive:
  \<^term>\<open>cdcl\<^sub>W_restart_mset.no_smaller_confl\<close> is needed but does not hold(at least, if cannot
  ensure that conflicts are found as soon as possible).\<close>
lemma improve_no_smaller_conflict:
  assumes \<open>improvep S T\<close> and
    \<open>no_smaller_confl S\<close>
  shows \<open>no_smaller_confl T\<close> and \<open>conflict_is_false_with_level T\<close>
  using assms apply (induction rule: improvep.induct)
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

inductive cdcl_bnb_bj :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
skip: "skip S S' \<Longrightarrow> cdcl_bnb_bj S S'" |
resolve: "resolve S S' \<Longrightarrow> cdcl_bnb_bj S S'" |
backtrack: "obacktrack S S' \<Longrightarrow> cdcl_bnb_bj S S'"

inductive_cases cdcl_bnb_bjE: "cdcl_bnb_bj S T"

inductive ocdcl\<^sub>W_o :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
decide: "decide S S' \<Longrightarrow> ocdcl\<^sub>W_o S S'" |
bj: "cdcl_bnb_bj S S' \<Longrightarrow> ocdcl\<^sub>W_o S S'"

inductive cdcl_bnb :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> for S :: 'st where
cdcl_conflict: "conflict S S' \<Longrightarrow> cdcl_bnb S S'" |
cdcl_propagate: "propagate S S' \<Longrightarrow> cdcl_bnb S S'" |
cdcl_improve: "improvep S S' \<Longrightarrow> cdcl_bnb S S'" |
cdcl_conflict_opt: "conflict_opt S S' \<Longrightarrow> cdcl_bnb S S'" |
cdcl_other': "ocdcl\<^sub>W_o S S' \<Longrightarrow> cdcl_bnb S S'"

inductive cdcl_bnb_stgy :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> for S :: 'st where
cdcl_bnb_conflict: "conflict S S' \<Longrightarrow> cdcl_bnb_stgy S S'" |
cdcl_bnb_propagate: "propagate S S' \<Longrightarrow> cdcl_bnb_stgy S S'" |
cdcl_bnb_improve: "improvep S S' \<Longrightarrow> cdcl_bnb_stgy S S'" |
cdcl_bnb_conflict_opt: "conflict_opt S S' \<Longrightarrow> cdcl_bnb_stgy S S'" |
cdcl_bnb_other': "ocdcl\<^sub>W_o S S' \<Longrightarrow> no_confl_prop_impr S \<Longrightarrow> cdcl_bnb_stgy S S'"

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
  subgoal apply (elim cdcl_bnb_bjE skipE resolveE obacktrackE)
    apply (frule skipH; simp; fail)
    apply (cases "trail S"; auto elim!: resolveE intro!: resolveH; fail)
    apply (frule backtrackH; simp; fail)
    done
  done

lemma obacktrack_backtrackg: \<open>obacktrack S T \<Longrightarrow> backtrackg S T\<close>
  unfolding obacktrack.simps backtrackg.simps
  by blast


subsubsection \<open>Pluging into normal CDCL\<close>

lemma cdcl_bnb_no_more_init_clss:
  \<open>cdcl_bnb S S' \<Longrightarrow> init_clss S = init_clss S'\<close>
  by (induction rule: cdcl_bnb.cases)
    (auto simp: improvep.simps conflict.simps propagate.simps
      conflict_opt.simps ocdcl\<^sub>W_o.simps obacktrack.simps skip.simps resolve.simps cdcl_bnb_bj.simps
      decide.simps)

lemma rtranclp_cdcl_bnb_no_more_init_clss:
  \<open>cdcl_bnb\<^sup>*\<^sup>* S S' \<Longrightarrow> init_clss S = init_clss S'\<close>
  by (induction rule: rtranclp_induct)
    (auto dest: cdcl_bnb_no_more_init_clss)

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
  using assms by (induct T rule: ocdcl\<^sub>W_o.induct) (auto simp: cdcl_bnb_bj.simps)

lemma cdcl\<^sub>W_o_cdcl\<^sub>W_o:
  \<open>ocdcl\<^sub>W_o S S' \<Longrightarrow> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o (abs_state S) (abs_state S')\<close>
  apply (induction rule: ocdcl\<^sub>W_o_all_rules_induct)
     apply (simp add: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o.simps decide_decide; fail)
    apply (blast dest: backtrack_backtrack)
   apply (blast dest: skip_skip)
  by (blast dest: resolve_resolve)

lemma cdcl_bnb_stgy_all_struct_inv:
  assumes \<open>cdcl_bnb S T\<close> and \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state T)\<close>
  using assms
proof (induction rule: cdcl_bnb.cases)
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

lemma rtranclp_cdcl_bnb_stgy_all_struct_inv:
  assumes \<open>cdcl_bnb\<^sup>*\<^sup>* S T\<close> and \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state T)\<close>
  using assms by induction (auto dest: cdcl_bnb_stgy_all_struct_inv)

definition cdcl_bnb_struct_invs :: \<open>'st \<Rightarrow> bool\<close> where
\<open>cdcl_bnb_struct_invs S \<longleftrightarrow>
   atms_of_mm (conflicting_clss S) \<subseteq> atms_of_mm (init_clss S)\<close>

lemma cdcl_bnb_cdcl_bnb_struct_invs:
  \<open>cdcl_bnb S T \<Longrightarrow> cdcl_bnb_struct_invs S \<Longrightarrow> cdcl_bnb_struct_invs T\<close>
  using atms_of_conflicting_clss[of \<open>update_weight_information _ S\<close>] apply -
  by (induction rule: cdcl_bnb.induct)
    (force simp: improvep.simps conflict.simps propagate.simps
      conflict_opt.simps ocdcl\<^sub>W_o.simps obacktrack.simps skip.simps resolve.simps
      cdcl_bnb_bj.simps decide.simps cdcl_bnb_struct_invs_def)+

lemma rtranclp_cdcl_bnb_cdcl_bnb_struct_invs:
  \<open>cdcl_bnb\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl_bnb_struct_invs S \<Longrightarrow> cdcl_bnb_struct_invs T\<close>
  by (induction rule: rtranclp_induct) (auto dest: cdcl_bnb_cdcl_bnb_struct_invs)

lemma cdcl_bnb_stgy_cdcl_bnb: \<open>cdcl_bnb_stgy S T \<Longrightarrow> cdcl_bnb S T\<close>
  by (auto simp: cdcl_bnb_stgy.simps intro: cdcl_bnb.intros)

lemma rtranclp_cdcl_bnb_stgy_cdcl_bnb: \<open>cdcl_bnb_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl_bnb\<^sup>*\<^sup>* S T\<close>
  by (induction rule: rtranclp_induct)
   (auto dest: cdcl_bnb_stgy_cdcl_bnb)

text \<open>The following does \<^emph>\<open>not\<close> hold, because we cannot guarantee the absence of conflict of
  smaller level after \<^term>\<open>improve\<close> and \<^term>\<open>conflict_opt\<close>.\<close>
lemma cdcl_bnb_all_stgy_inv:
  assumes \<open>cdcl_bnb S T\<close> and \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> and
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
  assumes \<open>improvep S T\<close> and \<open>conflict_is_false_with_level S\<close>
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
          then have \<open>cdcl_bnb S ?S'\<close>
            by (auto dest!: cdcl_bnb_bj.intros ocdcl\<^sub>W_o.intros intro: cdcl_bnb.intros)
          then have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state ?S')\<close>
            using cdcl_bnb_stgy_all_struct_inv[of S, OF _ lev] by fast
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

lemma cdcl_bnb_stgy_no_smaller_confl:
  assumes \<open>cdcl_bnb_stgy S T\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> and
    \<open>no_smaller_confl S\<close> and
    \<open>conflict_is_false_with_level S\<close>
  shows \<open>no_smaller_confl T\<close>
  using assms
proof (induction rule: cdcl_bnb_stgy.cases)
  case (cdcl_bnb_other' S')
  show ?case
    by (rule ocdcl\<^sub>W_o_no_smaller_confl_inv)
     (use cdcl_bnb_other' in \<open>auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def\<close>)
qed (auto intro: conflict_no_smaller_confl_inv propagate_no_smaller_confl_inv;
  auto simp: no_smaller_confl_def improvep.simps conflict_opt.simps)+

lemma ocdcl\<^sub>W_o_conflict_is_false_with_level_inv:
  assumes
    \<open>ocdcl\<^sub>W_o S S'\<close> and
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
    using cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o_conflict_is_false_with_level_inv[of \<open>abs_state S\<close> \<open>abs_state T\<close>]
    lev confl_inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by (auto dest!: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o.intros
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_bj.intros)
  then show \<open>?case\<close>
    by (auto simp: cdcl\<^sub>W_restart_mset.conflict_is_false_with_level_def
      conflict_is_false_with_level_def abs_state_def cdcl\<^sub>W_restart_mset_state)
next
  case (skip L C' M D T) note tr_S = this(1) and D = this(2) and T = this(5)
  have \<open>cdcl\<^sub>W_restart_mset.skip (abs_state S) (abs_state T)\<close>
     using skip.intros[of S L C' M D T] skip by (simp add: skip_skip)
  moreover have \<open>cdcl\<^sub>W_restart_mset.conflict_is_false_with_level (abs_state S)\<close>
    using confl_inv
    by (auto simp: cdcl\<^sub>W_restart_mset.conflict_is_false_with_level_def
      conflict_is_false_with_level_def abs_state_def cdcl\<^sub>W_restart_mset_state)
  ultimately have \<open>cdcl\<^sub>W_restart_mset.conflict_is_false_with_level (abs_state T)\<close>
    using  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o_conflict_is_false_with_level_inv[of \<open>abs_state S\<close> \<open>abs_state T\<close>]
    lev confl_inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by (auto dest!: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o.intros cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_bj.intros)
  then show \<open>?case\<close>
    by (auto simp: cdcl\<^sub>W_restart_mset.conflict_is_false_with_level_def
      conflict_is_false_with_level_def abs_state_def cdcl\<^sub>W_restart_mset_state)
next
  case backtrack
  then show ?case
    by (auto split: if_split_asm simp: cdcl\<^sub>W_M_level_inv_decomp lev conflict_is_false_with_level_def)
qed (auto simp: conflict_is_false_with_level_def)


lemma cdcl_bnb_stgy_conflict_is_false_with_level:
  assumes \<open>cdcl_bnb_stgy S T\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> and
    \<open>no_smaller_confl S\<close> and
    \<open>conflict_is_false_with_level S\<close>
  shows \<open>conflict_is_false_with_level T\<close>
  using assms
proof (induction rule: cdcl_bnb_stgy.cases)
  case (cdcl_bnb_conflict S')
  then show ?case
    using conflict_conflict_is_false_with_level
    by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
next
  case (cdcl_bnb_propagate S')
  then show ?case
    using propagate_conflict_is_false_with_level
    by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
next
  case (cdcl_bnb_improve S')
  then show ?case
    using improve_conflict_is_false_with_level by blast
next
  case (cdcl_bnb_conflict_opt S')
  then show ?case
    using conflict_opt_no_smaller_conflict(2) by blast
next
  case (cdcl_bnb_other' S')
  show ?case
    apply (rule ocdcl\<^sub>W_o_conflict_is_false_with_level_inv)
    using cdcl_bnb_other' by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
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
    imp: \<open>is_improving (trail S) M' S\<close>
  shows \<open>Ex (improvep S)\<close>
  using assms
  by (auto simp: improvep.simps intro!: exI)

definition cdcl_bnb_stgy_inv :: "'st \<Rightarrow> bool" where
  \<open>cdcl_bnb_stgy_inv S \<longleftrightarrow> conflict_is_false_with_level S \<and> no_smaller_confl S\<close>

lemma cdcl_bnb_stgy_invD:
  shows \<open>cdcl_bnb_stgy_inv S \<longleftrightarrow> cdcl\<^sub>W_stgy_invariant S\<close>
  unfolding cdcl\<^sub>W_stgy_invariant_def cdcl_bnb_stgy_inv_def
  by auto

lemma cdcl_bnb_stgy_stgy_inv:
  \<open>cdcl_bnb_stgy S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S) \<Longrightarrow>
    cdcl_bnb_stgy_inv S \<Longrightarrow> cdcl_bnb_stgy_inv T\<close>
  using cdcl\<^sub>W_stgy_cdcl\<^sub>W_stgy_invariant[of S T]
     cdcl_bnb_stgy_conflict_is_false_with_level cdcl_bnb_stgy_no_smaller_confl
  unfolding cdcl_bnb_stgy_inv_def
  by blast

lemma rtranclp_cdcl_bnb_stgy_stgy_inv:
  \<open>cdcl_bnb_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S) \<Longrightarrow>
    cdcl_bnb_stgy_inv S \<Longrightarrow> cdcl_bnb_stgy_inv T\<close>
  apply (induction rule: rtranclp_induct)
  subgoal by auto
  subgoal for T U
    using cdcl_bnb_stgy_stgy_inv rtranclp_cdcl_bnb_stgy_all_struct_inv
      rtranclp_cdcl_bnb_stgy_cdcl_bnb by blast
  done

lemma cdcl_bnb_cdcl\<^sub>W_learned_clauses_entailed_by_init:
  assumes
    \<open>cdcl_bnb S T\<close> and
    entailed: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (abs_state S)\<close> and
    all_struct: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (abs_state T)\<close>
  using assms(1)
proof (induction rule: cdcl_bnb.cases)
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
    set_mset (CDCL_W_Abstract_State.init_clss (abs_state (update_weight_information M' S)))\<close>
       if \<open>is_improving M M' S\<close> for M M'
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
    subgoal using o unfolding T by (blast dest: cdcl\<^sub>W_o_cdcl\<^sub>W_o cdcl\<^sub>W_restart_mset.other)
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

lemma rtranclp_cdcl_bnb_cdcl\<^sub>W_learned_clauses_entailed_by_init:
  assumes
    \<open>cdcl_bnb\<^sup>*\<^sup>* S T\<close> and
    entailed: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (abs_state S)\<close> and
    all_struct: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (abs_state T)\<close>
  using assms by (induction rule: rtranclp_induct)
   (auto intro: cdcl_bnb_cdcl\<^sub>W_learned_clauses_entailed_by_init
      rtranclp_cdcl_bnb_stgy_all_struct_inv)

lemma atms_of_init_clss_conflicting_clss2[simp]:
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

lemma obacktrack_imp_backtrack:
  \<open>obacktrack S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.backtrack (abs_state S) (abs_state T)\<close>
  by (elim obacktrackE, rule_tac D=D and L=L and K=K in cdcl\<^sub>W_restart_mset.backtrack.intros)
    (auto elim!: obacktrackE simp: cdcl\<^sub>W_restart_mset.backtrack.simps sim_abs_state_simp)

lemma backtrack_imp_obacktrack:
  \<open>cdcl\<^sub>W_restart_mset.backtrack (abs_state S) T \<Longrightarrow> Ex (obacktrack S)\<close>
  by (elim cdcl\<^sub>W_restart_mset.backtrackE, rule exI,
       rule_tac D=D and L=L and K=K in obacktrack.intros)
    (auto simp: cdcl\<^sub>W_restart_mset.backtrack.simps obacktrack.simps)

lemma cdcl\<^sub>W_same_weight: \<open>cdcl\<^sub>W S U \<Longrightarrow> weight S = weight U\<close>
  by (induction rule: cdcl\<^sub>W.induct)
    (auto simp: improvep.simps cdcl\<^sub>W.simps
        propagate.simps sim_abs_state_simp abs_state_def cdcl\<^sub>W_restart_mset_state
        clauses_def conflict.simps cdcl\<^sub>W_o.simps decide.simps cdcl\<^sub>W_bj.simps
        skip.simps resolve.simps backtrack.simps)

lemma ocdcl\<^sub>W_o_same_weight: \<open>ocdcl\<^sub>W_o S U \<Longrightarrow> weight S = weight U\<close>
  by (induction rule: ocdcl\<^sub>W_o.induct)
    (auto simp: improvep.simps cdcl\<^sub>W.simps cdcl_bnb_bj.simps
        propagate.simps sim_abs_state_simp abs_state_def cdcl\<^sub>W_restart_mset_state
        clauses_def conflict.simps cdcl\<^sub>W_o.simps decide.simps cdcl\<^sub>W_bj.simps
        skip.simps resolve.simps obacktrack.simps)

text \<open>This is a proof artefact: it is easier to reason on \<^term>\<open>improvep\<close> when the set of
  initial clauses is fixed (here by \<^term>\<open>N\<close>). The next theorem shows that the conclusion
  is equivalent to not fixing the set of clauses.\<close>
lemma wf_cdcl_bnb: (* \htmllink{wf_cdcl_bnb} *)
  assumes improve: \<open>\<And>S T. improvep S T \<Longrightarrow> init_clss S = N \<Longrightarrow> (\<nu> (weight T), \<nu> (weight S)) \<in> R\<close> and
    wf_R: \<open>wf R\<close>
  shows \<open>wf {(T, S). cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S) \<and> cdcl_bnb S T \<and>
      init_clss S = N}\<close>
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
        simp: cdcl\<^sub>W_same_weight cdcl_bnb.simps ocdcl\<^sub>W_o_same_weight
        elim: conflict_optE)
  ultimately show ?thesis
    by (rule wf_subset)
qed

corollary wf_cdcl_bnb_fixed_iff:
  shows \<open>(\<forall>N. wf {(T, S). cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S) \<and> cdcl_bnb S T
       \<and> init_clss S = N}) \<longleftrightarrow>
     wf {(T, S). cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S) \<and> cdcl_bnb S T}\<close>
    (is \<open>(\<forall>N. wf (?A N)) \<longleftrightarrow> wf ?B\<close>)
proof
  assume \<open>wf ?B\<close>
  then show \<open>\<forall>N. wf (?A N)\<close>
    by (intro allI, rule wf_subset) auto
next
  assume \<open>\<forall>N. wf (?A N)\<close>
  show \<open>wf ?B\<close>
    unfolding wf_iff_no_infinite_down_chain
  proof
    assume \<open>\<exists>f. \<forall>i. (f (Suc i), f i) \<in> ?B\<close>
    then obtain f where f: \<open>(f (Suc i), f i) \<in> ?B\<close> for i
      by blast
    then have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state (f n))\<close> for n
      by (induction n) auto
    with f have st: \<open>cdcl_bnb\<^sup>*\<^sup>* (f 0) (f n)\<close> for n
      apply (induction n)
      subgoal by auto
      subgoal by (subst rtranclp_unfold,subst tranclp_unfold_end)
         auto
      done
    let ?N = \<open>init_clss (f 0)\<close>
    have N: \<open>init_clss (f n) = ?N\<close> for n
      using st[of n] by (auto dest: rtranclp_cdcl_bnb_no_more_init_clss)
    have \<open>(f (Suc i), f i) \<in> ?A ?N\<close> for i
      using f N by auto
    with \<open>\<forall>N. wf (?A N)\<close> show False
      unfolding wf_iff_no_infinite_down_chain by blast
  qed
qed

text \<open>The following is a slightly more restricted version of the theorem, because it makes it possible
to add some specific invariant, which can be useful when the proof of the decreasing is complicated.
\<close>
lemma wf_cdcl_bnb_with_additional_inv:
  assumes improve: \<open>\<And>S T. improvep S T \<Longrightarrow> P S \<Longrightarrow> init_clss S = N \<Longrightarrow> (\<nu> (weight T), \<nu> (weight S)) \<in> R\<close> and
    wf_R: \<open>wf R\<close> and
    \<open>\<And>S T. cdcl_bnb S T \<Longrightarrow> P S \<Longrightarrow> init_clss S = N \<Longrightarrow> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S) \<Longrightarrow> P T\<close>
  shows \<open>wf {(T, S). cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S) \<and> cdcl_bnb S T \<and> P S \<and>
      init_clss S = N}\<close>
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
    using assms(3) cdcl_bnb.intros(3)
    by (auto dest: cdcl\<^sub>W.intros cdcl\<^sub>W_restart_mset.W_propagate cdcl\<^sub>W_restart_mset.W_other
          conflict_conflict propagate_propagate decide_decide improve conflict_opt_conflict
          cdcl\<^sub>W_o_cdcl\<^sub>W_o cdcl\<^sub>W_restart_mset.W_conflict W_conflict cdcl\<^sub>W_o.intros cdcl\<^sub>W.intros
          cdcl\<^sub>W_o_cdcl\<^sub>W_o
        simp: cdcl\<^sub>W_same_weight cdcl_bnb.simps ocdcl\<^sub>W_o_same_weight
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
  \<open>cdcl\<^sub>W_restart_mset.decide (abs_state S) T \<Longrightarrow> cdcl_bnb_struct_invs S \<Longrightarrow> Ex(decide S)\<close>
  apply (cases rule: cdcl\<^sub>W_restart_mset.decide.cases, assumption)
  subgoal for L
    apply (rule exI)
    apply (rule decide.intros[of _ L])
    by (auto simp: cdcl_bnb_struct_invs_def abs_state_def cdcl\<^sub>W_restart_mset_state)
  done

lemma cdcl_bnb_no_conflicting_clss_cdcl\<^sub>W:
  assumes \<open>cdcl_bnb S T\<close> and \<open>conflicting_clss T = {#}\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W (abs_state S) (abs_state T) \<and> conflicting_clss S = {#}\<close>
  using assms
  by (auto simp: cdcl_bnb.simps conflict_opt.simps improvep.simps ocdcl\<^sub>W_o.simps
      cdcl_bnb_bj.simps
    dest: conflict_conflict propagate_propagate decide_decide skip_skip resolve_resolve
      backtrack_backtrack
    intro: cdcl\<^sub>W_restart_mset.W_conflict cdcl\<^sub>W_restart_mset.W_propagate cdcl\<^sub>W_restart_mset.W_other
    dest: conflicting_clss_update_weight_information_in
    elim: conflictE propagateE decideE skipE resolveE improveE obacktrackE)

lemma rtranclp_cdcl_bnb_no_conflicting_clss_cdcl\<^sub>W:
  assumes \<open>cdcl_bnb\<^sup>*\<^sup>* S T\<close> and \<open>conflicting_clss T = {#}\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W\<^sup>*\<^sup>* (abs_state S) (abs_state T) \<and> conflicting_clss S = {#}\<close>
  using assms
  by (induction rule: rtranclp_induct)
     (fastforce dest: cdcl_bnb_no_conflicting_clss_cdcl\<^sub>W)+

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

lemma cdcl_bnb_stgy_no_conflicting_clss_cdcl\<^sub>W_stgy:
  assumes \<open>cdcl_bnb_stgy S T\<close> and \<open>conflicting_clss T = {#}\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (abs_state S) (abs_state T)\<close>
proof -
  have \<open>conflicting_clss S = {#}\<close>
    using cdcl_bnb_no_conflicting_clss_cdcl\<^sub>W[of S T] assms
    by (auto dest: cdcl_bnb_stgy_cdcl_bnb)
  then show ?thesis
    using assms
    by (auto 7 5 simp: cdcl_bnb_stgy.simps conflict_opt.simps ocdcl\<^sub>W_o.simps
        cdcl_bnb_bj.simps
      dest: conflict_conflict propagate_propagate decide_decide skip_skip resolve_resolve
        backtrack_backtrack
      dest: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy.intros cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o.intros
      dest: conflicting_clss_update_weight_information_in
        conflict_abs_ex_conflict_no_conflicting
        propagate_abs_ex_propagate_no_conflicting
      intro: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy.intros(3)
      elim: improveE)
qed

lemma rtranclp_cdcl_bnb_stgy_no_conflicting_clss_cdcl\<^sub>W_stgy:
  assumes \<open>cdcl_bnb_stgy\<^sup>*\<^sup>* S T\<close> and \<open>conflicting_clss T = {#}\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (abs_state S) (abs_state T)\<close>
  using assms apply (induction rule: rtranclp_induct)
  subgoal by auto
  subgoal for T U
    using cdcl_bnb_no_conflicting_clss_cdcl\<^sub>W[of T U, OF cdcl_bnb_stgy_cdcl_bnb]
    by (auto dest: cdcl_bnb_stgy_no_conflicting_clss_cdcl\<^sub>W_stgy)
  done


context
  assumes can_always_improve:
     \<open>\<And>S. trail S \<Turnstile>asm clauses S \<Longrightarrow> no_step conflict_opt S \<Longrightarrow>
       conflicting S = None \<Longrightarrow>
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S) \<Longrightarrow>
       total_over_m (lits_of_l (trail S)) (set_mset (clauses S)) \<Longrightarrow> Ex (improvep S)\<close>
begin

text \<open>The following theorems states a non-obvious (and slightly subtle) property: The fact that there
  is no conflicting cannot be shown without additional assumption. However, the assumption that every
  model leads to an improvements implies that we end up with a conflict.\<close>
lemma no_step_cdcl_bnb_cdcl\<^sub>W:
  assumes
    ns: \<open>no_step cdcl_bnb S\<close> and
    struct_invs: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close>
  shows \<open>no_step cdcl\<^sub>W_restart_mset.cdcl\<^sub>W (abs_state S)\<close>
proof -
  have ns_confl: \<open>no_step skip S\<close>  \<open>no_step resolve S\<close>  \<open>no_step obacktrack S\<close> and
    ns_nc: \<open>no_step conflict S\<close> \<open>no_step propagate S\<close> \<open>no_step improvep S\<close> \<open>no_step conflict_opt S\<close>
      \<open>no_step decide S\<close>
    using ns
    by (auto simp: cdcl_bnb.simps ocdcl\<^sub>W_o.simps cdcl_bnb_bj.simps)
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


lemma no_step_cdcl_bnb_stgy:
  assumes
    n_s: \<open>no_step cdcl_bnb S\<close> and
    all_struct: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> and
    stgy_inv: \<open>cdcl_bnb_stgy_inv S\<close>
  shows \<open>conflicting S = None \<or> conflicting S = Some {#}\<close>
proof (rule ccontr)
  assume \<open>\<not> ?thesis\<close>
  then obtain D where \<open>conflicting S = Some D\<close> and \<open>D \<noteq> {#}\<close>
    by auto
  moreover have \<open>no_step cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (abs_state S)\<close>
    using no_step_cdcl_bnb_cdcl\<^sub>W[OF n_s all_struct]
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_cdcl\<^sub>W by blast
  moreover have le: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause (abs_state S)\<close>
    using all_struct unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def by fast
  ultimately show False
    using cdcl\<^sub>W_restart_mset.conflicting_no_false_can_do_step[of \<open>abs_state S\<close>] all_struct stgy_inv le
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl_bnb_stgy_inv_def
    by (force dest: distinct_cdcl\<^sub>W_state_distinct_cdcl\<^sub>W_state
      simp: conflict_is_false_with_level_abs_iff)
qed

lemma no_step_cdcl_bnb_stgy_empty_conflict: (* \htmllink{no_step_cdcl_bnb_stgy_empty_conflict} *)
  assumes
    n_s: \<open>no_step cdcl_bnb S\<close> and
    all_struct: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> and
    stgy_inv: \<open>cdcl_bnb_stgy_inv S\<close>
  shows \<open>conflicting S = Some {#}\<close>
proof (rule ccontr)
  assume H: \<open>\<not> ?thesis\<close>
  have all_struct': \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close>
    by (simp add: all_struct)
  have le: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause (abs_state S)\<close>
    using all_struct
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl_bnb_stgy_inv_def
    by auto
  have \<open>conflicting S = None \<or> conflicting S = Some {#}\<close>
    using no_step_cdcl_bnb_stgy[OF n_s all_struct' stgy_inv] .
  then have confl: \<open>conflicting S = None\<close>
    using H by blast
  have \<open>no_step cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (abs_state S)\<close>
    using no_step_cdcl_bnb_cdcl\<^sub>W[OF n_s all_struct]
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_cdcl\<^sub>W by blast
  then have entail: \<open>trail S \<Turnstile>asm clauses S\<close>
    using confl cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_final_state_conclusive2[of \<open>abs_state S\<close>]
      all_struct stgy_inv le
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl_bnb_stgy_inv_def
    by (auto simp: conflict_is_false_with_level_abs_iff)
  have \<open>total_over_m (lits_of_l (trail S)) (set_mset (clauses S))\<close>
    using cdcl\<^sub>W_restart_mset.no_step_cdcl\<^sub>W_total[OF no_step_cdcl_bnb_cdcl\<^sub>W, of S] all_struct n_s confl
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by auto
  with can_always_improve entail confl all_struct
  show \<open>False\<close>
    using n_s by (auto simp: cdcl_bnb.simps)
qed

lemma full_cdcl_bnb_stgy_no_conflicting_clss_unsat: (* \htmllink{full_cdcl_bnb_stgy_no_conflicting_clss_unsat} *)
  assumes
    full: \<open>full cdcl_bnb_stgy S T\<close> and
    all_struct: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> and
    stgy_inv: \<open>cdcl_bnb_stgy_inv S\<close> and
    ent_init: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (abs_state S)\<close> and
    [simp]: \<open>conflicting_clss T = {#}\<close>
  shows \<open>unsatisfiable (set_mset (init_clss S))\<close>
proof -
  have ns: "no_step cdcl_bnb_stgy T" and
    st: "cdcl_bnb_stgy\<^sup>*\<^sup>* S T" and
    st': "cdcl_bnb\<^sup>*\<^sup>* S T" and
    ns': \<open>no_step cdcl_bnb T\<close>
    using full unfolding full_def apply (blast dest: rtranclp_cdcl_bnb_stgy_cdcl_bnb)+
    using full unfolding full_def
    by (metis cdcl_bnb.simps cdcl_bnb_conflict cdcl_bnb_conflict_opt cdcl_bnb_improve
      cdcl_bnb_other' cdcl_bnb_propagate no_confl_prop_impr.elims(3))
  have struct_T: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state T)\<close>
    using rtranclp_cdcl_bnb_stgy_all_struct_inv[OF st' all_struct] .
  have [simp]: \<open>conflicting_clss S = {#}\<close>
    using rtranclp_cdcl_bnb_no_conflicting_clss_cdcl\<^sub>W[OF st'] by auto
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (abs_state S) (abs_state T)\<close>
    using rtranclp_cdcl_bnb_stgy_no_conflicting_clss_cdcl\<^sub>W_stgy[OF st] by auto
  then have \<open>full cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (abs_state S) (abs_state T)\<close>
    using no_step_cdcl_bnb_cdcl\<^sub>W[OF ns' struct_T] unfolding full_def
    by (auto dest: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_cdcl\<^sub>W)
  moreover have \<open>cdcl\<^sub>W_restart_mset.no_smaller_confl (state_butlast S)\<close>
    using stgy_inv ent_init
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def conflict_is_false_with_level_abs_iff
      cdcl_bnb_stgy_inv_def conflict_is_false_with_level_abs_iff
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant_def
    by (auto simp: abs_state_def cdcl\<^sub>W_restart_mset_state cdcl_bnb_stgy_inv_def
      no_smaller_confl_def cdcl\<^sub>W_restart_mset.no_smaller_confl_def clauses_def
      cdcl\<^sub>W_restart_mset.clauses_def)
  ultimately have "conflicting T = Some {#} \<and> unsatisfiable (set_mset (init_clss S))
    \<or> conflicting T = None \<and> trail T \<Turnstile>asm init_clss S"
    using cdcl\<^sub>W_restart_mset.full_cdcl\<^sub>W_stgy_inv_normal_form[of \<open>abs_state S\<close> \<open>abs_state T\<close>] all_struct
      stgy_inv ent_init
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def conflict_is_false_with_level_abs_iff
      cdcl_bnb_stgy_inv_def conflict_is_false_with_level_abs_iff
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant_def
    by (auto simp: abs_state_def cdcl\<^sub>W_restart_mset_state cdcl_bnb_stgy_inv_def)
  moreover have \<open>cdcl_bnb_stgy_inv T\<close>
    using rtranclp_cdcl_bnb_stgy_stgy_inv[OF st all_struct stgy_inv] .
  ultimately show \<open>?thesis\<close>
    using no_step_cdcl_bnb_stgy_empty_conflict[OF ns' struct_T] by auto

qed


lemma ocdcl\<^sub>W_o_no_smaller_propa:
  assumes \<open>ocdcl\<^sub>W_o S T\<close> and
    inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> and
    smaller_propa: \<open>no_smaller_propa S\<close> and
    n_s: \<open>no_confl_prop_impr S\<close>
  shows \<open>no_smaller_propa T\<close>
  using assms(1)
proof (cases)
  case decide
  show ?thesis
    unfolding no_smaller_propa_def
  proof clarify
    fix M K M' D L
    assume
      tr: \<open>trail T = M' @ Decided K # M\<close> and
      D: \<open>D+{#L#} \<in># clauses T\<close> and
      undef: \<open>undefined_lit M L\<close> and
      M: \<open>M \<Turnstile>as CNot D\<close>
    then have "Ex (propagate S)"
      apply (cases M')
      using propagate_rule[of S "D+{#L#}" L "cons_trail (Propagated L (D + {#L#})) S"]
        smaller_propa decide
      by (auto simp: no_smaller_propa_def elim!: rulesE)
    then show False
      using n_s unfolding no_confl_prop_impr.simps by blast
  qed
next
  case bj
  then show ?thesis
  proof cases
    case skip
    then show ?thesis
      using assms no_smaller_propa_tl[of S T]
      by (auto simp: cdcl_bnb_bj.simps ocdcl\<^sub>W_o.simps obacktrack.simps
          resolve.simps
        elim!: rulesE)
  next
    case resolve
    then show ?thesis
      using assms no_smaller_propa_tl[of S T]
      by (auto simp: cdcl_bnb_bj.simps ocdcl\<^sub>W_o.simps obacktrack.simps
          resolve.simps
        elim!: rulesE)
  next
    case backtrack
    have inv_T: "cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state T)"
      using cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_cdcl\<^sub>W_all_struct_inv inv assms(1)
      using cdcl_bnb_stgy_all_struct_inv cdcl_other' by blast
    obtain D D' :: "'v clause" and K L :: "'v literal" and
      M1 M2 :: "('v, 'v clause) ann_lit list" and i :: nat where
      "conflicting S = Some (add_mset L D)" and
      decomp: "(Decided K # M1, M2) \<in> set (get_all_ann_decomposition (trail S))" and
      "get_level (trail S) L = backtrack_lvl S" and
      "get_level (trail S) L = get_maximum_level (trail S) (add_mset L D')" and
      i: "get_maximum_level (trail S) D' \<equiv> i" and
      lev_K: "get_level (trail S) K = i + 1" and
      D_D': \<open>D' \<subseteq># D\<close> and
      T: "T \<sim> cons_trail (Propagated L (add_mset L D'))
          (reduce_trail_to M1
            (add_learned_cls (add_mset L D')
              (update_conflicting None S)))"
      using backtrack by (auto elim!: obacktrackE)
    let ?D' = \<open>add_mset L D'\<close>
    have [simp]: "trail (reduce_trail_to M1 S) = M1"
      using decomp by auto
    obtain M'' c where M'': "trail S = M'' @ tl (trail T)" and c: \<open>M'' = c @ M2 @ [Decided K]\<close>
      using decomp T by auto
    have M1: "M1 = tl (trail T)" and tr_T: "trail T = Propagated L ?D' # M1"
      using decomp T by auto
    have lev_inv: "cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (abs_state S)"
      using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def by auto
    then have lev_inv_T: "cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (abs_state T)"
      using inv_T unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def by auto
    have n_d: "no_dup (trail S)"
      using lev_inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
      by (auto simp: abs_state_def trail.simps)
    have n_d_T: "no_dup (trail T)"
      using lev_inv_T unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
      by (auto simp: abs_state_def trail.simps)

    have i_lvl: \<open>i = backtrack_lvl T\<close>
      using no_dup_append_in_atm_notin[of \<open>c @ M2\<close> \<open>Decided K # tl (trail T)\<close> K]
      n_d lev_K unfolding c M'' by (auto simp: image_Un tr_T)

    from backtrack show ?thesis
      unfolding no_smaller_propa_def
    proof clarify
      fix M K' M' E' L'
      assume
        tr: \<open>trail T = M' @ Decided K' # M\<close> and
        E: \<open>E'+{#L'#} \<in># clauses T\<close> and
        undef: \<open>undefined_lit M L'\<close> and
        M: \<open>M \<Turnstile>as CNot E'\<close>
      have False if D: \<open>add_mset L D' = add_mset L' E'\<close> and M_D: \<open>M \<Turnstile>as CNot E'\<close>
      proof -
        have \<open>i \<noteq> 0\<close>
          using i_lvl tr T by auto
        moreover {
          have "M1 \<Turnstile>as CNot D'"
            using inv_T tr_T unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
            cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
            by (force simp: abs_state_def trail.simps conflicting.simps)
          then have "get_maximum_level M1 D' = i"
            using T i n_d D_D' unfolding M'' tr_T
            by (subst (asm) get_maximum_level_skip_beginning)
              (auto dest: defined_lit_no_dupD dest!: true_annots_CNot_definedD) }
        ultimately obtain L_max where
          L_max_in: "L_max \<in># D'" and
          lev_L_max: "get_level M1 L_max = i"
          using i get_maximum_level_exists_lit_of_max_level[of D' M1]
          by (cases D') auto
        have count_dec_M: "count_decided M < i"
          using T i_lvl unfolding tr by auto
        have "- L_max \<notin> lits_of_l M"
        proof (rule ccontr)
          assume \<open>\<not> ?thesis\<close>
          then have \<open>undefined_lit (M' @ [Decided K']) L_max\<close>
            using n_d_T unfolding tr
            by (auto dest: in_lits_of_l_defined_litD dest: defined_lit_no_dupD simp: atm_of_eq_atm_of)
          then have "get_level (tl M' @ Decided K' # M) L_max < i"
            apply (subst get_level_skip)
             apply (cases M'; auto simp add: atm_of_eq_atm_of lits_of_def; fail)
            using count_dec_M count_decided_ge_get_level[of M L_max] by auto
          then show False
            using lev_L_max tr unfolding tr_T by (auto simp: propagated_cons_eq_append_decide_cons)
        qed
        moreover have "- L \<notin> lits_of_l M"
        proof (rule ccontr)
          define MM where \<open>MM = tl M'\<close>
          assume \<open>\<not> ?thesis\<close>
          then have \<open>- L \<notin> lits_of_l (M' @ [Decided K'])\<close>
            using n_d_T unfolding tr by (auto simp: lits_of_def no_dup_def)
          have \<open>undefined_lit (M' @ [Decided K']) L\<close>
            apply (rule no_dup_uminus_append_in_atm_notin)
            using n_d_T \<open>\<not> - L \<notin> lits_of_l M\<close> unfolding tr by auto
          moreover have "M' = Propagated L ?D' # MM"
            using tr_T MM_def by (metis hd_Cons_tl propagated_cons_eq_append_decide_cons tr)
          ultimately show False
            by simp
        qed
        moreover have "L_max \<in># D' \<or> L \<in># D'"
          using D L_max_in by (auto split: if_splits)
        ultimately show False
          using M_D D by (auto simp: true_annots_true_cls true_clss_def add_mset_eq_add_mset)
      qed
      then show False
        using M'' smaller_propa tr undef M T E
        by (cases M') (auto simp: no_smaller_propa_def trivial_add_mset_remove_iff elim!: rulesE)
    qed
  qed
qed

lemma ocdcl\<^sub>W_no_smaller_propa:
  assumes \<open>cdcl_bnb_stgy S T\<close> and
    inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> and
    smaller_propa: \<open>no_smaller_propa S\<close> and
    n_s: \<open>no_confl_prop_impr S\<close>
  shows \<open>no_smaller_propa T\<close>
  using assms
  apply (cases)
  subgoal by (auto)
  subgoal by (auto)
  subgoal by (auto elim!: improveE simp: no_smaller_propa_def)
  subgoal by (auto elim!: conflict_optE simp: no_smaller_propa_def)
  subgoal using ocdcl\<^sub>W_o_no_smaller_propa by fast
  done


text \<open>Unfortunately, we cannot reuse the proof we have alrealy done.\<close>
lemma ocdcl\<^sub>W_no_relearning:
  assumes \<open>cdcl_bnb_stgy S T\<close> and
    inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> and
    smaller_propa: \<open>no_smaller_propa S\<close> and
    n_s: \<open>no_confl_prop_impr S\<close> and
    dist: \<open>distinct_mset (clauses S)\<close>
  shows \<open>distinct_mset (clauses T)\<close>
  using assms(1)
proof cases
  case cdcl_bnb_conflict
  then show ?thesis using dist by (auto elim: rulesE)
next
  case cdcl_bnb_propagate
  then show ?thesis using dist by (auto elim: rulesE)
next
  case cdcl_bnb_improve
  then show ?thesis using dist by (auto elim: improveE)
next
  case cdcl_bnb_conflict_opt
  then show ?thesis using dist by (auto elim: conflict_optE)
next
  case cdcl_bnb_other'
  then show ?thesis
  proof cases
    case decide
    then show ?thesis using dist by (auto elim: rulesE)
  next
    case bj
    then show ?thesis
    proof cases
      case skip
      then show ?thesis using dist by (auto elim: rulesE)
    next
      case resolve
      then show ?thesis using dist by (auto elim: rulesE)
    next
      case backtrack
      have smaller_propa: \<open>\<And>M K M' D L.
        trail S = M' @ Decided K # M \<Longrightarrow>
        D + {#L#} \<in># clauses S \<Longrightarrow> undefined_lit M L \<Longrightarrow> \<not> M \<Turnstile>as CNot D\<close>
        using smaller_propa unfolding no_smaller_propa_def by fast
      have inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state T)\<close>
        using inv
        using cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_cdcl\<^sub>W_all_struct_inv inv assms(1)
        using cdcl_bnb_stgy_all_struct_inv cdcl_other' backtrack ocdcl\<^sub>W_o.intros
        cdcl_bnb_bj.intros
        by blast
      then have n_d: \<open>no_dup (trail T)\<close> and
        ent: \<open>\<And>L mark a b.
          a @ Propagated L mark # b = trail T \<Longrightarrow>
           b \<Turnstile>as CNot (remove1_mset L mark) \<and> L \<in># mark\<close>
        unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
           cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
        by (auto simp: abs_state_def trail.simps)
      show ?thesis
      proof (rule ccontr)
        assume H: \<open>\<not>?thesis\<close>
        obtain D D' :: "'v clause" and K L :: "'v literal" and
          M1 M2 :: "('v, 'v clause) ann_lit list" and i :: nat where
          "conflicting S = Some (add_mset L D)" and
          decomp: "(Decided K # M1, M2) \<in> set (get_all_ann_decomposition (trail S))" and
          "get_level (trail S) L = backtrack_lvl S" and
          "get_level (trail S) L = get_maximum_level (trail S) (add_mset L D')" and
          i: "get_maximum_level (trail S) D' \<equiv> i" and
          lev_K: "get_level (trail S) K = i + 1" and
          D_D': \<open>D' \<subseteq># D\<close> and
          T: "T \<sim> cons_trail (Propagated L (add_mset L D'))
              (reduce_trail_to M1
                (add_learned_cls (add_mset L D')
                  (update_conflicting None S)))"
          using backtrack by (auto elim!: obacktrackE)
        from H T dist have LD': \<open>add_mset L D' \<in># clauses S\<close>
          by auto
        have \<open>\<not>M1 \<Turnstile>as CNot D'\<close>
          using get_all_ann_decomposition_exists_prepend[OF decomp] apply (elim exE)
          by (rule smaller_propa[of \<open>_ @ M2\<close> K M1 D' L])
            (use n_d T decomp LD' in auto)
        moreover have \<open>M1 \<Turnstile>as CNot D'\<close>
          using ent[of \<open>[]\<close> L \<open>add_mset L D'\<close> M1] T decomp by auto
        ultimately show False
          ..
      qed
    qed
  qed
qed


lemma full_cdcl_bnb_stgy_unsat:
  assumes
    st: \<open>full cdcl_bnb_stgy S T\<close> and
    all_struct: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state S)\<close> and
    opt_struct: \<open>cdcl_bnb_struct_invs S\<close> and
    stgy_inv: \<open>cdcl_bnb_stgy_inv S\<close>
  shows
    \<open>unsatisfiable (set_mset (clauses T + conflicting_clss T))\<close>
proof -
  have ns: \<open>no_step cdcl_bnb_stgy T\<close> and
    st: \<open>cdcl_bnb_stgy\<^sup>*\<^sup>* S T\<close> and
    st': \<open>cdcl_bnb\<^sup>*\<^sup>* S T\<close>
    using st unfolding full_def by (auto intro: rtranclp_cdcl_bnb_stgy_cdcl_bnb)
  have ns': \<open>no_step cdcl_bnb T\<close>
    by (meson cdcl_bnb.cases cdcl_bnb_stgy.simps no_confl_prop_impr.elims(3) ns)
  have struct_T: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (abs_state T)\<close>
    using rtranclp_cdcl_bnb_stgy_all_struct_inv[OF st' all_struct] .
  have stgy_T: \<open>cdcl_bnb_stgy_inv T\<close>
    using rtranclp_cdcl_bnb_stgy_stgy_inv[OF st all_struct stgy_inv] .
  have confl: \<open>conflicting T = Some {#}\<close>
    using no_step_cdcl_bnb_stgy_empty_conflict[OF ns' struct_T stgy_T] .

  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause (abs_state T)\<close> and
    alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (abs_state T)\<close>
    using struct_T unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def by fast+
  then have ent': \<open>set_mset (clauses T + conflicting_clss T) \<Turnstile>p {#}\<close>
    using confl unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_alt_def
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
      using ent' unfolding true_clss_cls_def by auto
  qed
qed

end

lemma cdcl_bnb_reasons_in_clauses:
  \<open>cdcl_bnb S T \<Longrightarrow> reasons_in_clauses S \<Longrightarrow> reasons_in_clauses T\<close>
  by (auto simp: cdcl_bnb.simps reasons_in_clauses_def ocdcl\<^sub>W_o.simps
        cdcl_bnb_bj.simps get_all_mark_of_propagated_tl_proped
    elim!: rulesE improveE conflict_optE obacktrackE
    dest!: in_set_tlD get_all_ann_decomposition_exists_prepend)

end

end
