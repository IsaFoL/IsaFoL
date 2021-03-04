theory CDCL_NOT
imports
  Weidenbach_Book_Base.WB_List_More
  Weidenbach_Book_Base.Wellfounded_More
  Entailment_Definition.Partial_Annotated_Herbrand_Interpretation
  CDCL_WNOT_Measure
begin

section \<open>NOT's CDCL\<close>

subsection \<open>Auxiliary Lemmas and Measure\<close>

text \<open>We define here some more simplification rules, or rules that have been useful as help
  for some tactic\<close>

lemma atms_of_uminus_lit_atm_of_lit_of:
  \<open>atms_of {# -lit_of x. x \<in># A#} = atm_of ` (lit_of ` (set_mset A))\<close>
  unfolding atms_of_def by (auto simp add: Fun.image_comp)

lemma atms_of_ms_single_image_atm_of_lit_of:
  \<open>atms_of_ms (unmark_s A) = atm_of ` (lit_of ` A)\<close>
  unfolding atms_of_ms_def by auto


subsection \<open>Initial Definitions\<close>

subsubsection \<open>The State\<close>

text \<open>We define here an abstraction over operation on the state we are manipulating.\<close>
locale dpll_state_ops =
  fixes
    trail :: \<open>'st \<Rightarrow> ('v, unit) ann_lits\<close> and
    clauses\<^sub>N\<^sub>O\<^sub>T :: \<open>'st \<Rightarrow> 'v clauses\<close> and
    prepend_trail :: \<open>('v, unit) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    tl_trail :: \<open>'st \<Rightarrow>'st\<close> and
    add_cls\<^sub>N\<^sub>O\<^sub>T :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    remove_cls\<^sub>N\<^sub>O\<^sub>T :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> 'st\<close>
begin
abbreviation state\<^sub>N\<^sub>O\<^sub>T :: \<open>'st \<Rightarrow> ('v, unit) ann_lit list \<times> 'v clauses\<close> where
\<open>state\<^sub>N\<^sub>O\<^sub>T S \<equiv> (trail S, clauses\<^sub>N\<^sub>O\<^sub>T S)\<close>
end

text \<open>NOT's state is basically a pair composed of the trail (i.e.\ the candidate model) and the
  set of clauses. We abstract this state to convert this state to other states. like Weidenbach's
  five-tuple.\<close>
locale dpll_state =
  dpll_state_ops
    trail clauses\<^sub>N\<^sub>O\<^sub>T prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T \<comment> \<open>related to the state\<close>
  for
    trail :: \<open>'st \<Rightarrow> ('v, unit) ann_lits\<close> and
    clauses\<^sub>N\<^sub>O\<^sub>T :: \<open>'st \<Rightarrow> 'v clauses\<close> and
    prepend_trail :: \<open>('v, unit) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    tl_trail :: \<open>'st \<Rightarrow>'st\<close> and
    add_cls\<^sub>N\<^sub>O\<^sub>T :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    remove_cls\<^sub>N\<^sub>O\<^sub>T :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> 'st\<close> +
  assumes
    prepend_trail\<^sub>N\<^sub>O\<^sub>T:
      \<open>state\<^sub>N\<^sub>O\<^sub>T (prepend_trail L st) = (L # trail st, clauses\<^sub>N\<^sub>O\<^sub>T st)\<close> and
    tl_trail\<^sub>N\<^sub>O\<^sub>T:
      \<open>state\<^sub>N\<^sub>O\<^sub>T (tl_trail st) = (tl (trail st), clauses\<^sub>N\<^sub>O\<^sub>T st)\<close> and
    add_cls\<^sub>N\<^sub>O\<^sub>T:
      \<open>state\<^sub>N\<^sub>O\<^sub>T (add_cls\<^sub>N\<^sub>O\<^sub>T C st) = (trail st, add_mset C (clauses\<^sub>N\<^sub>O\<^sub>T st))\<close> and
    remove_cls\<^sub>N\<^sub>O\<^sub>T:
      \<open>state\<^sub>N\<^sub>O\<^sub>T (remove_cls\<^sub>N\<^sub>O\<^sub>T C st) = (trail st, removeAll_mset C (clauses\<^sub>N\<^sub>O\<^sub>T st))\<close>
begin
lemma
  trail_prepend_trail[simp]:
    \<open>trail (prepend_trail L st) = L # trail st\<close>
    and
  trail_tl_trail\<^sub>N\<^sub>O\<^sub>T[simp]: \<open>trail (tl_trail st) = tl (trail st)\<close> and
  trail_add_cls\<^sub>N\<^sub>O\<^sub>T[simp]: \<open>trail (add_cls\<^sub>N\<^sub>O\<^sub>T C st) = trail st\<close> and
  trail_remove_cls\<^sub>N\<^sub>O\<^sub>T[simp]: \<open>trail (remove_cls\<^sub>N\<^sub>O\<^sub>T C st) = trail st\<close> and

  clauses_prepend_trail[simp]:
    \<open>clauses\<^sub>N\<^sub>O\<^sub>T (prepend_trail L st) = clauses\<^sub>N\<^sub>O\<^sub>T st\<close>
    and
  clauses_tl_trail[simp]: \<open>clauses\<^sub>N\<^sub>O\<^sub>T (tl_trail st) = clauses\<^sub>N\<^sub>O\<^sub>T st\<close> and
  clauses_add_cls\<^sub>N\<^sub>O\<^sub>T[simp]:
    \<open>clauses\<^sub>N\<^sub>O\<^sub>T (add_cls\<^sub>N\<^sub>O\<^sub>T C st) = add_mset C (clauses\<^sub>N\<^sub>O\<^sub>T st)\<close> and
  clauses_remove_cls\<^sub>N\<^sub>O\<^sub>T[simp]:
    \<open>clauses\<^sub>N\<^sub>O\<^sub>T (remove_cls\<^sub>N\<^sub>O\<^sub>T C st) = removeAll_mset C (clauses\<^sub>N\<^sub>O\<^sub>T st)\<close>
  using prepend_trail\<^sub>N\<^sub>O\<^sub>T[of L st] tl_trail\<^sub>N\<^sub>O\<^sub>T[of st] add_cls\<^sub>N\<^sub>O\<^sub>T[of C st] remove_cls\<^sub>N\<^sub>O\<^sub>T[of C st]
  by (cases \<open>state\<^sub>N\<^sub>O\<^sub>T st\<close>; auto)+

text \<open>We define the following function doing the backtrack in the trail:\<close>
function reduce_trail_to\<^sub>N\<^sub>O\<^sub>T :: \<open>'a list \<Rightarrow> 'st \<Rightarrow> 'st\<close> where
\<open>reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S =
  (if length (trail S) = length F \<or> trail S = [] then S else reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F (tl_trail S))\<close>
  by fast+
termination by (relation \<open>measure (\<lambda>(_, S). length (trail S))\<close>) auto

declare reduce_trail_to\<^sub>N\<^sub>O\<^sub>T.simps[simp del]

text \<open>Then we need several lemmas about the @{term reduce_trail_to\<^sub>N\<^sub>O\<^sub>T}.\<close>
lemma
  shows
  reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_Nil[simp]: \<open>trail S = [] \<Longrightarrow> reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S = S\<close> and
  reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_eq_length[simp]: \<open>length (trail S) = length F \<Longrightarrow> reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S = S\<close>
  by (auto simp: reduce_trail_to\<^sub>N\<^sub>O\<^sub>T.simps)

lemma reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_length_ne[simp]:
  \<open>length (trail S) \<noteq> length F \<Longrightarrow> trail S \<noteq> [] \<Longrightarrow>
    reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S = reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F (tl_trail S)\<close>
  by (auto simp: reduce_trail_to\<^sub>N\<^sub>O\<^sub>T.simps)

lemma trail_reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_length_le:
  assumes \<open>length F > length (trail S)\<close>
  shows \<open>trail (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S) = []\<close>
  using assms by (induction F S rule: reduce_trail_to\<^sub>N\<^sub>O\<^sub>T.induct)
    (subst reduce_trail_to\<^sub>N\<^sub>O\<^sub>T.simps, simp add: less_imp_diff_less )

lemma trail_reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_Nil[simp]:
  \<open>trail (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T [] S) = []\<close>
  by (induction "[]" S rule: reduce_trail_to\<^sub>N\<^sub>O\<^sub>T.induct)
    (subst reduce_trail_to\<^sub>N\<^sub>O\<^sub>T.simps, simp add: less_imp_diff_less )


lemma clauses_reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_Nil:
  \<open>clauses\<^sub>N\<^sub>O\<^sub>T (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T [] S) = clauses\<^sub>N\<^sub>O\<^sub>T S\<close>
  by (induction \<open>[]\<close> S rule: reduce_trail_to\<^sub>N\<^sub>O\<^sub>T.induct)
  (simp add: less_imp_diff_less reduce_trail_to\<^sub>N\<^sub>O\<^sub>T.simps)

lemma trail_reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_drop:
  \<open>trail (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S) =
    (if length (trail S) \<ge> length F
    then drop (length (trail S) - length F) (trail S)
    else [])\<close>
  apply (induction F S rule: reduce_trail_to\<^sub>N\<^sub>O\<^sub>T.induct)
  apply (rename_tac F S, case_tac \<open>trail S\<close>)
   apply auto[]
  apply (rename_tac list, case_tac \<open>Suc (length list) > length F\<close>)
   prefer 2 apply simp
  apply (subgoal_tac \<open>Suc (length list) - length F = Suc (length list - length F)\<close>)
   apply simp
  apply simp
  done

lemma reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_skip_beginning:
  assumes \<open>trail S = F' @ F\<close>
  shows \<open>trail (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S) = F\<close>
  using assms by (auto simp: trail_reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_drop)

lemma reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_clauses[simp]:
  \<open>clauses\<^sub>N\<^sub>O\<^sub>T (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S) = clauses\<^sub>N\<^sub>O\<^sub>T S\<close>
  by (induction F S rule: reduce_trail_to\<^sub>N\<^sub>O\<^sub>T.induct)
  (simp add: less_imp_diff_less reduce_trail_to\<^sub>N\<^sub>O\<^sub>T.simps)

lemma trail_eq_reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_eq:
  \<open>trail S = trail T \<Longrightarrow> trail (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S) = trail (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F T)\<close>
  apply (induction F S arbitrary: T rule: reduce_trail_to\<^sub>N\<^sub>O\<^sub>T.induct)
  by (metis trail_tl_trail\<^sub>N\<^sub>O\<^sub>T reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_eq_length reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_length_ne
    reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_Nil)

lemma trail_reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_add_cls\<^sub>N\<^sub>O\<^sub>T[simp]:
  \<open>no_dup (trail S) \<Longrightarrow>
    trail (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F (add_cls\<^sub>N\<^sub>O\<^sub>T C S)) = trail (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S)\<close>
  by (rule trail_eq_reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_eq) simp

lemma reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_trail_tl_trail_decomp[simp]:
  \<open>trail S = F' @ Decided K # F \<Longrightarrow>
     trail (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F (tl_trail S)) = F\<close>
  apply (rule reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_skip_beginning[of _ \<open>tl (F' @ Decided K # [])\<close>])
  by (cases F') (auto simp add:tl_append reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_skip_beginning)

lemma reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_length:
  \<open>length M = length M' \<Longrightarrow> reduce_trail_to\<^sub>N\<^sub>O\<^sub>T M S = reduce_trail_to\<^sub>N\<^sub>O\<^sub>T M' S\<close>
  apply (induction M S rule: reduce_trail_to\<^sub>N\<^sub>O\<^sub>T.induct)
  by (simp add: reduce_trail_to\<^sub>N\<^sub>O\<^sub>T.simps)

abbreviation trail_weight where
\<open>trail_weight S \<equiv> map ((\<lambda>l. 1 + length l) o snd) (get_all_ann_decomposition (trail S))\<close>

text \<open>As we are defining abstract states, the Isabelle equality about them is too strong: we want
  the weaker equivalence stating that two states are equal if they cannot be distinguished, i.e.\
  given the getter @{term trail} and @{term clauses\<^sub>N\<^sub>O\<^sub>T} do not distinguish them.\<close>

definition state_eq\<^sub>N\<^sub>O\<^sub>T :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> (infix "\<sim>" 50) where
\<open>S \<sim> T \<longleftrightarrow> trail S = trail T \<and> clauses\<^sub>N\<^sub>O\<^sub>T S = clauses\<^sub>N\<^sub>O\<^sub>T T\<close>

lemma state_eq\<^sub>N\<^sub>O\<^sub>T_ref[intro, simp]:
  \<open>S \<sim> S\<close>
  unfolding state_eq\<^sub>N\<^sub>O\<^sub>T_def by auto

lemma state_eq\<^sub>N\<^sub>O\<^sub>T_sym:
  \<open>S \<sim> T \<longleftrightarrow> T \<sim> S\<close>
  unfolding state_eq\<^sub>N\<^sub>O\<^sub>T_def by auto

lemma state_eq\<^sub>N\<^sub>O\<^sub>T_trans:
  \<open>S \<sim> T \<Longrightarrow> T \<sim> U \<Longrightarrow> S \<sim> U\<close>
  unfolding state_eq\<^sub>N\<^sub>O\<^sub>T_def by auto

lemma
  shows
    state_eq\<^sub>N\<^sub>O\<^sub>T_trail: \<open>S \<sim> T \<Longrightarrow> trail S = trail T\<close> and
    state_eq\<^sub>N\<^sub>O\<^sub>T_clauses: \<open>S \<sim> T \<Longrightarrow> clauses\<^sub>N\<^sub>O\<^sub>T S = clauses\<^sub>N\<^sub>O\<^sub>T T\<close>
  unfolding state_eq\<^sub>N\<^sub>O\<^sub>T_def by auto

lemmas state_simp\<^sub>N\<^sub>O\<^sub>T[simp] = state_eq\<^sub>N\<^sub>O\<^sub>T_trail state_eq\<^sub>N\<^sub>O\<^sub>T_clauses

lemma reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_state_eq\<^sub>N\<^sub>O\<^sub>T_compatible:
  assumes ST: \<open>S \<sim> T\<close>
  shows \<open>reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S \<sim> reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F T\<close>
proof -
  have \<open>clauses\<^sub>N\<^sub>O\<^sub>T (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S) = clauses\<^sub>N\<^sub>O\<^sub>T (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F T)\<close>
    using ST by auto
  moreover have \<open>trail (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S) = trail (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F T)\<close>
    using trail_eq_reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_eq[of S T F] ST by auto
  ultimately show ?thesis by (auto simp del: state_simp\<^sub>N\<^sub>O\<^sub>T simp: state_eq\<^sub>N\<^sub>O\<^sub>T_def)
qed

end \<comment> \<open>End on locale @{locale dpll_state}.\<close>


subsubsection \<open>Definition of the Transitions\<close>

text \<open>Each possible is in its own locale.\<close>
locale propagate_ops =
  dpll_state trail clauses\<^sub>N\<^sub>O\<^sub>T prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T
  for
    trail :: \<open>'st \<Rightarrow> ('v, unit) ann_lits\<close> and
    clauses\<^sub>N\<^sub>O\<^sub>T :: \<open>'st \<Rightarrow> 'v clauses\<close> and
    prepend_trail :: \<open>('v, unit) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    tl_trail :: \<open>'st \<Rightarrow>'st\<close> and
    add_cls\<^sub>N\<^sub>O\<^sub>T :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    remove_cls\<^sub>N\<^sub>O\<^sub>T :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> 'st\<close> +
  fixes
    propagate_conds :: \<open>('v, unit) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st \<Rightarrow> bool\<close>
begin
inductive propagate\<^sub>N\<^sub>O\<^sub>T :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> where
propagate\<^sub>N\<^sub>O\<^sub>T[intro]: \<open>add_mset L C \<in># clauses\<^sub>N\<^sub>O\<^sub>T S \<Longrightarrow> trail S \<Turnstile>as CNot C
    \<Longrightarrow> undefined_lit (trail S) L
    \<Longrightarrow> propagate_conds (Propagated L ()) S T
    \<Longrightarrow> T \<sim> prepend_trail (Propagated L ()) S
    \<Longrightarrow> propagate\<^sub>N\<^sub>O\<^sub>T S T\<close>
inductive_cases propagate\<^sub>N\<^sub>O\<^sub>TE[elim]: \<open>propagate\<^sub>N\<^sub>O\<^sub>T S T\<close>

end

locale decide_ops =
  dpll_state trail clauses\<^sub>N\<^sub>O\<^sub>T prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T
  for
    trail :: \<open>'st \<Rightarrow> ('v, unit) ann_lits\<close> and
    clauses\<^sub>N\<^sub>O\<^sub>T :: \<open>'st \<Rightarrow> 'v clauses\<close> and
    prepend_trail :: \<open>('v, unit) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    tl_trail :: \<open>'st \<Rightarrow>'st\<close> and
    add_cls\<^sub>N\<^sub>O\<^sub>T :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    remove_cls\<^sub>N\<^sub>O\<^sub>T :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> 'st\<close> +
  fixes
    decide_conds :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close>
begin
inductive decide\<^sub>N\<^sub>O\<^sub>T :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> where
decide\<^sub>N\<^sub>O\<^sub>T[intro]:
  \<open>undefined_lit (trail S) L \<Longrightarrow>
  atm_of L \<in> atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<Longrightarrow>
  T \<sim> prepend_trail (Decided L) S \<Longrightarrow>
  decide_conds S T \<Longrightarrow>
  decide\<^sub>N\<^sub>O\<^sub>T S T\<close>

inductive_cases decide\<^sub>N\<^sub>O\<^sub>TE[elim]: \<open>decide\<^sub>N\<^sub>O\<^sub>T S S'\<close>
end

locale backjumping_ops =
  dpll_state trail clauses\<^sub>N\<^sub>O\<^sub>T prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T
  for
    trail :: \<open>'st \<Rightarrow> ('v, unit) ann_lits\<close> and
    clauses\<^sub>N\<^sub>O\<^sub>T :: \<open>'st \<Rightarrow> 'v clauses\<close> and
    prepend_trail :: \<open>('v, unit) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    tl_trail :: \<open>'st \<Rightarrow>'st\<close> and
    add_cls\<^sub>N\<^sub>O\<^sub>T :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    remove_cls\<^sub>N\<^sub>O\<^sub>T :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> 'st\<close> +
  fixes
    backjump_conds :: \<open>'v clause \<Rightarrow> 'v clause \<Rightarrow> 'v literal \<Rightarrow> 'st \<Rightarrow> 'st \<Rightarrow> bool\<close>
begin

inductive backjump where
\<open>trail S = F' @ Decided K # F
   \<Longrightarrow> T \<sim> prepend_trail (Propagated L ()) (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S)
   \<Longrightarrow> C \<in># clauses\<^sub>N\<^sub>O\<^sub>T S
   \<Longrightarrow> trail S \<Turnstile>as CNot C
   \<Longrightarrow> undefined_lit F L
   \<Longrightarrow> atm_of L \<in> atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<union> atm_of ` (lits_of_l (trail S))
   \<Longrightarrow> clauses\<^sub>N\<^sub>O\<^sub>T S \<Turnstile>pm add_mset L C'
   \<Longrightarrow> F \<Turnstile>as CNot C'
   \<Longrightarrow> backjump_conds C C' L S T
   \<Longrightarrow> backjump S T\<close>
inductive_cases backjumpE: \<open>backjump S T\<close>

text \<open>The condition @{term \<open>atm_of L \<in> atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<union> atm_of ` (lits_of_l (trail S))\<close>}
  is not implied by the the condition @{term \<open>clauses\<^sub>N\<^sub>O\<^sub>T S \<Turnstile>pm add_mset L C'\<close>} (no negation).\<close>
end


subsection \<open>DPLL with Backjumping\<close>

locale dpll_with_backjumping_ops =
  propagate_ops trail clauses\<^sub>N\<^sub>O\<^sub>T prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T propagate_conds +
  decide_ops trail clauses\<^sub>N\<^sub>O\<^sub>T prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T decide_conds +
  backjumping_ops trail clauses\<^sub>N\<^sub>O\<^sub>T prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T backjump_conds
  for
    trail :: \<open>'st \<Rightarrow> ('v, unit) ann_lits\<close> and
    clauses\<^sub>N\<^sub>O\<^sub>T :: \<open>'st \<Rightarrow> 'v clauses\<close> and
    prepend_trail :: \<open>('v, unit) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    tl_trail :: \<open>'st \<Rightarrow>'st\<close> and
    add_cls\<^sub>N\<^sub>O\<^sub>T :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    remove_cls\<^sub>N\<^sub>O\<^sub>T :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    inv :: \<open>'st \<Rightarrow> bool\<close> and
    decide_conds :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> and
    backjump_conds :: \<open>'v clause \<Rightarrow> 'v clause \<Rightarrow> 'v literal \<Rightarrow> 'st \<Rightarrow> 'st \<Rightarrow> bool\<close> and
    propagate_conds :: \<open>('v, unit) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st \<Rightarrow> bool\<close> +
  assumes
    bj_can_jump:
      \<open>\<And>S C F' K F L.
        inv S \<Longrightarrow>
        trail S = F' @ Decided K # F \<Longrightarrow>
        C \<in># clauses\<^sub>N\<^sub>O\<^sub>T S \<Longrightarrow>
        trail S \<Turnstile>as CNot C \<Longrightarrow>
        undefined_lit F L \<Longrightarrow>
        atm_of L \<in> atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<union> atm_of ` (lits_of_l (F' @ Decided K # F)) \<Longrightarrow>
        clauses\<^sub>N\<^sub>O\<^sub>T S \<Turnstile>pm add_mset L C' \<Longrightarrow>
        F \<Turnstile>as CNot C' \<Longrightarrow>
        \<not>no_step backjump S\<close> and
    can_propagate_or_decide_or_backjump:
      \<open>atm_of L \<in> atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<Longrightarrow>
      undefined_lit (trail S) L \<Longrightarrow>
      satisfiable (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T S)) \<Longrightarrow>
      inv S \<Longrightarrow>
      no_dup (trail S) \<Longrightarrow>
      \<exists>T. decide\<^sub>N\<^sub>O\<^sub>T S T \<or> propagate\<^sub>N\<^sub>O\<^sub>T S T \<or> backjump S T\<close>
begin

text \<open>We cannot add a like condition @{term \<open>atms_of C' \<subseteq> atms_of_ms N\<close>} to ensure that we
  can backjump even if the last decision variable has disappeared from the set of clauses.

  The part of the condition @{term \<open>atm_of L \<in> atm_of ` (lits_of_l (F' @ Decided K # F))\<close>} is
  important, otherwise you are not sure that you can backtrack.\<close>

subsubsection \<open>Definition\<close>

text \<open>We define dpll with backjumping:\<close>
inductive dpll_bj :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> for S :: 'st where
bj_decide\<^sub>N\<^sub>O\<^sub>T: \<open>decide\<^sub>N\<^sub>O\<^sub>T S S' \<Longrightarrow> dpll_bj S S'\<close> |
bj_propagate\<^sub>N\<^sub>O\<^sub>T: \<open>propagate\<^sub>N\<^sub>O\<^sub>T S S' \<Longrightarrow> dpll_bj S S'\<close> |
bj_backjump: \<open>backjump S S' \<Longrightarrow> dpll_bj S S'\<close>

lemmas dpll_bj_induct = dpll_bj.induct[split_format(complete)]
thm dpll_bj_induct[OF dpll_with_backjumping_ops_axioms]
lemma dpll_bj_all_induct[consumes 2, case_names decide\<^sub>N\<^sub>O\<^sub>T propagate\<^sub>N\<^sub>O\<^sub>T backjump]:
  fixes S T :: \<open>'st\<close>
  assumes
    \<open>dpll_bj S T\<close> and
    \<open>inv S\<close>
    \<open>\<And>L T. undefined_lit (trail S) L \<Longrightarrow> atm_of L \<in> atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S)
      \<Longrightarrow> T \<sim> prepend_trail (Decided L) S
      \<Longrightarrow> P S T\<close> and
    \<open>\<And>C L T. add_mset L C \<in># clauses\<^sub>N\<^sub>O\<^sub>T S \<Longrightarrow> trail S \<Turnstile>as CNot C \<Longrightarrow> undefined_lit (trail S) L
      \<Longrightarrow> T \<sim> prepend_trail (Propagated L ()) S
      \<Longrightarrow> P S T\<close> and
    \<open>\<And>C F' K F L C' T. C \<in># clauses\<^sub>N\<^sub>O\<^sub>T S \<Longrightarrow> F' @ Decided K # F \<Turnstile>as CNot C
      \<Longrightarrow> trail S = F' @ Decided K # F
      \<Longrightarrow> undefined_lit F L
      \<Longrightarrow> atm_of L \<in> atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<union> atm_of ` (lits_of_l (F' @ Decided K # F))
      \<Longrightarrow> clauses\<^sub>N\<^sub>O\<^sub>T S \<Turnstile>pm add_mset L C'
      \<Longrightarrow> F \<Turnstile>as CNot C'
      \<Longrightarrow> T \<sim> prepend_trail (Propagated L ()) (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S)
      \<Longrightarrow> P S T\<close>
  shows \<open>P S T\<close>
  apply (induct T rule: dpll_bj_induct[OF local.dpll_with_backjumping_ops_axioms])
     apply (rule assms(1))
    using assms(3) apply blast
   apply (elim propagate\<^sub>N\<^sub>O\<^sub>TE) using assms(4) apply blast
  apply (elim backjumpE) using assms(5) \<open>inv S\<close> by simp


subsubsection \<open>Basic properties\<close>

paragraph \<open>First, some better suited induction principle\<close>
lemma dpll_bj_clauses:
  assumes \<open>dpll_bj S T\<close> and \<open>inv S\<close>
  shows \<open>clauses\<^sub>N\<^sub>O\<^sub>T S = clauses\<^sub>N\<^sub>O\<^sub>T T\<close>
  using assms by (induction rule: dpll_bj_all_induct) auto

paragraph \<open>No duplicates in the trail\<close>
lemma dpll_bj_no_dup:
  assumes \<open>dpll_bj S T\<close> and \<open>inv S\<close>
  and \<open>no_dup (trail S)\<close>
  shows \<open>no_dup (trail T)\<close>
  using assms by (induction rule: dpll_bj_all_induct)
  (auto simp add: defined_lit_map reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_skip_beginning dest: no_dup_appendD)

paragraph \<open>Valuations\<close>
lemma dpll_bj_sat_iff:
  assumes \<open>dpll_bj S T\<close> and \<open>inv S\<close>
  shows \<open>I \<Turnstile>sm clauses\<^sub>N\<^sub>O\<^sub>T S \<longleftrightarrow> I \<Turnstile>sm clauses\<^sub>N\<^sub>O\<^sub>T T\<close>
  using assms by (induction rule: dpll_bj_all_induct) auto

paragraph \<open>Clauses\<close>
lemma dpll_bj_atms_of_ms_clauses_inv:
  assumes
    \<open>dpll_bj S T\<close> and
    \<open>inv S\<close>
  shows \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) = atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T T)\<close>
  using assms by (induction rule: dpll_bj_all_induct) auto

lemma dpll_bj_atms_in_trail:
  assumes
    \<open>dpll_bj S T\<close> and
    \<open>inv S\<close> and
    \<open>atm_of ` (lits_of_l (trail S)) \<subseteq> atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S)\<close>
  shows \<open>atm_of ` (lits_of_l (trail T)) \<subseteq> atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S)\<close>
  using assms by (induction rule: dpll_bj_all_induct)
  (auto simp: in_plus_implies_atm_of_on_atms_of_ms reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_skip_beginning)

lemma dpll_bj_atms_in_trail_in_set:
  assumes \<open>dpll_bj S T\<close>and
    \<open>inv S\<close> and
  \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<subseteq> A\<close> and
  \<open>atm_of ` (lits_of_l (trail S)) \<subseteq> A\<close>
  shows \<open>atm_of ` (lits_of_l (trail T)) \<subseteq> A\<close>
  using assms by (induction rule: dpll_bj_all_induct)
  (auto simp: in_plus_implies_atm_of_on_atms_of_ms)

lemma dpll_bj_all_decomposition_implies_inv:
  assumes
    \<open>dpll_bj S T\<close> and
    inv: \<open>inv S\<close> and
    decomp: \<open>all_decomposition_implies_m (clauses\<^sub>N\<^sub>O\<^sub>T S) (get_all_ann_decomposition (trail S))\<close>
  shows \<open>all_decomposition_implies_m (clauses\<^sub>N\<^sub>O\<^sub>T T) (get_all_ann_decomposition (trail T))\<close>
  using assms(1,2)
proof (induction rule:dpll_bj_all_induct)
  case decide\<^sub>N\<^sub>O\<^sub>T
  then show ?case using decomp by auto
next
  case (propagate\<^sub>N\<^sub>O\<^sub>T C L T) note propa = this(1) and undef = this(3) and T = this(4)
  let ?M' = \<open>trail (prepend_trail (Propagated L ()) S)\<close>
  let ?N = \<open>clauses\<^sub>N\<^sub>O\<^sub>T S\<close>
  obtain a y l where ay: \<open>get_all_ann_decomposition ?M' = (a, y) # l\<close>
    by (cases \<open>get_all_ann_decomposition ?M'\<close>) fastforce+
  then have M': \<open>?M' = y @ a\<close> using get_all_ann_decomposition_decomp[of ?M'] by auto
  have M: \<open>get_all_ann_decomposition (trail S) = (a, tl y) # l\<close>
    using ay undef by (cases \<open> get_all_ann_decomposition (trail S)\<close>) auto
  have y\<^sub>0: \<open>y = (Propagated L ()) # (tl y)\<close>
    using ay undef by (auto simp add: M)
  from arg_cong[OF this, of set] have y[simp]: \<open>set y = insert (Propagated L ()) (set (tl y))\<close>
    by simp
  have tr_S: \<open>trail S = tl y @ a\<close>
    using arg_cong[OF M', of tl] y\<^sub>0 M get_all_ann_decomposition_decomp by force
  have a_Un_N_M: \<open>unmark_l a \<union> set_mset ?N \<Turnstile>ps unmark_l (tl y)\<close>
    using decomp ay unfolding all_decomposition_implies_def by (simp add: M)+

  moreover have \<open>unmark_l a \<union> set_mset ?N \<Turnstile>p {#L#}\<close> (is \<open>?I \<Turnstile>p _\<close>)
  proof (rule true_clss_cls_plus_CNot)
    show \<open>?I \<Turnstile>p add_mset L C\<close>
      using propa propagate\<^sub>N\<^sub>O\<^sub>T.prems by (auto dest!: true_clss_clss_in_imp_true_clss_cls)
  next
    have \<open>unmark_l ?M' \<Turnstile>ps CNot C\<close>
      using \<open>trail S \<Turnstile>as CNot C\<close> undef by (auto simp add: true_annots_true_clss_clss)
    have a1: \<open>unmark_l a \<union> unmark_l (tl y) \<Turnstile>ps CNot C\<close>
      using propagate\<^sub>N\<^sub>O\<^sub>T.hyps(2) tr_S true_annots_true_clss_clss
      by (force simp add: image_Un sup_commute)
    then have \<open>unmark_l a \<union> set_mset (clauses\<^sub>N\<^sub>O\<^sub>T S) \<Turnstile>ps unmark_l a \<union> unmark_l (tl y)\<close>
      using a_Un_N_M true_clss_clss_def by blast
    then show \<open>unmark_l a \<union> set_mset (clauses\<^sub>N\<^sub>O\<^sub>T S) \<Turnstile>ps CNot C\<close>
      using a1 by (meson true_clss_clss_left_right true_clss_clss_union_and
          true_clss_clss_union_l_r)
  qed
  ultimately have \<open>unmark_l a \<union> set_mset ?N \<Turnstile>ps unmark_l ?M'\<close>
    unfolding M' by (auto simp add: all_in_true_clss_clss image_Un)
  then show ?case
    using decomp T M undef unfolding ay all_decomposition_implies_def by (auto simp add: ay)
next
  case (backjump C F' K F L D T) note confl = this(2) and tr = this(3) and undef = this(4) and
    L = this(5) and N_C = this(6) and vars_D = this(5) and T = this(8)
  have decomp: \<open>all_decomposition_implies_m (clauses\<^sub>N\<^sub>O\<^sub>T S) (get_all_ann_decomposition F)\<close>
    using decomp unfolding tr all_decomposition_implies_def
    by (metis (no_types, lifting) get_all_ann_decomposition.simps(1)
      get_all_ann_decomposition_never_empty hd_Cons_tl insert_iff list.sel(3) list.set(2)
      tl_get_all_ann_decomposition_skip_some)

  obtain a b li where F: \<open>get_all_ann_decomposition F = (a, b) # li\<close>
    by (cases \<open>get_all_ann_decomposition F\<close>) auto
  have \<open>F = b @ a\<close>
    using get_all_ann_decomposition_decomp[of F a b] F by auto
  have a_N_b:\<open>unmark_l a \<union> set_mset (clauses\<^sub>N\<^sub>O\<^sub>T S) \<Turnstile>ps unmark_l b\<close>
    using decomp unfolding all_decomposition_implies_def by (auto simp add: F)

  have F_D: \<open>unmark_l F \<Turnstile>ps CNot D\<close>
    using \<open>F \<Turnstile>as CNot D\<close> by (simp add: true_annots_true_clss_clss)
  then have \<open>unmark_l a \<union> unmark_l b \<Turnstile>ps CNot D\<close>
    unfolding \<open>F = b @ a\<close> by (simp add: image_Un sup.commute)
  have a_N_CNot_D: \<open>unmark_l a \<union> set_mset (clauses\<^sub>N\<^sub>O\<^sub>T S) \<Turnstile>ps CNot D \<union> unmark_l b\<close>
    apply (rule true_clss_clss_left_right)
    using a_N_b F_D unfolding \<open>F = b @ a\<close> by (auto simp add: image_Un ac_simps)

  have a_N_D_L: \<open>unmark_l a \<union> set_mset (clauses\<^sub>N\<^sub>O\<^sub>T S) \<Turnstile>p add_mset L D\<close>
    by (simp add: N_C)
  have \<open>unmark_l a \<union> set_mset (clauses\<^sub>N\<^sub>O\<^sub>T S) \<Turnstile>p {#L#}\<close>
    using a_N_D_L a_N_CNot_D by (blast intro: true_clss_cls_plus_CNot)
  then show ?case
    using decomp T tr undef unfolding all_decomposition_implies_def by (auto simp add: F)
qed


subsubsection \<open>Termination\<close>

paragraph \<open>Using a proper measure\<close>
lemma length_get_all_ann_decomposition_append_Decided:
  \<open>length (get_all_ann_decomposition (F' @ Decided K # F)) =
    length (get_all_ann_decomposition F')
    + length (get_all_ann_decomposition (Decided K # F))
    - 1\<close>
  by (induction F' rule: ann_lit_list_induct) auto

lemma take_length_get_all_ann_decomposition_decided_sandwich:
  \<open>take (length (get_all_ann_decomposition F))
      (map (f o snd) (rev (get_all_ann_decomposition (F' @ Decided K # F))))
      =
     map (f o snd) (rev (get_all_ann_decomposition F))
    \<close>
proof (induction F' rule: ann_lit_list_induct)
  case Nil
  then show ?case by auto
next
  case (Decided K)
  then show ?case by (simp add: length_get_all_ann_decomposition_append_Decided)
next
  case (Propagated L m F') note IH = this(1)
  obtain a b l where F': \<open>get_all_ann_decomposition (F' @ Decided K # F) = (a, b) # l\<close>
    by (cases \<open>get_all_ann_decomposition (F' @ Decided K # F)\<close>) auto
  have \<open>length (get_all_ann_decomposition F) - length l = 0\<close>
    using length_get_all_ann_decomposition_append_Decided[of F' K F]
    unfolding F' by (cases \<open>get_all_ann_decomposition F'\<close>) auto
  then show ?case
    using IH by (simp add: F')
qed

lemma length_get_all_ann_decomposition_length:
  \<open>length (get_all_ann_decomposition M) \<le> 1 + length M\<close>
  by (induction M rule: ann_lit_list_induct) auto

lemma length_in_get_all_ann_decomposition_bounded:
  assumes i:\<open>i \<in> set (trail_weight S)\<close>
  shows \<open>i \<le> Suc (length (trail S))\<close>
proof -
  obtain a b where
    \<open>(a, b) \<in> set (get_all_ann_decomposition (trail S))\<close> and
    ib: \<open>i = Suc (length b)\<close>
    using i by auto
  then obtain c where \<open>trail S = c @ b @ a\<close>
    using get_all_ann_decomposition_exists_prepend' by metis
  from arg_cong[OF this, of length] show ?thesis using i ib by auto
qed


paragraph \<open>Well-foundedness\<close>
text \<open>The bounds are the following:
  \<^item> @{term \<open>1+card (atms_of_ms A)\<close>}: @{term \<open>card (atms_of_ms A)\<close>} is an upper bound on the length
  of the list. As @{term get_all_ann_decomposition} appends an possibly empty couple at the end,
  adding one is needed.
  \<^item> @{term \<open>2+card (atms_of_ms A)\<close>}: @{term \<open>card (atms_of_ms A)\<close>} is an upper bound on the number
  of elements, where adding one is necessary for the same reason as for the bound on the list, and
  one is needed to have a strict bound.
  \<close>
abbreviation unassigned_lit :: \<open>'b clause set \<Rightarrow> 'a list \<Rightarrow> nat\<close> where
  \<open>unassigned_lit N M \<equiv> card (atms_of_ms N) - length M\<close>

lemma dpll_bj_trail_mes_increasing_prop:
  fixes M :: \<open>('v, unit) ann_lits \<close> and N :: \<open>'v clauses\<close>
  assumes
    \<open>dpll_bj S T\<close> and
    \<open>inv S\<close> and
    NA: \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<subseteq> atms_of_ms A\<close> and
    MA: \<open>atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A\<close> and
    n_d: \<open>no_dup (trail S)\<close> and
    finite: \<open>finite A\<close>
  shows \<open>\<mu>\<^sub>C (1+card (atms_of_ms A)) (2+card (atms_of_ms A)) (trail_weight T)
    > \<mu>\<^sub>C (1+card (atms_of_ms A)) (2+card (atms_of_ms A)) (trail_weight S)\<close>
  using assms(1,2)
proof (induction rule: dpll_bj_all_induct)
  case (propagate\<^sub>N\<^sub>O\<^sub>T C L T) note CLN = this(1) and MC = this(2) and undef_L = this(3) and T = this(4)
  have incl: \<open>atm_of ` lits_of_l (Propagated L () # trail S) \<subseteq> atms_of_ms A\<close>
    using propagate\<^sub>N\<^sub>O\<^sub>T dpll_bj_atms_in_trail_in_set bj_propagate\<^sub>N\<^sub>O\<^sub>T NA MA CLN
    by (auto simp: in_plus_implies_atm_of_on_atms_of_ms)

  have no_dup: \<open>no_dup (Propagated L () # trail S)\<close>
    using defined_lit_map n_d undef_L by auto
  obtain a b l where M: \<open>get_all_ann_decomposition (trail S) = (a, b) # l\<close>
    by (cases \<open>get_all_ann_decomposition (trail S)\<close>) auto
  have b_le_M: \<open>length b \<le> length (trail S)\<close>
    using get_all_ann_decomposition_decomp[of \<open>trail S\<close>] by (simp add: M)
  have \<open>finite (atms_of_ms A)\<close> using finite by simp

  then have \<open>length (Propagated L () # trail S) \<le> card (atms_of_ms A)\<close>
    using incl finite unfolding no_dup_length_eq_card_atm_of_lits_of_l[OF no_dup]
    by (simp add: card_mono)
  then have latm: \<open>unassigned_lit A b = Suc (unassigned_lit A (Propagated L () # b))\<close>
    using b_le_M by auto
  then show ?case using T undef_L by (auto simp: latm M \<mu>\<^sub>C_cons)
next
  case (decide\<^sub>N\<^sub>O\<^sub>T L) note undef_L = this(1) and MC = this(2) and T = this(3)
  have incl: \<open>atm_of ` lits_of_l (Decided L # (trail S)) \<subseteq> atms_of_ms A\<close>
    using dpll_bj_atms_in_trail_in_set bj_decide\<^sub>N\<^sub>O\<^sub>T decide\<^sub>N\<^sub>O\<^sub>T.decide\<^sub>N\<^sub>O\<^sub>T[OF decide\<^sub>N\<^sub>O\<^sub>T.hyps] NA MA MC
    by auto

  have no_dup: \<open>no_dup (Decided L # (trail S))\<close>
    using defined_lit_map n_d undef_L by auto
  obtain a b l where M: \<open>get_all_ann_decomposition (trail S) = (a, b) # l\<close>
    by (cases \<open>get_all_ann_decomposition (trail S)\<close>) auto

  then have \<open>length (Decided L # (trail S)) \<le> card (atms_of_ms A)\<close>
    using incl finite unfolding no_dup_length_eq_card_atm_of_lits_of_l[OF no_dup]
    by (simp add: card_mono)
  show ?case using T undef_L by (simp add: \<mu>\<^sub>C_cons)
next
  case (backjump C F' K F L C' T) note undef_L = this(4) and MC = this(1) and tr_S = this(3) and
    L = this(5) and T = this(8)
  have incl: \<open>atm_of ` lits_of_l (Propagated L () # F) \<subseteq> atms_of_ms A\<close>
    using dpll_bj_atms_in_trail_in_set NA MA L by (auto simp: tr_S)

  have no_dup: \<open>no_dup (Propagated L () # F)\<close>
    using defined_lit_map n_d undef_L tr_S by (auto dest: no_dup_appendD)
  obtain a b l where M: \<open>get_all_ann_decomposition (trail S) = (a, b) # l\<close>
    by (cases \<open>get_all_ann_decomposition (trail S)\<close>) auto
  have b_le_M: \<open>length b \<le> length (trail S)\<close>
    using get_all_ann_decomposition_decomp[of \<open>trail S\<close>] by (simp add: M)
  have fin_atms_A: \<open>finite (atms_of_ms A)\<close> using finite by simp

  then have F_le_A: \<open>length (Propagated L () # F) \<le> card (atms_of_ms A)\<close>
    using incl finite unfolding no_dup_length_eq_card_atm_of_lits_of_l[OF no_dup]
    by (simp add: card_mono)
  have tr_S_le_A: \<open>length (trail S) \<le> card (atms_of_ms A)\<close>
    using n_d MA by (metis fin_atms_A card_mono no_dup_length_eq_card_atm_of_lits_of_l)
  obtain a b l where F: \<open>get_all_ann_decomposition F = (a, b) # l\<close>
    by (cases \<open>get_all_ann_decomposition F\<close>) auto
  then have \<open>F = b @ a\<close>
    using get_all_ann_decomposition_decomp[of \<open>Propagated L () # F\<close> a
      \<open>Propagated L () # b\<close>] by simp
  then have latm: \<open>unassigned_lit A b = Suc (unassigned_lit A (Propagated L () # b))\<close>
     using F_le_A by simp
  obtain rem where
    rem:\<open>map (\<lambda>a. Suc (length (snd a))) (rev (get_all_ann_decomposition (F' @ Decided K # F)))
    = map (\<lambda>a. Suc (length (snd a))) (rev (get_all_ann_decomposition F)) @ rem\<close>
    using take_length_get_all_ann_decomposition_decided_sandwich[of F \<open>\<lambda>a. Suc (length a)\<close> F' K]
    unfolding o_def by (metis append_take_drop_id)
  then have rem: \<open>map (\<lambda>a. Suc (length (snd a)))
      (get_all_ann_decomposition (F' @ Decided K # F))
    = rev rem @ map (\<lambda>a. Suc (length (snd a))) ((get_all_ann_decomposition F))\<close>
    by (simp add: rev_map[symmetric] rev_swap)
  have \<open>length (rev rem @ map (\<lambda>a. Suc (length (snd a))) (get_all_ann_decomposition F))
          \<le> Suc (card (atms_of_ms A))\<close>
    using arg_cong[OF rem, of length] tr_S_le_A
    length_get_all_ann_decomposition_length[of \<open>F' @ Decided K # F\<close>] tr_S by auto
  moreover {
    { fix i :: nat and xs :: \<open>'a list\<close>
      have \<open>i < length xs \<Longrightarrow> length xs - Suc i < length xs\<close>
        by auto
      then have H: \<open>i<length xs \<Longrightarrow> rev xs ! i \<in> set xs\<close>
        using rev_nth[of i xs] unfolding in_set_conv_nth by (force simp add: in_set_conv_nth)
    } note H = this
    have \<open>\<forall>i<length rem. rev rem ! i < card (atms_of_ms A) + 2\<close>
      using tr_S_le_A length_in_get_all_ann_decomposition_bounded[of _ S] unfolding tr_S
      by (force simp add: o_def rem dest!: H intro: length_get_all_ann_decomposition_length) }
  ultimately show ?case
    using \<mu>\<^sub>C_bounded[of \<open>rev rem\<close> \<open>card (atms_of_ms A)+2\<close> \<open>unassigned_lit A l\<close>] T undef_L
    by (simp add: rem \<mu>\<^sub>C_append \<mu>\<^sub>C_cons F tr_S)
qed

lemma dpll_bj_trail_mes_decreasing_prop:
  assumes dpll: \<open>dpll_bj S T\<close> and inv: \<open>inv S\<close> and
  N_A: \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<subseteq> atms_of_ms A\<close> and
  M_A: \<open>atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A\<close> and
  nd: \<open>no_dup (trail S)\<close> and
  fin_A: \<open>finite A\<close>
  shows \<open>(2+card (atms_of_ms A)) ^ (1+card (atms_of_ms A))
               - \<mu>\<^sub>C (1+card (atms_of_ms A)) (2+card (atms_of_ms A)) (trail_weight T)
            < (2+card (atms_of_ms A)) ^ (1+card (atms_of_ms A))
               - \<mu>\<^sub>C (1+card (atms_of_ms A)) (2+card (atms_of_ms A)) (trail_weight S)\<close>
proof -
  let ?b = \<open>2+card (atms_of_ms A)\<close>
  let ?s = \<open>1+card (atms_of_ms A)\<close>
  let ?\<mu> = \<open>\<mu>\<^sub>C ?s ?b\<close>
  have M'_A: \<open>atm_of ` lits_of_l (trail T) \<subseteq> atms_of_ms A\<close>
    by (meson M_A N_A dpll dpll_bj_atms_in_trail_in_set inv)
  have nd': \<open>no_dup (trail T)\<close>
    using \<open>dpll_bj S T\<close> dpll_bj_no_dup nd inv by blast
  { fix i :: nat and xs :: \<open>'a list\<close>
    have \<open>i < length xs \<Longrightarrow> length xs - Suc i < length xs\<close>
      by auto
    then have H: \<open>i<length xs \<Longrightarrow> xs ! i \<in> set xs\<close>
      using rev_nth[of i xs] unfolding in_set_conv_nth by (force simp add: in_set_conv_nth)
  } note H = this

  have l_M_A: \<open>length (trail S) \<le> card (atms_of_ms A)\<close>
    by (simp add: fin_A M_A card_mono no_dup_length_eq_card_atm_of_lits_of_l nd)
  have l_M'_A: \<open>length (trail T) \<le> card (atms_of_ms A)\<close>
    by (simp add: fin_A M'_A card_mono no_dup_length_eq_card_atm_of_lits_of_l nd')
  have l_trail_weight_M: \<open>length (trail_weight T) \<le> 1+card (atms_of_ms A)\<close>
     using l_M'_A length_get_all_ann_decomposition_length[of \<open>trail T\<close>] by auto
  have bounded_M: \<open>\<forall>i<length (trail_weight T). (trail_weight T)! i < card (atms_of_ms A) + 2\<close>
    using length_in_get_all_ann_decomposition_bounded[of _ T] l_M'_A
    by (metis (no_types, lifting) H Nat.le_trans add_2_eq_Suc' not_le not_less_eq_eq)

  from dpll_bj_trail_mes_increasing_prop[OF dpll inv N_A M_A nd fin_A]
  have \<open>\<mu>\<^sub>C ?s ?b (trail_weight S) < \<mu>\<^sub>C ?s ?b (trail_weight T)\<close> by simp
  moreover from \<mu>\<^sub>C_bounded[OF bounded_M l_trail_weight_M]
    have \<open>\<mu>\<^sub>C ?s ?b (trail_weight T) \<le> ?b ^ ?s\<close> by auto
  ultimately show ?thesis by linarith
qed

lemma wf_dpll_bj: (*  \htmllink{wf_dpll_bj} *)
  assumes fin: \<open>finite A\<close>
  shows \<open>wf {(T, S). dpll_bj S T
    \<and> atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<subseteq> atms_of_ms A \<and> atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A
    \<and> no_dup (trail S) \<and> inv S}\<close>
  (is \<open>wf ?A\<close>)
proof (rule wf_bounded_measure[of _
        \<open>\<lambda>_. (2 + card (atms_of_ms A))^(1 + card (atms_of_ms A))\<close>
        \<open>\<lambda>S. \<mu>\<^sub>C (1+card (atms_of_ms A)) (2+card (atms_of_ms A)) (trail_weight S)\<close>])
  fix a b :: \<open>'st\<close>
  let ?b = \<open>2+card (atms_of_ms A)\<close>
  let ?s = \<open>1+card (atms_of_ms A)\<close>
  let ?\<mu> = \<open>\<mu>\<^sub>C ?s ?b\<close>
  assume ab: \<open>(b, a) \<in> ?A\<close>

  have fin_A: \<open>finite (atms_of_ms A)\<close>
    using fin by auto
  have
    dpll_bj: \<open>dpll_bj a b\<close> and
    N_A: \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T a) \<subseteq> atms_of_ms A\<close> and
    M_A: \<open>atm_of ` lits_of_l (trail a) \<subseteq> atms_of_ms A\<close> and
    nd: \<open>no_dup (trail a)\<close> and
    inv: \<open>inv a\<close>
    using ab by auto

  have M'_A: \<open>atm_of ` lits_of_l (trail b) \<subseteq> atms_of_ms A\<close>
    by (meson M_A N_A \<open>dpll_bj a b\<close> dpll_bj_atms_in_trail_in_set inv)
  have nd': \<open>no_dup (trail b)\<close>
    using \<open>dpll_bj a b\<close> dpll_bj_no_dup nd inv by blast
  { fix i :: nat and xs :: \<open>'a list\<close>
    have \<open>i < length xs \<Longrightarrow> length xs - Suc i < length xs\<close>
      by auto
    then have H: \<open>i<length xs \<Longrightarrow> xs ! i \<in> set xs\<close>
      using rev_nth[of i xs] unfolding in_set_conv_nth by (force simp add: in_set_conv_nth)
  } note H = this

  have l_M_A: \<open>length (trail a) \<le> card (atms_of_ms A)\<close>
    by (simp add: fin_A M_A card_mono no_dup_length_eq_card_atm_of_lits_of_l nd)
  have l_M'_A: \<open>length (trail b) \<le> card (atms_of_ms A)\<close>
    by (simp add: fin_A M'_A card_mono no_dup_length_eq_card_atm_of_lits_of_l nd')
  have l_trail_weight_M: \<open>length (trail_weight b) \<le> 1+card (atms_of_ms A)\<close>
     using l_M'_A length_get_all_ann_decomposition_length[of \<open>trail b\<close>] by auto
  have bounded_M: \<open>\<forall>i<length (trail_weight b). (trail_weight b)! i < card (atms_of_ms A) + 2\<close>
    using length_in_get_all_ann_decomposition_bounded[of _ b] l_M'_A
    by (metis (no_types, lifting) Nat.le_trans One_nat_def Suc_1 add.right_neutral add_Suc_right
      le_imp_less_Suc less_eq_Suc_le nth_mem)

  from dpll_bj_trail_mes_increasing_prop[OF dpll_bj inv N_A M_A nd fin]
  have \<open>\<mu>\<^sub>C ?s ?b (trail_weight a) < \<mu>\<^sub>C ?s ?b (trail_weight b)\<close> by simp
  moreover from \<mu>\<^sub>C_bounded[OF bounded_M l_trail_weight_M]
    have \<open>\<mu>\<^sub>C ?s ?b (trail_weight b) \<le> ?b ^ ?s\<close> by auto
  ultimately show \<open>?b ^ ?s \<le> ?b ^ ?s \<and>
           \<mu>\<^sub>C ?s ?b (trail_weight b) \<le> ?b ^ ?s \<and>
           \<mu>\<^sub>C ?s ?b (trail_weight a) < \<mu>\<^sub>C ?s ?b (trail_weight b)\<close>
    by blast
qed

paragraph \<open>Alternative termination proof\<close>

abbreviation DPLL_mes\<^sub>W where
  \<open>DPLL_mes\<^sub>W A M \<equiv>
    map (\<lambda>L. if is_decided L then 2::nat else 1) (rev M) @ replicate (card A - length M) 3\<close>

lemma distinctcard_atm_of_lit_of_eq_length:
  assumes "no_dup S"
  shows "card (atm_of ` lits_of_l S) = length S"
  using assms by (induct S) (auto simp add: image_image lits_of_def no_dup_def)

lemma dpll_bj_trail_mes_decreasing_less_than:
  assumes dpll: \<open>dpll_bj S T\<close> and inv: \<open>inv S\<close> and
    N_A: \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<subseteq> atms_of_ms A\<close> and
    M_A: \<open>atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A\<close> and
    nd: \<open>no_dup (trail S)\<close> and
    fin_A: \<open>finite A\<close>
  shows \<open>(DPLL_mes\<^sub>W (atms_of_ms A) (trail T), DPLL_mes\<^sub>W (atms_of_ms A) (trail S)) \<in>
    lexn less_than (card ((atms_of_ms A)))\<close>
  using assms(1,2)
proof (induction rule: dpll_bj_all_induct)
  case (decide\<^sub>N\<^sub>O\<^sub>T L T)
  define n where
    \<open>n = card (atms_of_ms A) - card (atm_of ` lits_of_l (trail S))\<close>

  have [simp]: \<open>length (trail S) = card (atm_of ` lits_of_l (trail S))\<close>
    using nd by (auto simp: no_dup_def lits_of_def image_image dest: distinct_card)
  have \<open>atm_of L \<notin> atm_of ` lits_of_l (trail S)\<close>
    by (metis decide\<^sub>N\<^sub>O\<^sub>T.hyps(1) defined_lit_map imageE in_lits_of_l_defined_litD)

  have \<open>card (atms_of_ms A) > card (atm_of ` lits_of_l (trail S))\<close>
    by (metis N_A \<open>atm_of L \<notin> atm_of ` lits_of_l (trail S)\<close> atms_of_ms_finite card_seteq decide\<^sub>N\<^sub>O\<^sub>T.hyps(2)
        M_A fin_A not_le subsetCE)
  then have
    n_0: \<open>n > 0\<close> and
    n_Suc: \<open>card (atms_of_ms A) - Suc (card (atm_of ` lits_of_l (trail S))) = n - 1\<close>
    unfolding n_def by auto

  show ?case
    using fin_A decide\<^sub>N\<^sub>O\<^sub>T n_0 unfolding state_eq\<^sub>N\<^sub>O\<^sub>T_trail[OF decide\<^sub>N\<^sub>O\<^sub>T(3)]
    by (cases n) (auto simp: prepend_same_lexn n_def[symmetric] n_Suc lexn_Suc
        simp del: state_simp\<^sub>N\<^sub>O\<^sub>T lexn.simps)
next
  case (propagate\<^sub>N\<^sub>O\<^sub>T C L T) note C = this(1) and undef = this(3) and T = this(3)
  then have \<open>card (atms_of_ms A) > length (trail S)\<close>
  proof -
    have f7: "atm_of L \<in> atms_of_ms A"
      using N_A C in_m_in_literals by blast
    have "undefined_lit (trail S) (- L)"
      using undef by auto
    then show ?thesis
      using f7 nd fin_A M_A undef by (metis atm_of_in_atm_of_set_in_uminus atms_of_ms_finite
          card_seteq in_lits_of_l_defined_litD leI no_dup_length_eq_card_atm_of_lits_of_l)
  qed
  then show ?case
    using fin_A unfolding state_eq\<^sub>N\<^sub>O\<^sub>T_trail[OF propagate\<^sub>N\<^sub>O\<^sub>T(4)]
    by (cases \<open>card (atms_of_ms A) - length (trail S)\<close>)
      (auto simp: prepend_same_lexn lexn_Suc
        simp del: state_simp\<^sub>N\<^sub>O\<^sub>T lexn.simps)
next
  case (backjump C F' K F L C' T) note tr_S = this(3)
  have \<open>trail (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S) = F\<close>
    by (simp add: tr_S)
  have \<open>no_dup F\<close>
    using nd tr_S by (auto dest: no_dup_appendD)
  then have card_A_F: \<open>card (atms_of_ms A) > length F\<close>
    using distinctcard_atm_of_lit_of_eq_length[of \<open>trail S\<close>] card_mono[OF _ M_A] fin_A nd tr_S
    by auto
  have \<open>no_dup (F' @ F)\<close>
    using nd tr_S by (auto dest: no_dup_appendD)
  then have \<open>no_dup F'\<close>
    apply (subst (asm) no_dup_rev[symmetric])
    using nd tr_S by (auto dest: no_dup_appendD)
  then have card_A_F': \<open>card (atms_of_ms A) > length F' + length F\<close>
    using distinctcard_atm_of_lit_of_eq_length[of \<open>trail S\<close>] card_mono[OF _ M_A] fin_A nd tr_S
    by auto
  show ?case
    using card_A_F card_A_F'
    unfolding state_eq\<^sub>N\<^sub>O\<^sub>T_trail[OF backjump(8)]
    by (cases \<open>card (atms_of_ms A) - length F\<close>)
      (auto simp: tr_S prepend_same_lexn lexn_Suc simp del: state_simp\<^sub>N\<^sub>O\<^sub>T lexn.simps)
qed

lemma
  assumes fin[simp]: \<open>finite A\<close>
  shows \<open>wf {(T, S). dpll_bj S T
    \<and> atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<subseteq> atms_of_ms A \<and> atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A
    \<and> no_dup (trail S) \<and> inv S}\<close>
    (is \<open>wf ?A\<close>)
  unfolding conj_commute[of \<open>dpll_bj _ _\<close>]
  apply (rule wf_wf_if_measure'[of _ _ _  \<open>\<lambda>S. DPLL_mes\<^sub>W ((atms_of_ms A)) (trail S)\<close>])
   apply (rule wf_lexn)
   apply (rule wf_less_than)
  by (rule dpll_bj_trail_mes_decreasing_less_than; use fin in simp)


subsubsection \<open>Normal Forms\<close>

text \<open>
  We prove that given a normal form of DPLL, with some structural invariants, then either @{term N}
  is satisfiable and the built valuation @{term M} is a model; or @{term N} is unsatisfiable.

  Idea of the proof: We have to prove tat @{term \<open>satisfiable N\<close>}, @{term \<open>\<not>M\<Turnstile>as N\<close>}
  and there is no remaining step is incompatible.
  \<^enum> The @{term decide} rule tells us that every variable in @{term N} has a value.
  \<^enum> The assumption @{term \<open>\<not>M\<Turnstile>as N\<close>} implies that there is conflict.
  \<^enum> There is at least one decision in the trail (otherwise, @{term M} would be a model of the set
    of clauses @{term N}).
  \<^enum> Now if we build the clause with all the decision literals of the trail, we can apply the
  @{term backjump} rule.

  The assumption are saying that we have a finite upper bound @{term A} for the literals, that we
  cannot do any step @{term \<open>no_step dpll_bj S\<close>}\<close>
theorem dpll_backjump_final_state:
  fixes A :: \<open>'v clause set\<close> and S T :: \<open>'st\<close>
  assumes
    \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<subseteq> atms_of_ms A\<close> and
    \<open>atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A\<close> and
    \<open>no_dup (trail S)\<close> and
    \<open>finite A\<close> and
    inv: \<open>inv S\<close> and
    n_d: \<open>no_dup (trail S)\<close> and
    n_s: \<open>no_step dpll_bj S\<close> and
    decomp: \<open>all_decomposition_implies_m (clauses\<^sub>N\<^sub>O\<^sub>T S) (get_all_ann_decomposition (trail S))\<close>
  shows \<open>unsatisfiable (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T S))
    \<or> (trail S \<Turnstile>asm clauses\<^sub>N\<^sub>O\<^sub>T S \<and> satisfiable (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T S)))\<close>
proof -
  let ?N = \<open>set_mset (clauses\<^sub>N\<^sub>O\<^sub>T S)\<close>
  let ?M = \<open>trail S\<close>
  consider
      (sat) \<open>satisfiable ?N\<close> and \<open>?M \<Turnstile>as ?N\<close>
    | (sat') \<open>satisfiable ?N\<close> and \<open>\<not> ?M \<Turnstile>as ?N\<close>
    | (unsat) \<open>unsatisfiable ?N\<close>
    by auto
  then show ?thesis
    proof cases
      case sat' note sat = this(1) and M = this(2)
      obtain C where \<open>C \<in> ?N\<close> and \<open>\<not>?M \<Turnstile>a C\<close> using M unfolding true_annots_def by auto
      obtain I :: \<open>'v literal set\<close> where
        \<open>I \<Turnstile>s ?N\<close> and
        cons: \<open>consistent_interp I\<close> and
        tot: \<open>total_over_m I ?N\<close> and
        atm_I_N: \<open>atm_of `I \<subseteq> atms_of_ms ?N\<close>
        using sat unfolding satisfiable_def_min by auto
      let ?I = \<open>I \<union> {P| P. P \<in> lits_of_l ?M \<and> atm_of P \<notin> atm_of ` I}\<close>
      let ?O = \<open>{unmark L |L. is_decided L \<and> L \<in> set ?M \<and> atm_of (lit_of L) \<notin> atms_of_ms ?N}\<close>
      have cons_I': \<open>consistent_interp ?I\<close>
        using cons using \<open>no_dup ?M\<close> unfolding consistent_interp_def
        by (auto simp add: atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set lits_of_def
          dest!: no_dup_cannot_not_lit_and_uminus)
      have tot_I': \<open>total_over_m ?I (?N \<union> unmark_l ?M)\<close>
        using tot atm_I_N unfolding total_over_m_def total_over_set_def
        by (fastforce simp: image_iff lits_of_def)
      have \<open>{P |P. P \<in> lits_of_l ?M \<and> atm_of P \<notin> atm_of ` I} \<Turnstile>s ?O\<close>
        using \<open>I\<Turnstile>s ?N\<close> atm_I_N by (auto simp add: atm_of_eq_atm_of true_clss_def lits_of_def)
      then have I'_N: \<open>?I \<Turnstile>s ?N \<union> ?O\<close>
        using \<open>I\<Turnstile>s ?N\<close> true_clss_union_increase by force
      have tot': \<open>total_over_m ?I (?N\<union>?O)\<close>
        using atm_I_N tot unfolding total_over_m_def total_over_set_def
        by (force simp: lits_of_def elim!: is_decided_ex_Decided)

      have atms_N_M: \<open>atms_of_ms ?N \<subseteq> atm_of ` lits_of_l ?M\<close>
      proof (rule ccontr)
        assume \<open>\<not> ?thesis\<close>
        then obtain l :: 'v where
          l_N: \<open>l \<in> atms_of_ms ?N\<close> and
          l_M: \<open>l \<notin> atm_of ` lits_of_l ?M\<close>
          by auto
        have \<open>undefined_lit ?M (Pos l)\<close>
          using l_M by (metis Decided_Propagated_in_iff_in_lits_of_l
              atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set literal.sel(1))
        then show False
          using l_N n_s can_propagate_or_decide_or_backjump[of \<open>Pos l\<close> S] inv n_d sat
          by (auto dest: dpll_bj.intros)
      qed
      have \<open>?M \<Turnstile>as CNot C\<close>
        apply (rule all_variables_defined_not_imply_cnot)
        using \<open>C \<in> set_mset (clauses\<^sub>N\<^sub>O\<^sub>T S)\<close> \<open>\<not> trail S \<Turnstile>a C\<close>
           atms_N_M by (auto dest: atms_of_atms_of_ms_mono)
      have \<open>\<exists>l \<in> set ?M. is_decided l\<close>
        proof (rule ccontr)
          let ?O = \<open>{unmark L |L. is_decided L \<and> L \<in> set ?M \<and> atm_of (lit_of L) \<notin> atms_of_ms ?N}\<close>
          have \<theta>[iff]: \<open>\<And>I. total_over_m I (?N \<union> ?O \<union> unmark_l ?M)
            \<longleftrightarrow> total_over_m I (?N \<union>unmark_l ?M)\<close>
            unfolding total_over_set_def total_over_m_def atms_of_ms_def by blast
          assume \<open>\<not> ?thesis\<close>
          then have [simp]:\<open>{unmark L |L. is_decided L \<and> L \<in> set ?M}
            = {unmark L |L. is_decided L \<and> L \<in> set ?M \<and> atm_of (lit_of L) \<notin> atms_of_ms ?N}\<close>
            by auto
          then have \<open>?N \<union> ?O \<Turnstile>ps unmark_l ?M\<close>
            using all_decomposition_implies_propagated_lits_are_implied[OF decomp] by auto

          then have \<open>?I \<Turnstile>s unmark_l ?M\<close>
            using cons_I' I'_N tot_I' \<open>?I \<Turnstile>s ?N \<union> ?O\<close> unfolding \<theta> true_clss_clss_def by blast
          then have \<open>lits_of_l ?M \<subseteq> ?I\<close>
            unfolding true_clss_def lits_of_def by auto
          then have \<open>?M \<Turnstile>as ?N\<close>
            using I'_N \<open>C \<in> ?N\<close> \<open>\<not> ?M \<Turnstile>a C\<close> cons_I' atms_N_M
            by (meson \<open>trail S \<Turnstile>as CNot C\<close> consistent_CNot_not rev_subsetD sup_ge1 true_annot_def
              true_annots_def true_cls_mono_set_mset_l true_clss_def)
          then show False using M by fast
        qed
      from List.split_list_first_propE[OF this] obtain K :: \<open>'v literal\<close> and
        F F' :: \<open>('v, unit) ann_lits\<close> where
        M_K: \<open>?M = F' @ Decided K # F\<close> and
        nm: \<open>\<forall>f\<in>set F'. \<not>is_decided f\<close>
        by (metis (full_types) is_decided_ex_Decided old.unit.exhaust)
      let ?K = \<open>Decided K :: ('v, unit) ann_lit\<close>
      have \<open>?K \<in> set ?M\<close>
        unfolding M_K by auto
      let ?C = \<open>image_mset lit_of {#L\<in>#mset ?M. is_decided L \<and> L\<noteq>?K#} :: 'v clause\<close>
      let ?C' = \<open>set_mset (image_mset (\<lambda>L::'v literal. {#L#}) (?C + unmark ?K))\<close>
      have \<open>?N \<union> {unmark L |L. is_decided L \<and> L \<in> set ?M} \<Turnstile>ps unmark_l ?M\<close>
        using all_decomposition_implies_propagated_lits_are_implied[OF decomp] .
      moreover have C': \<open>?C' = {unmark L |L. is_decided L \<and> L \<in> set ?M}\<close>
        unfolding M_K by standard force+
      ultimately have N_C_M: \<open>?N \<union> ?C' \<Turnstile>ps unmark_l ?M\<close>
        by auto
      have N_M_False: \<open>?N \<union> (\<lambda>L. unmark L) ` (set ?M) \<Turnstile>ps {{#}}\<close>
        unfolding true_clss_clss_def true_annots_def Ball_def true_annot_def
      proof (intro allI impI)
        fix LL :: "'v literal set"
        assume
          tot: \<open>total_over_m LL (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T S) \<union> unmark_l (trail S) \<union> {{#}})\<close> and
          cons: \<open>consistent_interp LL\<close> and
          LL: \<open>LL \<Turnstile>s set_mset (clauses\<^sub>N\<^sub>O\<^sub>T S) \<union> unmark_l (trail S)\<close>
        have \<open>total_over_m LL (CNot C)\<close>
          by (metis \<open>C \<in># clauses\<^sub>N\<^sub>O\<^sub>T S\<close> insert_absorb tot total_over_m_CNot_toal_over_m
              total_over_m_insert total_over_m_union)
        then have "total_over_m LL (unmark_l (trail S) \<union> CNot C)"
            using tot by force
          then show "LL \<Turnstile>s {{#}}"
            using tot cons LL
            by (metis (no_types) \<open>C \<in># clauses\<^sub>N\<^sub>O\<^sub>T S\<close> \<open>trail S \<Turnstile>as CNot C\<close> consistent_CNot_not
                true_annots_true_clss_clss true_clss_clss_def true_clss_def true_clss_union)
      qed
      have \<open>undefined_lit F K\<close> using \<open>no_dup ?M\<close> unfolding M_K by (auto simp: defined_lit_map)
      moreover {
        have \<open>?N \<union> ?C' \<Turnstile>ps {{#}}\<close>
          proof -
            have A: \<open>?N \<union> ?C' \<union> unmark_l ?M = ?N \<union> unmark_l ?M\<close>
              unfolding M_K by auto
            show ?thesis
              using true_clss_clss_left_right[OF N_C_M, of \<open>{{#}}\<close>] N_M_False unfolding A by auto
          qed
        have \<open>?N \<Turnstile>p image_mset uminus ?C + {#-K#}\<close>
          unfolding true_clss_cls_def true_clss_clss_def total_over_m_def
          proof (intro allI impI)
            fix I
            assume
              tot: \<open>total_over_set I (atms_of_ms (?N \<union> {image_mset uminus ?C+ {#- K#}}))\<close> and
              cons: \<open>consistent_interp I\<close> and
              \<open>I \<Turnstile>s ?N\<close>
            have \<open>(K \<in> I \<and> -K \<notin> I) \<or> (-K \<in> I \<and> K \<notin> I)\<close>
              using cons tot unfolding consistent_interp_def by (cases K) auto
            have \<open> {a \<in> set (trail S). is_decided a \<and> a \<noteq> Decided K} =
              set (trail S) \<inter> {L. is_decided L \<and> L \<noteq> Decided K}\<close>
             by auto
            then have tot': \<open>total_over_set I
               (atm_of ` lit_of ` (set ?M \<inter> {L. is_decided L \<and> L \<noteq> Decided K}))\<close>
              using tot by (auto simp add: atms_of_uminus_lit_atm_of_lit_of)
            { fix x :: \<open>('v, unit) ann_lit\<close>
              assume
                a3: \<open>lit_of x \<notin> I\<close> and
                a1: \<open>x \<in> set ?M\<close> and
                a4: \<open>is_decided x\<close> and
                a5: \<open>x \<noteq> Decided K\<close>
              then have \<open>Pos (atm_of (lit_of x)) \<in> I \<or> Neg (atm_of (lit_of x)) \<in> I\<close>
                using a5 a4 tot' a1 unfolding total_over_set_def atms_of_s_def by blast
              moreover have f6: \<open>Neg (atm_of (lit_of x)) = - Pos (atm_of (lit_of x))\<close>
                by simp
              ultimately have \<open>- lit_of x \<in> I\<close>
                using f6 a3 by (metis (no_types) atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set
                  literal.sel(1))
            } note H = this

            have \<open>\<not>I \<Turnstile>s ?C'\<close>
              using \<open>?N \<union> ?C' \<Turnstile>ps {{#}}\<close> tot cons \<open>I \<Turnstile>s ?N\<close>
              unfolding true_clss_clss_def total_over_m_def
              by (simp add: atms_of_uminus_lit_atm_of_lit_of atms_of_ms_single_image_atm_of_lit_of)
            then show \<open>I \<Turnstile> image_mset uminus ?C + {#- K#}\<close>
              unfolding true_clss_def true_cls_def using \<open>(K \<in> I \<and> -K \<notin> I) \<or> (-K \<in> I \<and> K \<notin> I)\<close>
              by (auto dest!: H)
          qed }
      moreover have \<open>F \<Turnstile>as CNot (image_mset uminus ?C)\<close>
        using nm unfolding true_annots_def CNot_def M_K by (auto simp add: lits_of_def)
      ultimately have False
        using bj_can_jump[of S F' K F C \<open>-K\<close>
          \<open>image_mset uminus (image_mset lit_of {# L :# mset ?M. is_decided L \<and> L \<noteq> Decided K#})\<close>]
          \<open>C\<in>?N\<close> n_s \<open>?M \<Turnstile>as CNot C\<close> bj_backjump inv \<open>no_dup (trail S)\<close> sat
          unfolding M_K by auto
        then show ?thesis by fast
    qed auto
qed

end \<comment> \<open>End of the locale @{locale dpll_with_backjumping_ops}.\<close>

locale dpll_with_backjumping =
  dpll_with_backjumping_ops trail clauses\<^sub>N\<^sub>O\<^sub>T prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T inv
    decide_conds backjump_conds propagate_conds
  for
    trail :: \<open>'st \<Rightarrow> ('v, unit) ann_lits\<close> and
    clauses\<^sub>N\<^sub>O\<^sub>T :: \<open>'st \<Rightarrow> 'v clauses\<close> and
    prepend_trail :: \<open>('v, unit) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    tl_trail :: \<open>'st \<Rightarrow>'st\<close> and
    add_cls\<^sub>N\<^sub>O\<^sub>T :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    remove_cls\<^sub>N\<^sub>O\<^sub>T :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    inv :: \<open>'st \<Rightarrow> bool\<close> and
    decide_conds :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> and
    backjump_conds :: \<open>'v clause \<Rightarrow> 'v clause \<Rightarrow> 'v literal \<Rightarrow> 'st \<Rightarrow> 'st \<Rightarrow> bool\<close> and
    propagate_conds :: \<open>('v, unit) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st \<Rightarrow> bool\<close>
  +
  assumes dpll_bj_inv: \<open>\<And>S T. dpll_bj S T \<Longrightarrow> inv S \<Longrightarrow> inv T\<close>
begin

lemma rtranclp_dpll_bj_inv:
  assumes \<open>dpll_bj\<^sup>*\<^sup>* S T\<close> and \<open>inv S\<close>
  shows \<open>inv T\<close>
  using assms by (induction rule: rtranclp_induct)
    (auto simp add: dpll_bj_no_dup intro: dpll_bj_inv)

lemma rtranclp_dpll_bj_no_dup:
  assumes \<open>dpll_bj\<^sup>*\<^sup>* S T\<close> and \<open>inv S\<close>
  and \<open>no_dup (trail S)\<close>
  shows \<open>no_dup (trail T)\<close>
  using assms by (induction rule: rtranclp_induct)
  (auto simp add: dpll_bj_no_dup dest: rtranclp_dpll_bj_inv dpll_bj_inv)

lemma rtranclp_dpll_bj_atms_of_ms_clauses_inv:
  assumes
    \<open>dpll_bj\<^sup>*\<^sup>* S T\<close> and \<open>inv S\<close>
  shows \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) = atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T T)\<close>
  using assms by (induction rule: rtranclp_induct)
    (auto dest: rtranclp_dpll_bj_inv dpll_bj_atms_of_ms_clauses_inv)

lemma rtranclp_dpll_bj_atms_in_trail:
  assumes
    \<open>dpll_bj\<^sup>*\<^sup>* S T\<close> and
    \<open>inv S\<close> and
    \<open>atm_of ` (lits_of_l (trail S)) \<subseteq> atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S)\<close>
  shows \<open>atm_of ` (lits_of_l (trail T)) \<subseteq> atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T T)\<close>
  using assms apply (induction rule: rtranclp_induct)
  using dpll_bj_atms_in_trail dpll_bj_atms_of_ms_clauses_inv rtranclp_dpll_bj_inv by auto

lemma rtranclp_dpll_bj_sat_iff:
  assumes \<open>dpll_bj\<^sup>*\<^sup>* S T\<close> and \<open>inv S\<close>
  shows \<open>I \<Turnstile>sm clauses\<^sub>N\<^sub>O\<^sub>T S \<longleftrightarrow> I \<Turnstile>sm clauses\<^sub>N\<^sub>O\<^sub>T T\<close>
  using assms by (induction rule: rtranclp_induct)
    (auto dest!: dpll_bj_sat_iff simp: rtranclp_dpll_bj_inv)

lemma rtranclp_dpll_bj_atms_in_trail_in_set:
  assumes
    \<open>dpll_bj\<^sup>*\<^sup>* S T\<close> and
    \<open>inv S\<close>
    \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<subseteq> A\<close> and
    \<open>atm_of ` (lits_of_l (trail S)) \<subseteq> A\<close>
  shows \<open>atm_of ` (lits_of_l (trail T)) \<subseteq> A\<close>
  using assms by (induction rule: rtranclp_induct)
  (auto dest: rtranclp_dpll_bj_inv
    simp: dpll_bj_atms_in_trail_in_set rtranclp_dpll_bj_atms_of_ms_clauses_inv rtranclp_dpll_bj_inv)

lemma rtranclp_dpll_bj_all_decomposition_implies_inv:
  assumes
    \<open>dpll_bj\<^sup>*\<^sup>* S T\<close> and
    \<open>inv S\<close>
    \<open>all_decomposition_implies_m (clauses\<^sub>N\<^sub>O\<^sub>T S) (get_all_ann_decomposition (trail S))\<close>
  shows \<open>all_decomposition_implies_m (clauses\<^sub>N\<^sub>O\<^sub>T T) (get_all_ann_decomposition (trail T))\<close>
  using assms by (induction rule: rtranclp_induct)
    (auto intro: dpll_bj_all_decomposition_implies_inv simp: rtranclp_dpll_bj_inv)

lemma rtranclp_dpll_bj_inv_incl_dpll_bj_inv_trancl:
  \<open>{(T, S). dpll_bj\<^sup>+\<^sup>+ S T
    \<and> atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<subseteq> atms_of_ms A \<and> atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A
    \<and> no_dup (trail S) \<and> inv S}
     \<subseteq> {(T, S). dpll_bj S T \<and> atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<subseteq> atms_of_ms A
        \<and> atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A \<and> no_dup (trail S) \<and> inv S}\<^sup>+\<close>
    (is \<open>?A \<subseteq> ?B\<^sup>+\<close>)
proof standard
  fix x
  assume x_A: \<open>x \<in> ?A\<close>
  obtain S T::\<open>'st\<close> where
    x[simp]: \<open>x = (T, S)\<close> by (cases x) auto
  have
    \<open>dpll_bj\<^sup>+\<^sup>+ S T\<close> and
    \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<subseteq> atms_of_ms A\<close> and
    \<open>atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A\<close> and
    \<open>no_dup (trail S)\<close> and
     \<open>inv S\<close>
    using x_A by auto
  then show \<open>x \<in> ?B\<^sup>+\<close> unfolding x
    proof (induction rule: tranclp_induct)
      case base
      then show ?case by auto
    next
      case (step T U) note step = this(1) and ST = this(2) and IH = this(3)[OF this(4-7)]
        and N_A = this(4) and M_A = this(5) and nd = this(6) and inv = this(7)

      have [simp]: \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) = atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T T)\<close>
        using step rtranclp_dpll_bj_atms_of_ms_clauses_inv tranclp_into_rtranclp inv by fastforce
      have \<open>no_dup (trail T)\<close>
        using local.step nd rtranclp_dpll_bj_no_dup tranclp_into_rtranclp inv by fastforce
      moreover have \<open>atm_of ` (lits_of_l (trail T)) \<subseteq> atms_of_ms A\<close>
        by (metis inv M_A N_A local.step rtranclp_dpll_bj_atms_in_trail_in_set
          tranclp_into_rtranclp)
      moreover have \<open>inv T\<close>
         using inv local.step rtranclp_dpll_bj_inv tranclp_into_rtranclp by fastforce
      ultimately have \<open>(U, T) \<in> ?B\<close> using ST N_A M_A inv by auto
      then show ?case using IH by (rule trancl_into_trancl2)
    qed
qed

lemma wf_tranclp_dpll_bj:
  assumes fin: \<open>finite A\<close>
  shows \<open>wf {(T, S). dpll_bj\<^sup>+\<^sup>+ S T
    \<and> atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<subseteq> atms_of_ms A \<and> atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A
    \<and> no_dup (trail S) \<and> inv S}\<close>
  using wf_trancl[OF wf_dpll_bj[OF fin]] rtranclp_dpll_bj_inv_incl_dpll_bj_inv_trancl
  by (rule wf_subset)

lemma dpll_bj_sat_ext_iff:
  \<open>dpll_bj S T \<Longrightarrow> inv S \<Longrightarrow> I\<Turnstile>sextm clauses\<^sub>N\<^sub>O\<^sub>T S \<longleftrightarrow> I\<Turnstile>sextm clauses\<^sub>N\<^sub>O\<^sub>T T\<close>
  by (simp add: dpll_bj_clauses)

lemma rtranclp_dpll_bj_sat_ext_iff:
  \<open>dpll_bj\<^sup>*\<^sup>* S T \<Longrightarrow> inv S \<Longrightarrow> I\<Turnstile>sextm clauses\<^sub>N\<^sub>O\<^sub>T S \<longleftrightarrow> I\<Turnstile>sextm clauses\<^sub>N\<^sub>O\<^sub>T T\<close>
  by (induction rule: rtranclp_induct) (simp_all add: rtranclp_dpll_bj_inv dpll_bj_sat_ext_iff)

theorem full_dpll_backjump_final_state:
  fixes A :: \<open>'v clause set\<close> and S T :: \<open>'st\<close>
  assumes
    full: \<open>full dpll_bj S T\<close> and
    atms_S: \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<subseteq> atms_of_ms A\<close> and
    atms_trail: \<open>atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A\<close> and
    n_d: \<open>no_dup (trail S)\<close> and
    \<open>finite A\<close> and
    inv: \<open>inv S\<close> and
    decomp: \<open>all_decomposition_implies_m (clauses\<^sub>N\<^sub>O\<^sub>T S) (get_all_ann_decomposition (trail S))\<close>
  shows \<open>unsatisfiable (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T S))
  \<or> (trail T \<Turnstile>asm clauses\<^sub>N\<^sub>O\<^sub>T S \<and> satisfiable (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T S)))\<close>
proof -
  have st: \<open>dpll_bj\<^sup>*\<^sup>* S T\<close> and \<open>no_step dpll_bj T\<close>
    using full unfolding full_def by fast+
  moreover have \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T T) \<subseteq> atms_of_ms A\<close>
    using atms_S inv rtranclp_dpll_bj_atms_of_ms_clauses_inv st by blast
  moreover have \<open>atm_of ` lits_of_l (trail T) \<subseteq> atms_of_ms A\<close>
     using atms_S atms_trail inv rtranclp_dpll_bj_atms_in_trail_in_set st by auto
  moreover have \<open>no_dup (trail T)\<close>
    using n_d inv rtranclp_dpll_bj_no_dup st by blast
  moreover have inv: \<open>inv T\<close>
    using inv rtranclp_dpll_bj_inv st by blast
  moreover
    have decomp: \<open>all_decomposition_implies_m (clauses\<^sub>N\<^sub>O\<^sub>T T) (get_all_ann_decomposition (trail T))\<close>
      using \<open>inv S\<close> decomp rtranclp_dpll_bj_all_decomposition_implies_inv st by blast
  ultimately have \<open>unsatisfiable (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T T))
    \<or> (trail T \<Turnstile>asm clauses\<^sub>N\<^sub>O\<^sub>T T \<and> satisfiable (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T T)))\<close>
    using \<open>finite A\<close> dpll_backjump_final_state by force
  then show ?thesis
    by (meson \<open>inv S\<close> rtranclp_dpll_bj_sat_iff satisfiable_carac st true_annots_true_cls)
qed

corollary full_dpll_backjump_final_state_from_init_state: (* \htmllink{full_dpll_backjump_final_state_from_init_state}*)
  fixes A :: \<open>'v clause set\<close> and S T :: \<open>'st\<close>
  assumes
    full: \<open>full dpll_bj S T\<close> and
    \<open>trail S = []\<close> and
    \<open>clauses\<^sub>N\<^sub>O\<^sub>T S = N\<close> and
    \<open>inv S\<close>
  shows \<open>unsatisfiable (set_mset N) \<or> (trail T \<Turnstile>asm N \<and> satisfiable (set_mset N))\<close>
  using assms full_dpll_backjump_final_state[of S T \<open>set_mset N\<close>] by auto

lemma tranclp_dpll_bj_trail_mes_decreasing_prop:
  assumes dpll: \<open>dpll_bj\<^sup>+\<^sup>+ S T\<close> and inv: \<open>inv S\<close> and
  N_A: \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<subseteq> atms_of_ms A\<close> and
  M_A: \<open>atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A\<close> and
  n_d: \<open>no_dup (trail S)\<close> and
  fin_A: \<open>finite A\<close>
  shows \<open>(2+card (atms_of_ms A)) ^ (1+card (atms_of_ms A))
               - \<mu>\<^sub>C (1+card (atms_of_ms A)) (2+card (atms_of_ms A)) (trail_weight T)
            < (2+card (atms_of_ms A)) ^ (1+card (atms_of_ms A))
               - \<mu>\<^sub>C (1+card (atms_of_ms A)) (2+card (atms_of_ms A)) (trail_weight S)\<close>
  using dpll
proof induction
  case base
  then show ?case
    using N_A M_A n_d dpll_bj_trail_mes_decreasing_prop fin_A inv by blast
next
  case (step T U) note st = this(1) and dpll = this(2) and IH = this(3)
  have \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) = atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T T)\<close>
    using rtranclp_dpll_bj_atms_of_ms_clauses_inv by (metis dpll_bj_clauses dpll_bj_inv inv st
      tranclpD)
  then have N_A': \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T T) \<subseteq> atms_of_ms A\<close>
     using N_A by auto
  moreover have M_A': \<open>atm_of ` lits_of_l (trail T) \<subseteq> atms_of_ms A\<close>
    by (meson M_A N_A inv rtranclp_dpll_bj_atms_in_trail_in_set st dpll
      tranclp.r_into_trancl tranclp_into_rtranclp tranclp_trans)
  moreover have nd: \<open>no_dup (trail T)\<close>
    by (metis inv n_d rtranclp_dpll_bj_no_dup st tranclp_into_rtranclp)
  moreover have \<open>inv T\<close>
    by (meson dpll dpll_bj_inv inv rtranclp_dpll_bj_inv st tranclp_into_rtranclp)
  ultimately show ?case
    using IH dpll_bj_trail_mes_decreasing_prop[of T U A] dpll fin_A by linarith
qed

end \<comment> \<open>End of the locale @{locale dpll_with_backjumping}.\<close>


subsection \<open>CDCL\<close>

text \<open>In this section we will now define the conflict driven clause learning above DPLL: we first
  introduce the rules learn and forget, and the add these rules to the DPLL calculus.\<close>

subsubsection \<open>Learn and Forget\<close>

text \<open>Learning adds a new clause where all the literals are already included in the clauses.\<close>
locale learn_ops =
  dpll_state trail clauses\<^sub>N\<^sub>O\<^sub>T prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T
  for
    trail :: \<open>'st \<Rightarrow> ('v, unit) ann_lits\<close> and
    clauses\<^sub>N\<^sub>O\<^sub>T :: \<open>'st \<Rightarrow> 'v clauses\<close> and
    prepend_trail :: \<open>('v, unit) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    tl_trail :: \<open>'st \<Rightarrow>'st\<close> and
    add_cls\<^sub>N\<^sub>O\<^sub>T :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    remove_cls\<^sub>N\<^sub>O\<^sub>T :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> 'st\<close> +
  fixes
    learn_conds :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> bool\<close>
begin

inductive learn :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> where
learn\<^sub>N\<^sub>O\<^sub>T_rule: \<open>clauses\<^sub>N\<^sub>O\<^sub>T S \<Turnstile>pm C \<Longrightarrow>
  atms_of C \<subseteq> atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<union> atm_of ` (lits_of_l (trail S)) \<Longrightarrow>
  learn_conds C S \<Longrightarrow>
  T \<sim> add_cls\<^sub>N\<^sub>O\<^sub>T C S \<Longrightarrow>
  learn S T\<close>
inductive_cases learn\<^sub>N\<^sub>O\<^sub>TE: \<open>learn S T\<close>

lemma learn_\<mu>\<^sub>C_stable:
  assumes \<open>learn S T\<close> and \<open>no_dup (trail S)\<close>
  shows \<open>\<mu>\<^sub>C A B (trail_weight S) = \<mu>\<^sub>C A B (trail_weight T)\<close>
  using assms by (auto elim: learn\<^sub>N\<^sub>O\<^sub>TE)
end

text \<open>Forget removes an information that can be deduced from the context (e.g.\ redundant clauses,
  tautologies)\<close>
locale forget_ops =
  dpll_state trail clauses\<^sub>N\<^sub>O\<^sub>T prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T
  for
    trail :: \<open>'st \<Rightarrow> ('v, unit) ann_lits\<close> and
    clauses\<^sub>N\<^sub>O\<^sub>T :: \<open>'st \<Rightarrow> 'v clauses\<close> and
    prepend_trail :: \<open>('v, unit) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    tl_trail :: \<open>'st \<Rightarrow>'st\<close> and
    add_cls\<^sub>N\<^sub>O\<^sub>T :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    remove_cls\<^sub>N\<^sub>O\<^sub>T :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> 'st\<close> +
  fixes
    forget_conds :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> bool\<close>
begin

inductive forget\<^sub>N\<^sub>O\<^sub>T :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> where
forget\<^sub>N\<^sub>O\<^sub>T:
  \<open>removeAll_mset C(clauses\<^sub>N\<^sub>O\<^sub>T S) \<Turnstile>pm C \<Longrightarrow>
  forget_conds C S \<Longrightarrow>
  C \<in># clauses\<^sub>N\<^sub>O\<^sub>T S \<Longrightarrow>
  T \<sim> remove_cls\<^sub>N\<^sub>O\<^sub>T C S \<Longrightarrow>

  forget\<^sub>N\<^sub>O\<^sub>T S T\<close>
inductive_cases forget\<^sub>N\<^sub>O\<^sub>TE: \<open>forget\<^sub>N\<^sub>O\<^sub>T S T\<close>

lemma forget_\<mu>\<^sub>C_stable:
  assumes \<open>forget\<^sub>N\<^sub>O\<^sub>T S T\<close>
  shows \<open>\<mu>\<^sub>C A B (trail_weight S) = \<mu>\<^sub>C A B (trail_weight T)\<close>
  using assms by (auto elim!: forget\<^sub>N\<^sub>O\<^sub>TE)
end

locale learn_and_forget\<^sub>N\<^sub>O\<^sub>T =
  learn_ops trail clauses\<^sub>N\<^sub>O\<^sub>T prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T learn_conds +
  forget_ops trail clauses\<^sub>N\<^sub>O\<^sub>T prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T forget_conds
  for
    trail :: \<open>'st \<Rightarrow> ('v, unit) ann_lits\<close> and
    clauses\<^sub>N\<^sub>O\<^sub>T :: \<open>'st \<Rightarrow> 'v clauses\<close> and
    prepend_trail :: \<open>('v, unit) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    tl_trail :: \<open>'st \<Rightarrow>'st\<close> and
    add_cls\<^sub>N\<^sub>O\<^sub>T :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    remove_cls\<^sub>N\<^sub>O\<^sub>T :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    learn_conds forget_conds :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> bool\<close>
begin
inductive learn_and_forget\<^sub>N\<^sub>O\<^sub>T :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close>
where
lf_learn: \<open>learn S T \<Longrightarrow> learn_and_forget\<^sub>N\<^sub>O\<^sub>T S T\<close> |
lf_forget: \<open>forget\<^sub>N\<^sub>O\<^sub>T S T \<Longrightarrow> learn_and_forget\<^sub>N\<^sub>O\<^sub>T S T\<close>
end


subsubsection \<open>Definition of CDCL\<close>

locale conflict_driven_clause_learning_ops =
  dpll_with_backjumping_ops trail clauses\<^sub>N\<^sub>O\<^sub>T prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T
    inv decide_conds backjump_conds propagate_conds +
  learn_and_forget\<^sub>N\<^sub>O\<^sub>T trail clauses\<^sub>N\<^sub>O\<^sub>T prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T learn_conds
    forget_conds
  for
    trail :: \<open>'st \<Rightarrow> ('v, unit) ann_lits\<close> and
    clauses\<^sub>N\<^sub>O\<^sub>T :: \<open>'st \<Rightarrow> 'v clauses\<close> and
    prepend_trail :: \<open>('v, unit) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    tl_trail :: \<open>'st \<Rightarrow>'st\<close> and
    add_cls\<^sub>N\<^sub>O\<^sub>T :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    remove_cls\<^sub>N\<^sub>O\<^sub>T :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    inv :: \<open>'st \<Rightarrow> bool\<close> and
    decide_conds :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> and
    backjump_conds :: \<open>'v clause \<Rightarrow> 'v clause \<Rightarrow> 'v literal \<Rightarrow> 'st \<Rightarrow> 'st \<Rightarrow> bool\<close> and
    propagate_conds :: \<open>('v, unit) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st \<Rightarrow> bool\<close> and
    learn_conds forget_conds :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> bool\<close>
begin

inductive cdcl\<^sub>N\<^sub>O\<^sub>T :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> for S :: 'st where
c_dpll_bj: \<open>dpll_bj S S' \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T S S'\<close> |
c_learn: \<open>learn S S' \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T S S'\<close> |
c_forget\<^sub>N\<^sub>O\<^sub>T: \<open>forget\<^sub>N\<^sub>O\<^sub>T S S' \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T S S'\<close>

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_all_induct[consumes 1, case_names dpll_bj learn forget\<^sub>N\<^sub>O\<^sub>T]:
  fixes S T :: \<open>'st\<close>
  assumes \<open>cdcl\<^sub>N\<^sub>O\<^sub>T S T\<close> and
    dpll: \<open>\<And>T. dpll_bj S T \<Longrightarrow> P S T\<close> and
    learning:
      \<open>\<And>C T. clauses\<^sub>N\<^sub>O\<^sub>T S \<Turnstile>pm C \<Longrightarrow>
      atms_of C \<subseteq> atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<union> atm_of ` (lits_of_l (trail S)) \<Longrightarrow>
      T \<sim> add_cls\<^sub>N\<^sub>O\<^sub>T C S \<Longrightarrow>
      P S T\<close> and
    forgetting: \<open>\<And>C T. removeAll_mset C (clauses\<^sub>N\<^sub>O\<^sub>T S) \<Turnstile>pm C \<Longrightarrow>
      C \<in># clauses\<^sub>N\<^sub>O\<^sub>T S \<Longrightarrow>
      T \<sim> remove_cls\<^sub>N\<^sub>O\<^sub>T C S \<Longrightarrow>
      P S T\<close>
  shows \<open>P S T\<close>
  using assms(1) by (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T.induct)
  (auto intro: assms(2, 3, 4) elim!: learn\<^sub>N\<^sub>O\<^sub>TE forget\<^sub>N\<^sub>O\<^sub>TE)+

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_no_dup:
  assumes
    \<open>cdcl\<^sub>N\<^sub>O\<^sub>T S T\<close> and
    \<open>inv S\<close> and
    \<open>no_dup (trail S)\<close>
  shows \<open>no_dup (trail T)\<close>
  using assms by (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T_all_induct) (auto intro: dpll_bj_no_dup)

paragraph \<open>Consistency of the trail\<close>
lemma cdcl\<^sub>N\<^sub>O\<^sub>T_consistent:
  assumes
    \<open>cdcl\<^sub>N\<^sub>O\<^sub>T S T\<close> and
    \<open>inv S\<close> and
    \<open>no_dup (trail S)\<close>
  shows \<open>consistent_interp (lits_of_l (trail T))\<close>
  using cdcl\<^sub>N\<^sub>O\<^sub>T_no_dup[OF assms] distinct_consistent_interp by fast

text \<open>The subtle problem here is that tautologies can be removed, meaning that some variable can
  disappear of the problem. It is also means that some variable of the trail might not be present
  in the clauses anymore.\<close>
lemma cdcl\<^sub>N\<^sub>O\<^sub>T_atms_of_ms_clauses_decreasing:
  assumes \<open>cdcl\<^sub>N\<^sub>O\<^sub>T S T\<close>and \<open>inv S\<close>
  shows \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T T) \<subseteq> atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<union> atm_of ` (lits_of_l (trail S))\<close>
  using assms by (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T_all_induct)
    (auto dest!: dpll_bj_atms_of_ms_clauses_inv set_mp simp add: atms_of_ms_def Union_eq)

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_atms_in_trail:
  assumes \<open>cdcl\<^sub>N\<^sub>O\<^sub>T S T\<close>and \<open>inv S\<close>
  and \<open>atm_of ` (lits_of_l (trail S)) \<subseteq> atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S)\<close>
  shows \<open>atm_of ` (lits_of_l (trail T)) \<subseteq> atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S)\<close>
  using assms by (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T_all_induct) (auto simp add: dpll_bj_atms_in_trail)

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_atms_in_trail_in_set:
  assumes
    \<open>cdcl\<^sub>N\<^sub>O\<^sub>T S T\<close> and \<open>inv S\<close> and
    \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<subseteq> A\<close> and
    \<open>atm_of ` (lits_of_l (trail S)) \<subseteq> A\<close>
  shows \<open>atm_of ` (lits_of_l (trail T)) \<subseteq> A\<close>
  using assms
  by (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T_all_induct)
     (simp_all add: dpll_bj_atms_in_trail_in_set dpll_bj_atms_of_ms_clauses_inv)

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_all_decomposition_implies:
  assumes \<open>cdcl\<^sub>N\<^sub>O\<^sub>T S T\<close> and \<open>inv S\<close> and
    \<open>all_decomposition_implies_m (clauses\<^sub>N\<^sub>O\<^sub>T S) (get_all_ann_decomposition (trail S))\<close>
  shows
    \<open>all_decomposition_implies_m (clauses\<^sub>N\<^sub>O\<^sub>T T) (get_all_ann_decomposition (trail T))\<close>
  using assms(1,2,3)
proof (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T_all_induct)
  case dpll_bj
  then show ?case
     using dpll_bj_all_decomposition_implies_inv by blast
next
  case learn
  then show ?case by (auto simp add: all_decomposition_implies_def)
next
  case (forget\<^sub>N\<^sub>O\<^sub>T C T) note cls_C = this(1) and C = this(2) and T = this(3) and inv = this(4) and
    decomp = this(5)
  show ?case
    unfolding all_decomposition_implies_def Ball_def
    proof (intro allI, clarify)
      fix a b
      assume \<open>(a, b) \<in> set (get_all_ann_decomposition (trail T))\<close>
      then have \<open>unmark_l a \<union> set_mset (clauses\<^sub>N\<^sub>O\<^sub>T S) \<Turnstile>ps unmark_l b\<close>
        using decomp T by (auto simp add: all_decomposition_implies_def)
      moreover
        have a1:\<open>C \<in> set_mset (clauses\<^sub>N\<^sub>O\<^sub>T S)\<close>
          using C by blast
        have \<open>clauses\<^sub>N\<^sub>O\<^sub>T T = clauses\<^sub>N\<^sub>O\<^sub>T (remove_cls\<^sub>N\<^sub>O\<^sub>T C S)\<close>
         using T state_eq\<^sub>N\<^sub>O\<^sub>T_clauses by blast
        then have \<open>set_mset (clauses\<^sub>N\<^sub>O\<^sub>T T) \<Turnstile>ps set_mset (clauses\<^sub>N\<^sub>O\<^sub>T S)\<close>
          using a1 by (metis (no_types) clauses_remove_cls\<^sub>N\<^sub>O\<^sub>T cls_C insert_Diff order_refl
          set_mset_minus_replicate_mset(1) true_clss_clss_def true_clss_clss_insert)
      ultimately show \<open>unmark_l a \<union> set_mset (clauses\<^sub>N\<^sub>O\<^sub>T T)
        \<Turnstile>ps unmark_l b\<close>
        using true_clss_clss_generalise_true_clss_clss by blast
    qed
qed

paragraph \<open>Extension of models\<close>
lemma cdcl\<^sub>N\<^sub>O\<^sub>T_bj_sat_ext_iff:
  assumes \<open>cdcl\<^sub>N\<^sub>O\<^sub>T S T\<close>and \<open>inv S\<close>
  shows \<open>I\<Turnstile>sextm clauses\<^sub>N\<^sub>O\<^sub>T S \<longleftrightarrow> I\<Turnstile>sextm clauses\<^sub>N\<^sub>O\<^sub>T T\<close>
  using assms
proof (induction rule:cdcl\<^sub>N\<^sub>O\<^sub>T_all_induct)
  case dpll_bj
  then show ?case by (simp add: dpll_bj_clauses)
next
  case (learn C T) note T = this(3)
  { fix J
    assume
      \<open>I \<Turnstile>sextm clauses\<^sub>N\<^sub>O\<^sub>T S\<close> and
      \<open>I \<subseteq> J\<close> and
      tot: \<open>total_over_m J (set_mset (add_mset C (clauses\<^sub>N\<^sub>O\<^sub>T S)))\<close> and
      cons: \<open>consistent_interp J\<close>
    then have \<open>J \<Turnstile>sm clauses\<^sub>N\<^sub>O\<^sub>T S\<close> unfolding true_clss_ext_def by auto

    moreover
      with \<open>clauses\<^sub>N\<^sub>O\<^sub>T S\<Turnstile>pm C\<close> have \<open>J \<Turnstile> C\<close>
        using tot cons unfolding true_clss_cls_def by auto
    ultimately have \<open>J \<Turnstile>sm {#C#} + clauses\<^sub>N\<^sub>O\<^sub>T S\<close> by auto
  }
  then have H: \<open>I \<Turnstile>sextm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<Longrightarrow> I \<Turnstile>sext insert C (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T S))\<close>
    unfolding true_clss_ext_def by auto
  show ?case
    apply standard
      using T apply (auto simp add: H)[]
    using T apply simp
    by (metis Diff_insert_absorb insert_subset subsetI subset_antisym
      true_clss_ext_decrease_right_remove_r)
next
  case (forget\<^sub>N\<^sub>O\<^sub>T C T) note cls_C = this(1) and T = this(3)
  { fix J
    assume
      \<open>I \<Turnstile>sext set_mset (clauses\<^sub>N\<^sub>O\<^sub>T S) - {C}\<close> and
      \<open>I \<subseteq> J\<close> and
      tot: \<open>total_over_m J (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T S))\<close> and
      cons: \<open>consistent_interp J\<close>
    then have \<open>J \<Turnstile>s set_mset (clauses\<^sub>N\<^sub>O\<^sub>T S) - {C}\<close>
      unfolding true_clss_ext_def by (meson Diff_subset total_over_m_subset)

    moreover
      with cls_C have \<open>J \<Turnstile> C\<close>
        using tot cons unfolding true_clss_cls_def
        by (metis Un_commute forget\<^sub>N\<^sub>O\<^sub>T.hyps(2) insert_Diff insert_is_Un order_refl
          set_mset_minus_replicate_mset(1))
    ultimately have \<open>J \<Turnstile>sm (clauses\<^sub>N\<^sub>O\<^sub>T S)\<close> by (metis insert_Diff_single true_clss_insert)
  }
  then have H: \<open>I \<Turnstile>sext set_mset (clauses\<^sub>N\<^sub>O\<^sub>T S) - {C} \<Longrightarrow> I \<Turnstile>sextm (clauses\<^sub>N\<^sub>O\<^sub>T S)\<close>
    unfolding true_clss_ext_def by blast
  show ?case using T by (auto simp: true_clss_ext_decrease_right_remove_r H)
qed

end \<comment> \<open>End of the locale @{locale conflict_driven_clause_learning_ops}.\<close>

subsubsection \<open>CDCL with invariant\<close>
locale conflict_driven_clause_learning =
  conflict_driven_clause_learning_ops +
  assumes cdcl\<^sub>N\<^sub>O\<^sub>T_inv: \<open>\<And>S T. cdcl\<^sub>N\<^sub>O\<^sub>T S T \<Longrightarrow> inv S \<Longrightarrow> inv T\<close>
begin
sublocale dpll_with_backjumping
  apply unfold_locales
  using cdcl\<^sub>N\<^sub>O\<^sub>T.simps cdcl\<^sub>N\<^sub>O\<^sub>T_inv by auto

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_inv:
  \<open>cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T \<Longrightarrow> inv S \<Longrightarrow> inv T\<close>
  by (induction rule: rtranclp_induct) (auto simp add: cdcl\<^sub>N\<^sub>O\<^sub>T_inv)

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_no_dup:
  assumes \<open>cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T\<close> and \<open>inv S\<close>
  and \<open>no_dup (trail S)\<close>
  shows \<open>no_dup (trail T)\<close>
  using assms by (induction rule: rtranclp_induct) (auto intro: cdcl\<^sub>N\<^sub>O\<^sub>T_no_dup rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_inv)

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_trail_clauses_bound:
  assumes
    cdcl: \<open>cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T\<close> and
    inv: \<open>inv S\<close> and
    atms_clauses_S: \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<subseteq> A\<close> and
    atms_trail_S: \<open>atm_of `(lits_of_l (trail S)) \<subseteq> A\<close>
  shows \<open>atm_of ` (lits_of_l (trail T)) \<subseteq> A \<and> atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T T) \<subseteq> A\<close>
  using cdcl
proof (induction rule: rtranclp_induct)
  case base
  then show ?case using atms_clauses_S atms_trail_S by simp
next
  case (step T U) note st = this(1) and cdcl\<^sub>N\<^sub>O\<^sub>T = this(2) and IH = this(3)
  have \<open>inv T\<close> using inv st rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_inv by blast
   have \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T U) \<subseteq> A\<close>
    using cdcl\<^sub>N\<^sub>O\<^sub>T_atms_of_ms_clauses_decreasing[OF cdcl\<^sub>N\<^sub>O\<^sub>T] IH \<open>inv T\<close> by fast
  moreover
    have \<open>atm_of `(lits_of_l (trail U)) \<subseteq> A\<close>
      using cdcl\<^sub>N\<^sub>O\<^sub>T_atms_in_trail_in_set[OF cdcl\<^sub>N\<^sub>O\<^sub>T, of A]
      by (meson atms_trail_S atms_clauses_S IH \<open>inv T\<close> cdcl\<^sub>N\<^sub>O\<^sub>T )
  ultimately show ?case by fast
qed

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_all_decomposition_implies:
  assumes \<open>cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T\<close> and \<open>inv S\<close> and \<open>no_dup (trail S)\<close> and
    \<open>all_decomposition_implies_m (clauses\<^sub>N\<^sub>O\<^sub>T S) (get_all_ann_decomposition (trail S))\<close>
  shows
    \<open>all_decomposition_implies_m (clauses\<^sub>N\<^sub>O\<^sub>T T) (get_all_ann_decomposition (trail T))\<close>
  using assms by (induction)
  (auto intro: rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_inv cdcl\<^sub>N\<^sub>O\<^sub>T_all_decomposition_implies rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_no_dup)

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_bj_sat_ext_iff:
  assumes \<open>cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T\<close>and \<open>inv S\<close>
  shows \<open>I\<Turnstile>sextm clauses\<^sub>N\<^sub>O\<^sub>T S \<longleftrightarrow> I\<Turnstile>sextm clauses\<^sub>N\<^sub>O\<^sub>T T\<close>
  using assms apply (induction rule: rtranclp_induct)
  using cdcl\<^sub>N\<^sub>O\<^sub>T_bj_sat_ext_iff by (auto intro: rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_inv rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_no_dup)

definition cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv where
\<open>cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv A S \<longleftrightarrow> (finite A \<and> inv S \<and> atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<subseteq> atms_of_ms A
    \<and> atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A \<and> no_dup (trail S))\<close>

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv:
  assumes \<open>cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T\<close> and \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv A S\<close>
  shows \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv A T\<close>
  using assms unfolding cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv_def
  by (simp add: rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_inv rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_no_dup rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_trail_clauses_bound)

(* is the same as learn_and_forget\<^sub>N\<^sub>O\<^sub>T *)
abbreviation learn_or_forget where
\<open>learn_or_forget S T \<equiv> learn S T \<or> forget\<^sub>N\<^sub>O\<^sub>T S T\<close>

lemma rtranclp_learn_or_forget_cdcl\<^sub>N\<^sub>O\<^sub>T:
  \<open>learn_or_forget\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T\<close>
  using rtranclp_mono[of learn_or_forget cdcl\<^sub>N\<^sub>O\<^sub>T] by (blast intro: cdcl\<^sub>N\<^sub>O\<^sub>T.c_learn cdcl\<^sub>N\<^sub>O\<^sub>T.c_forget\<^sub>N\<^sub>O\<^sub>T)

lemma learn_or_forget_dpll_\<mu>\<^sub>C:
  assumes
    l_f: \<open>learn_or_forget\<^sup>*\<^sup>* S T\<close> and
    dpll: \<open>dpll_bj T U\<close> and
    inv: \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv A S\<close>
  shows \<open>(2+card (atms_of_ms A)) ^ (1+card (atms_of_ms A))
      - \<mu>\<^sub>C (1+card (atms_of_ms A)) (2+card (atms_of_ms A)) (trail_weight U)
    < (2+card (atms_of_ms A)) ^ (1+card (atms_of_ms A))
      - \<mu>\<^sub>C (1+card (atms_of_ms A)) (2+card (atms_of_ms A)) (trail_weight S)\<close>
     (is \<open>?\<mu> U < ?\<mu> S\<close>)
proof -
  have \<open>?\<mu> S = ?\<mu> T\<close>
    using l_f
    proof (induction)
      case base
      then show ?case by simp
    next
      case (step T U)
      moreover then have \<open>no_dup (trail T)\<close>
        using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_no_dup[of S T] cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv_def inv
        rtranclp_learn_or_forget_cdcl\<^sub>N\<^sub>O\<^sub>T by auto
      ultimately show ?case
        using forget_\<mu>\<^sub>C_stable learn_\<mu>\<^sub>C_stable inv unfolding cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv_def by presburger
    qed
  moreover have \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv A T\<close>
     using rtranclp_learn_or_forget_cdcl\<^sub>N\<^sub>O\<^sub>T cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv l_f inv by blast
  ultimately show ?thesis
    using dpll_bj_trail_mes_decreasing_prop[of T U A, OF dpll] finite
    unfolding cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv_def by presburger
qed

lemma infinite_cdcl\<^sub>N\<^sub>O\<^sub>T_exists_learn_and_forget_infinite_chain: (* \htmlink{infinite_cdcl_NOT_exists_learn_and_forget_infinite_chain} *)
  assumes
    \<open>\<And>i. cdcl\<^sub>N\<^sub>O\<^sub>T (f i) (f(Suc i))\<close> and
    inv: \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv A (f 0)\<close>
  shows \<open>\<exists>j. \<forall>i\<ge>j. learn_or_forget (f i) (f (Suc i))\<close>
  using assms
proof (induction \<open>(2+card (atms_of_ms A)) ^ (1+card (atms_of_ms A))
    - \<mu>\<^sub>C (1+card (atms_of_ms A)) (2+card (atms_of_ms A)) (trail_weight (f 0))\<close>
    arbitrary: f
    rule: nat_less_induct_case)
  case (Suc n) note IH = this(1) and \<mu> = this(2) and cdcl\<^sub>N\<^sub>O\<^sub>T = this(3) and inv = this(4)
  consider
    (dpll_end) \<open>\<exists>j. \<forall>i\<ge>j. learn_or_forget (f i) (f (Suc i))\<close>
    | (dpll_more) \<open>\<not>(\<exists>j. \<forall>i\<ge>j. learn_or_forget (f i) (f (Suc i)))\<close>
    by blast
  then show ?case
  proof cases
    case dpll_end
    then show ?thesis by auto
  next
    case dpll_more
    then have j: \<open>\<exists>i. \<not> learn (f i) (f (Suc i)) \<and> \<not>forget\<^sub>N\<^sub>O\<^sub>T (f i) (f (Suc i))\<close>
      by blast
    obtain i where
      i_learn_forget: \<open>\<not>learn (f i) (f (Suc i)) \<and> \<not>forget\<^sub>N\<^sub>O\<^sub>T (f i) (f (Suc i))\<close> and
      \<open>\<forall>k<i. learn_or_forget (f k) (f (Suc k))\<close>
    proof -
      obtain i\<^sub>0 where \<open>\<not> learn (f i\<^sub>0) (f (Suc i\<^sub>0)) \<and> \<not>forget\<^sub>N\<^sub>O\<^sub>T (f i\<^sub>0) (f (Suc i\<^sub>0))\<close>
        using j by auto
      then have \<open>{i. i\<le>i\<^sub>0 \<and> \<not> learn (f i) (f (Suc i)) \<and> \<not>forget\<^sub>N\<^sub>O\<^sub>T (f i) (f (Suc i))} \<noteq> {}\<close>
        by auto
      let ?I = \<open>{i. i\<le>i\<^sub>0 \<and> \<not> learn (f i) (f (Suc i)) \<and> \<not>forget\<^sub>N\<^sub>O\<^sub>T (f i) (f (Suc i))}\<close>
      let ?i = \<open>Min ?I\<close>
      have \<open>finite ?I\<close>
        by auto
      have \<open>\<not> learn (f ?i) (f (Suc ?i)) \<and> \<not>forget\<^sub>N\<^sub>O\<^sub>T (f ?i) (f (Suc ?i))\<close>
        using Min_in[OF \<open>finite ?I\<close> \<open>?I \<noteq> {}\<close>] by auto
      moreover have \<open>\<forall>k<?i. learn_or_forget (f k) (f (Suc k))\<close>
        using Min.coboundedI[of \<open>{i. i \<le> i\<^sub>0 \<and> \<not> learn (f i) (f (Suc i)) \<and> \<not> forget\<^sub>N\<^sub>O\<^sub>T (f i)
            (f (Suc i))}\<close>, simplified]
        by (meson \<open>\<not> learn (f i\<^sub>0) (f (Suc i\<^sub>0)) \<and> \<not> forget\<^sub>N\<^sub>O\<^sub>T (f i\<^sub>0) (f (Suc i\<^sub>0))\<close> less_imp_le
            dual_order.trans not_le)
      ultimately show ?thesis using that by blast
    qed
    define g where \<open>g = (\<lambda>n. f (n + Suc i))\<close>
    have \<open>dpll_bj (f i) (g 0)\<close>
      using i_learn_forget cdcl\<^sub>N\<^sub>O\<^sub>T cdcl\<^sub>N\<^sub>O\<^sub>T.cases unfolding g_def by auto
    {
      fix j
      assume \<open>j \<le> i\<close>
      then have \<open>learn_or_forget\<^sup>*\<^sup>* (f 0) (f j)\<close>
        apply (induction j)
         apply simp
        by (metis (no_types, lifting) Suc_leD Suc_le_lessD rtranclp.simps
            \<open>\<forall>k<i. learn (f k) (f (Suc k)) \<or> forget\<^sub>N\<^sub>O\<^sub>T (f k) (f (Suc k))\<close>)
    }
    then have \<open>learn_or_forget\<^sup>*\<^sup>* (f 0) (f i)\<close> by blast
    then have \<open>(2 + card (atms_of_ms A)) ^ (1 + card (atms_of_ms A))
      - \<mu>\<^sub>C (1 + card (atms_of_ms A)) (2 + card (atms_of_ms A)) (trail_weight (g 0))
      < (2 + card (atms_of_ms A)) ^ (1 + card (atms_of_ms A))
      - \<mu>\<^sub>C (1 + card (atms_of_ms A)) (2 + card (atms_of_ms A)) (trail_weight (f 0))\<close>
      using learn_or_forget_dpll_\<mu>\<^sub>C[of \<open>f 0\<close> \<open>f i\<close> \<open>g 0\<close> A] inv \<open>dpll_bj (f i) (g 0)\<close>
      unfolding cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv_def by linarith

    moreover have cdcl\<^sub>N\<^sub>O\<^sub>T_i: \<open>cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* (f 0) (g 0)\<close>
      using rtranclp_learn_or_forget_cdcl\<^sub>N\<^sub>O\<^sub>T[of \<open>f 0\<close> \<open>f i\<close>] \<open>learn_or_forget\<^sup>*\<^sup>* (f 0) (f i)\<close>
        cdcl\<^sub>N\<^sub>O\<^sub>T[of i] unfolding g_def by auto
    moreover have \<open>\<And>i. cdcl\<^sub>N\<^sub>O\<^sub>T (g i) (g (Suc i))\<close>
      using cdcl\<^sub>N\<^sub>O\<^sub>T g_def by auto
    moreover have \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv A (g 0)\<close>
      using inv cdcl\<^sub>N\<^sub>O\<^sub>T_i rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_trail_clauses_bound g_def cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv by auto
    ultimately obtain j where j: \<open>\<And>i. i\<ge>j \<Longrightarrow> learn_or_forget (g i) (g (Suc i))\<close>
      using IH unfolding \<mu>[symmetric] by presburger
    show ?thesis
    proof
      {
        fix k
        assume \<open>k \<ge> j + Suc i\<close>
        then have \<open>learn_or_forget (f k) (f (Suc k))\<close>
          using j[of \<open>k-Suc i\<close>] unfolding g_def by auto
      }
      then show \<open>\<forall>k\<ge>j+Suc i. learn_or_forget (f k) (f (Suc k))\<close>
        by auto
    qed
  qed
next
  case 0 note H = this(1) and cdcl\<^sub>N\<^sub>O\<^sub>T = this(2) and inv = this(3)
  show ?case
  proof (rule ccontr)
    assume \<open>\<not> ?case\<close>
    then have j: \<open>\<exists>i. \<not> learn (f i) (f (Suc i)) \<and> \<not>forget\<^sub>N\<^sub>O\<^sub>T (f i) (f (Suc i))\<close>
      by blast
    obtain i where
      \<open>\<not>learn (f i) (f (Suc i)) \<and> \<not>forget\<^sub>N\<^sub>O\<^sub>T (f i) (f (Suc i))\<close> and
      \<open>\<forall>k<i. learn_or_forget (f k) (f (Suc k))\<close>
    proof -
      obtain i\<^sub>0 where \<open>\<not> learn (f i\<^sub>0) (f (Suc i\<^sub>0)) \<and> \<not>forget\<^sub>N\<^sub>O\<^sub>T (f i\<^sub>0) (f (Suc i\<^sub>0))\<close>
        using j by auto
      then have \<open>{i. i\<le>i\<^sub>0 \<and> \<not> learn (f i) (f (Suc i)) \<and> \<not>forget\<^sub>N\<^sub>O\<^sub>T (f i) (f (Suc i))} \<noteq> {}\<close>
        by auto
      let ?I = \<open>{i. i\<le>i\<^sub>0 \<and> \<not> learn (f i) (f (Suc i)) \<and> \<not>forget\<^sub>N\<^sub>O\<^sub>T (f i) (f (Suc i))}\<close>
      let ?i = \<open>Min ?I\<close>
      have \<open>finite ?I\<close>
        by auto
      have \<open>\<not> learn (f ?i) (f (Suc ?i)) \<and> \<not>forget\<^sub>N\<^sub>O\<^sub>T (f ?i) (f (Suc ?i))\<close>
        using Min_in[OF \<open>finite ?I\<close> \<open>?I \<noteq> {}\<close>] by auto
      moreover have \<open>\<forall>k<?i. learn_or_forget (f k) (f (Suc k))\<close>
        using Min.coboundedI[of \<open>{i. i \<le> i\<^sub>0 \<and> \<not> learn (f i) (f (Suc i)) \<and> \<not> forget\<^sub>N\<^sub>O\<^sub>T (f i)
            (f (Suc i))}\<close>, simplified]
        by (meson \<open>\<not> learn (f i\<^sub>0) (f (Suc i\<^sub>0)) \<and> \<not> forget\<^sub>N\<^sub>O\<^sub>T (f i\<^sub>0) (f (Suc i\<^sub>0))\<close> less_imp_le
            dual_order.trans not_le)
      ultimately show ?thesis using that by blast
    qed
    have \<open>dpll_bj (f i) (f (Suc i))\<close>
      using \<open>\<not> learn (f i) (f (Suc i)) \<and> \<not> forget\<^sub>N\<^sub>O\<^sub>T (f i) (f (Suc i))\<close> cdcl\<^sub>N\<^sub>O\<^sub>T cdcl\<^sub>N\<^sub>O\<^sub>T.cases
      by blast
    {
      fix j
      assume \<open>j \<le> i\<close>
      then have \<open>learn_or_forget\<^sup>*\<^sup>* (f 0) (f j)\<close>
        apply (induction j)
         apply simp
        by (metis (no_types, lifting) Suc_leD Suc_le_lessD rtranclp.simps
            \<open>\<forall>k<i. learn (f k) (f (Suc k)) \<or> forget\<^sub>N\<^sub>O\<^sub>T (f k) (f (Suc k))\<close>)
    }
    then have \<open>learn_or_forget\<^sup>*\<^sup>* (f 0) (f i)\<close> by blast

    then show False
      using learn_or_forget_dpll_\<mu>\<^sub>C[of \<open>f 0\<close> \<open>f i\<close> \<open>f (Suc i)\<close> A] inv 0
        \<open>dpll_bj (f i) (f (Suc i))\<close> unfolding cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv_def by linarith
  qed
qed

lemma wf_cdcl\<^sub>N\<^sub>O\<^sub>T_no_learn_and_forget_infinite_chain:
  assumes
    no_infinite_lf: \<open>\<And>f j. \<not> (\<forall>i\<ge>j. learn_or_forget (f i) (f (Suc i)))\<close>
  shows \<open>wf {(T, S). cdcl\<^sub>N\<^sub>O\<^sub>T S T \<and> cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv A S}\<close>
    (is \<open>wf {(T, S). cdcl\<^sub>N\<^sub>O\<^sub>T S T \<and> ?inv S}\<close>)
  unfolding wf_iff_no_infinite_down_chain
proof (rule ccontr)
  assume \<open>\<not> \<not> (\<exists>f. \<forall>i. (f (Suc i), f i) \<in> {(T, S). cdcl\<^sub>N\<^sub>O\<^sub>T S T \<and> ?inv S})\<close>
  then obtain f where
    \<open>\<forall>i. cdcl\<^sub>N\<^sub>O\<^sub>T (f i) (f (Suc i)) \<and> ?inv (f i)\<close>
    by fast
  then have \<open>\<exists>j. \<forall>i\<ge>j. learn_or_forget (f i) (f (Suc i))\<close>
    using infinite_cdcl\<^sub>N\<^sub>O\<^sub>T_exists_learn_and_forget_infinite_chain[of f] by meson
  then show False using no_infinite_lf by blast
qed

lemma inv_and_tranclp_cdcl_\<^sub>N\<^sub>O\<^sub>T_tranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_and_inv:
  \<open>cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>+\<^sup>+ S T \<and> cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv A S \<longleftrightarrow> (\<lambda>S T. cdcl\<^sub>N\<^sub>O\<^sub>T S T \<and> cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv A S)\<^sup>+\<^sup>+ S T\<close>
  (is \<open>?A \<and> ?I \<longleftrightarrow> ?B\<close>)
proof
  assume \<open>?A \<and> ?I\<close>
  then have ?A and ?I by blast+
  then show ?B
    apply induction
      apply (simp add: tranclp.r_into_trancl)
    by (subst tranclp.simps) (auto intro: cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv tranclp_into_rtranclp)
next
  assume ?B
  then have ?A by induction auto
  moreover have ?I using \<open>?B\<close> tranclpD by fastforce
  ultimately show \<open>?A \<and> ?I\<close> by blast
qed

lemma wf_tranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_no_learn_and_forget_infinite_chain:
  assumes
    no_infinite_lf: \<open>\<And>f j. \<not> (\<forall>i\<ge>j. learn_or_forget (f i) (f (Suc i)))\<close>
  shows \<open>wf {(T, S). cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>+\<^sup>+ S T \<and> cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv A S}\<close>
  using wf_trancl[OF wf_cdcl\<^sub>N\<^sub>O\<^sub>T_no_learn_and_forget_infinite_chain[OF no_infinite_lf]]
  apply (rule wf_subset)
  by (auto simp: trancl_set_tranclp inv_and_tranclp_cdcl_\<^sub>N\<^sub>O\<^sub>T_tranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_and_inv)

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_final_state:
  assumes
    n_s: \<open>no_step cdcl\<^sub>N\<^sub>O\<^sub>T S\<close> and
    inv: \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv A S\<close> and
    decomp: \<open>all_decomposition_implies_m (clauses\<^sub>N\<^sub>O\<^sub>T S) (get_all_ann_decomposition (trail S))\<close>
  shows \<open>unsatisfiable (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T S))
    \<or> (trail S \<Turnstile>asm clauses\<^sub>N\<^sub>O\<^sub>T S \<and> satisfiable (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T S)))\<close>
proof -
  have n_s': \<open>no_step dpll_bj S\<close>
    using n_s by (auto simp: cdcl\<^sub>N\<^sub>O\<^sub>T.simps)
  show ?thesis
    apply (rule dpll_backjump_final_state[of S A])
    using inv decomp n_s' unfolding cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv_def by auto
qed

lemma full_cdcl\<^sub>N\<^sub>O\<^sub>T_final_state:
  assumes
    full: \<open>full cdcl\<^sub>N\<^sub>O\<^sub>T S T\<close> and
    inv: \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv A S\<close> and
    n_d: \<open>no_dup (trail S)\<close> and
    decomp: \<open>all_decomposition_implies_m (clauses\<^sub>N\<^sub>O\<^sub>T S) (get_all_ann_decomposition (trail S))\<close>
  shows \<open>unsatisfiable (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T T))
    \<or> (trail T \<Turnstile>asm clauses\<^sub>N\<^sub>O\<^sub>T T \<and> satisfiable (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T T)))\<close>
proof -
  have st: \<open>cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T\<close> and n_s: \<open>no_step cdcl\<^sub>N\<^sub>O\<^sub>T T\<close>
    using full unfolding full_def by blast+
  have n_s': \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv A T\<close>
    using cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv inv st by blast
  moreover have \<open>all_decomposition_implies_m (clauses\<^sub>N\<^sub>O\<^sub>T T) (get_all_ann_decomposition (trail T))\<close>
    using cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv_def decomp inv rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_all_decomposition_implies st by auto
  ultimately show ?thesis
    using cdcl\<^sub>N\<^sub>O\<^sub>T_final_state n_s by blast
qed

end \<comment> \<open>End of the locale @{locale conflict_driven_clause_learning}.\<close>


subsubsection \<open>Termination\<close>

text \<open>To prove termination we need to restrict learn and forget. Otherwise we could forget and
  relearn the exact same clause over and over. A first idea is to forbid removing clauses that
  can be used to backjump. This does not change the rules of the calculus. A second idea is to
  ``merge'' backjump and learn: that way, though closer to implementation, needs a change of the
  rules, since the backjump-rule learns the clause used to backjump.\<close>

subsubsection \<open>Restricting learn and forget\<close>

locale conflict_driven_clause_learning_learning_before_backjump_only_distinct_learnt =
  dpll_state trail clauses\<^sub>N\<^sub>O\<^sub>T prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T +
  conflict_driven_clause_learning trail clauses\<^sub>N\<^sub>O\<^sub>T prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T
    inv decide_conds backjump_conds propagate_conds
  \<open>\<lambda>C S. distinct_mset C \<and> \<not>tautology C \<and> learn_restrictions C S \<and>
    (\<exists>F K d F' C' L. trail S = F' @ Decided K # F \<and> C = add_mset L C' \<and> F \<Turnstile>as CNot C'
      \<and> add_mset L C' \<notin># clauses\<^sub>N\<^sub>O\<^sub>T S)\<close>
  \<open>\<lambda>C S. \<not>(\<exists>F' F K d L. trail S = F' @ Decided K # F \<and> F \<Turnstile>as CNot (remove1_mset L C))
    \<and> forget_restrictions C S\<close>
    for
    trail :: \<open>'st \<Rightarrow> ('v, unit) ann_lits\<close> and
    clauses\<^sub>N\<^sub>O\<^sub>T :: \<open>'st \<Rightarrow> 'v clauses\<close> and
    prepend_trail :: \<open>('v, unit) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    tl_trail :: \<open>'st \<Rightarrow>'st\<close> and
    add_cls\<^sub>N\<^sub>O\<^sub>T :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    remove_cls\<^sub>N\<^sub>O\<^sub>T :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    inv :: \<open>'st \<Rightarrow> bool\<close> and
    decide_conds :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> and
    backjump_conds :: \<open>'v clause \<Rightarrow> 'v clause \<Rightarrow> 'v literal \<Rightarrow> 'st \<Rightarrow> 'st \<Rightarrow> bool\<close> and
    propagate_conds :: \<open>('v, unit) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st \<Rightarrow> bool\<close> and
    learn_restrictions forget_restrictions :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> bool\<close>
begin

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_learn_all_induct[consumes 1, case_names dpll_bj learn forget\<^sub>N\<^sub>O\<^sub>T]:
  fixes S T :: \<open>'st\<close>
  assumes \<open>cdcl\<^sub>N\<^sub>O\<^sub>T S T\<close> and
    dpll: \<open>\<And>T. dpll_bj S T \<Longrightarrow> P S T\<close> and
    learning:
      \<open>\<And>C F K F' C' L T. clauses\<^sub>N\<^sub>O\<^sub>T S \<Turnstile>pm C \<Longrightarrow>
        atms_of C \<subseteq> atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<union> atm_of ` (lits_of_l (trail S)) \<Longrightarrow>
        distinct_mset C \<Longrightarrow>
        \<not> tautology C \<Longrightarrow>
        learn_restrictions C S \<Longrightarrow>
        trail S = F' @ Decided K # F \<Longrightarrow>
        C = add_mset L C' \<Longrightarrow>
        F \<Turnstile>as CNot C' \<Longrightarrow>
        add_mset L C' \<notin># clauses\<^sub>N\<^sub>O\<^sub>T S \<Longrightarrow>
        T \<sim> add_cls\<^sub>N\<^sub>O\<^sub>T C S \<Longrightarrow>
        P S T\<close> and
    forgetting: \<open>\<And>C T. removeAll_mset C (clauses\<^sub>N\<^sub>O\<^sub>T S) \<Turnstile>pm C \<Longrightarrow>
      C \<in># clauses\<^sub>N\<^sub>O\<^sub>T S \<Longrightarrow>
      \<not>(\<exists>F' F K L. trail S = F' @ Decided K # F \<and> F \<Turnstile>as CNot (C - {#L#})) \<Longrightarrow>
      T \<sim> remove_cls\<^sub>N\<^sub>O\<^sub>T C S \<Longrightarrow>
      forget_restrictions C S \<Longrightarrow>
      P S T\<close>
    shows \<open>P S T\<close>
  using assms(1)
  apply (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T.induct)
    apply (auto dest: assms(2) simp add: learn_ops_axioms)[]
   apply (auto elim!: learn_ops.learn.cases[OF learn_ops_axioms] dest: assms(3))[]
  apply (auto elim!: forget_ops.forget\<^sub>N\<^sub>O\<^sub>T.cases[OF forget_ops_axioms] dest!: assms(4))
  done

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_inv:
  \<open>cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T \<Longrightarrow> inv S \<Longrightarrow> inv T\<close>
  apply (induction rule: rtranclp_induct)
   apply simp
  using cdcl\<^sub>N\<^sub>O\<^sub>T_inv unfolding conflict_driven_clause_learning_def
  conflict_driven_clause_learning_axioms_def by blast

lemma learn_always_simple_clauses:
  assumes
    learn: \<open>learn S T\<close> and
    n_d: \<open>no_dup (trail S)\<close>
  shows \<open>set_mset (clauses\<^sub>N\<^sub>O\<^sub>T T - clauses\<^sub>N\<^sub>O\<^sub>T S)
    \<subseteq> simple_clss (atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<union> atm_of ` lits_of_l (trail S))\<close>
proof
  fix C assume C: \<open>C \<in> set_mset (clauses\<^sub>N\<^sub>O\<^sub>T T - clauses\<^sub>N\<^sub>O\<^sub>T S)\<close>
  have \<open>distinct_mset C\<close> \<open>\<not>tautology C\<close> using learn C n_d by (elim learn\<^sub>N\<^sub>O\<^sub>TE; auto)+
  then have \<open>C \<in> simple_clss (atms_of C)\<close>
    using distinct_mset_not_tautology_implies_in_simple_clss by blast
  moreover have \<open>atms_of C \<subseteq> atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<union> atm_of ` lits_of_l (trail S)\<close>
    using learn C n_d by (elim learn\<^sub>N\<^sub>O\<^sub>TE) (auto simp: atms_of_ms_def atms_of_def image_Un
      true_annots_CNot_all_atms_defined)
  moreover have \<open>finite (atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<union> atm_of ` lits_of_l (trail S))\<close>
     by auto
  ultimately show \<open>C \<in> simple_clss (atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<union> atm_of ` lits_of_l (trail S))\<close>
    using simple_clss_mono by (metis (no_types) insert_subset mk_disjoint_insert)
qed

definition \<open>conflicting_bj_clss S \<equiv>
   {C+{#L#} |C L. C+{#L#} \<in># clauses\<^sub>N\<^sub>O\<^sub>T S \<and> distinct_mset (C+{#L#})
   \<and> \<not>tautology (C+{#L#})
     \<and> (\<exists>F' K F. trail S = F' @ Decided K # F \<and> F \<Turnstile>as CNot C)}\<close>

lemma conflicting_bj_clss_remove_cls\<^sub>N\<^sub>O\<^sub>T[simp]:
  \<open>conflicting_bj_clss (remove_cls\<^sub>N\<^sub>O\<^sub>T C S) = conflicting_bj_clss S - {C}\<close>
  unfolding conflicting_bj_clss_def by fastforce

lemma conflicting_bj_clss_remove_cls\<^sub>N\<^sub>O\<^sub>T'[simp]:
  \<open>T \<sim> remove_cls\<^sub>N\<^sub>O\<^sub>T C S \<Longrightarrow> conflicting_bj_clss T = conflicting_bj_clss S - {C}\<close>
  unfolding conflicting_bj_clss_def by fastforce

lemma conflicting_bj_clss_add_cls\<^sub>N\<^sub>O\<^sub>T_state_eq:
  assumes
    T: \<open>T \<sim> add_cls\<^sub>N\<^sub>O\<^sub>T C' S\<close> and
    n_d: \<open>no_dup (trail S)\<close>
  shows \<open>conflicting_bj_clss T
    = conflicting_bj_clss S
      \<union> (if \<exists>C L. C' = add_mset L C \<and> distinct_mset (add_mset L C) \<and> \<not>tautology (add_mset L C)
     \<and> (\<exists>F' K d F. trail S = F' @ Decided K # F \<and> F \<Turnstile>as CNot C)
     then {C'} else {})\<close>
proof -
  define P where \<open>P = (\<lambda>C L T. distinct_mset (add_mset L C) \<and> \<not> tautology (add_mset L C) \<and>
    (\<exists>F' K F. trail T = F' @ Decided K # F \<and> F \<Turnstile>as CNot C))\<close>
  have conf: \<open>\<And>T. conflicting_bj_clss T = {add_mset L C |C L. add_mset L C \<in># clauses\<^sub>N\<^sub>O\<^sub>T T \<and> P C L T}\<close>
    unfolding conflicting_bj_clss_def P_def by auto
  have P_S_T: \<open>\<And>C L. P C L T = P C L S\<close>
    using T n_d unfolding P_def by auto
  have P: \<open>conflicting_bj_clss T = {add_mset L C |C L. add_mset L C \<in># clauses\<^sub>N\<^sub>O\<^sub>T S \<and> P C L T} \<union>
     {add_mset L C |C L. add_mset L C \<in># {#C'#} \<and> P C L T}\<close>
    using T n_d unfolding conf by auto
  moreover have \<open>{add_mset L C |C L. add_mset L C \<in># clauses\<^sub>N\<^sub>O\<^sub>T S \<and> P C L T} = conflicting_bj_clss S\<close>
    using T n_d unfolding P_def conflicting_bj_clss_def by auto
  moreover have \<open>{add_mset L C |C L. add_mset L C \<in># {#C'#} \<and> P C L T} =
    (if \<exists>C L. C' = add_mset L C \<and> P C L S then {C'} else {})\<close>
    using n_d T by (force simp: P_S_T)
  ultimately show ?thesis unfolding P_def by presburger
qed

lemma conflicting_bj_clss_add_cls\<^sub>N\<^sub>O\<^sub>T:
  \<open>no_dup (trail S) \<Longrightarrow>
  conflicting_bj_clss (add_cls\<^sub>N\<^sub>O\<^sub>T C' S)
    = conflicting_bj_clss S
      \<union> (if \<exists>C L. C' = C +{#L#}\<and> distinct_mset (C+{#L#}) \<and> \<not>tautology (C+{#L#})
     \<and> (\<exists>F' K d F. trail S = F' @ Decided K # F \<and> F \<Turnstile>as CNot C)
     then {C'} else {})\<close>
  using conflicting_bj_clss_add_cls\<^sub>N\<^sub>O\<^sub>T_state_eq by auto

lemma conflicting_bj_clss_incl_clauses:
   \<open>conflicting_bj_clss S \<subseteq> set_mset (clauses\<^sub>N\<^sub>O\<^sub>T S)\<close>
  unfolding conflicting_bj_clss_def by auto

lemma finite_conflicting_bj_clss[simp]:
  \<open>finite (conflicting_bj_clss S)\<close>
  using conflicting_bj_clss_incl_clauses[of S] rev_finite_subset by blast

lemma learn_conflicting_increasing:
  \<open>no_dup (trail S) \<Longrightarrow> learn S T \<Longrightarrow> conflicting_bj_clss S \<subseteq> conflicting_bj_clss T\<close>
  apply (elim learn\<^sub>N\<^sub>O\<^sub>TE)
  by (subst conflicting_bj_clss_add_cls\<^sub>N\<^sub>O\<^sub>T_state_eq[of T]) auto

abbreviation \<open>conflicting_bj_clss_yet b S \<equiv>
  3 ^ b - card (conflicting_bj_clss S)\<close>

abbreviation \<mu>\<^sub>L :: \<open>nat \<Rightarrow> 'st \<Rightarrow> nat \<times> nat\<close> where
  \<open>\<mu>\<^sub>L b S \<equiv> (conflicting_bj_clss_yet b S, card (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T S)))\<close>

lemma do_not_forget_before_backtrack_rule_clause_learned_clause_untouched:
  assumes \<open>forget\<^sub>N\<^sub>O\<^sub>T S T\<close>
  shows \<open>conflicting_bj_clss S = conflicting_bj_clss T\<close>
  using assms apply (elim forget\<^sub>N\<^sub>O\<^sub>TE)
  apply rule
   apply (subst conflicting_bj_clss_remove_cls\<^sub>N\<^sub>O\<^sub>T'[of T], simp)
   apply (fastforce simp: conflicting_bj_clss_def remove1_mset_add_mset_If split: if_splits)
  apply fastforce
  done

lemma forget_\<mu>\<^sub>L_decrease:
  assumes forget\<^sub>N\<^sub>O\<^sub>T: \<open>forget\<^sub>N\<^sub>O\<^sub>T S T\<close>
  shows \<open>(\<mu>\<^sub>L b T, \<mu>\<^sub>L b S) \<in> less_than <*lex*> less_than\<close>
proof -
  have \<open>card (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T S)) > 0\<close>
    using forget\<^sub>N\<^sub>O\<^sub>T by (elim forget\<^sub>N\<^sub>O\<^sub>TE) (auto simp: size_mset_removeAll_mset_le_iff card_gt_0_iff)
  then have \<open>card (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T T)) < card (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T S))\<close>
    using forget\<^sub>N\<^sub>O\<^sub>T by (elim forget\<^sub>N\<^sub>O\<^sub>TE) (auto simp: size_mset_removeAll_mset_le_iff)
  then show ?thesis
    unfolding do_not_forget_before_backtrack_rule_clause_learned_clause_untouched[OF forget\<^sub>N\<^sub>O\<^sub>T]
    by auto
qed

lemma set_condition_or_split:
   \<open>{a. (a = b \<or> Q a) \<and> S a} = (if S b then {b} else {}) \<union> {a. Q a \<and> S a}\<close>
  by auto

lemma set_insert_neq:
  \<open>A \<noteq> insert a A \<longleftrightarrow> a \<notin> A\<close>
  by auto

lemma learn_\<mu>\<^sub>L_decrease:
  assumes learnST: \<open>learn S T\<close> and n_d: \<open>no_dup (trail S)\<close> and
   A: \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<union> atm_of ` lits_of_l (trail S) \<subseteq> A\<close> and
   fin_A: \<open>finite A\<close>
  shows \<open>(\<mu>\<^sub>L (card A) T, \<mu>\<^sub>L (card A) S) \<in> less_than <*lex*> less_than\<close>
proof -
  have [simp]: \<open>(atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T T) \<union> atm_of ` lits_of_l (trail T))
    = (atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<union> atm_of ` lits_of_l (trail S))\<close>
    using learnST n_d by (elim learn\<^sub>N\<^sub>O\<^sub>TE) auto

  then have \<open>card (atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T T) \<union> atm_of ` lits_of_l (trail T))
    = card (atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<union> atm_of ` lits_of_l (trail S))\<close>
    by (auto intro!: card_mono)
  then have 3: \<open>(3::nat) ^ card (atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T T) \<union> atm_of ` lits_of_l (trail T))
    = 3 ^ card (atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<union> atm_of ` lits_of_l (trail S))\<close>
    by (auto intro: power_mono)
  moreover have \<open>conflicting_bj_clss S \<subseteq> conflicting_bj_clss T\<close>
    using learnST n_d by (simp add: learn_conflicting_increasing)
  moreover have \<open>conflicting_bj_clss S \<noteq> conflicting_bj_clss T\<close>
    using learnST
    proof (elim learn\<^sub>N\<^sub>O\<^sub>TE, goal_cases)
      case (1 C) note clss_S = this(1) and atms_C = this(2) and inv = this(3) and T = this(4)
      then obtain F K F' C' L where
        tr_S: \<open>trail S = F' @ Decided K # F\<close> and
        C: \<open>C = add_mset L C'\<close> and
        F: \<open>F \<Turnstile>as CNot C'\<close> and
        C_S:\<open>add_mset L C' \<notin># clauses\<^sub>N\<^sub>O\<^sub>T S\<close>
        by blast
      moreover have \<open>distinct_mset C\<close> \<open>\<not> tautology C\<close> using inv by blast+
      ultimately have \<open>add_mset L C' \<in> conflicting_bj_clss T\<close>
        using T n_d unfolding conflicting_bj_clss_def by fastforce
      moreover have \<open>add_mset L C' \<notin> conflicting_bj_clss S\<close>
        using C_S unfolding conflicting_bj_clss_def by auto
      ultimately show ?case by blast
    qed
  moreover have fin_T: \<open>finite (conflicting_bj_clss T)\<close>
    using learnST by induction (auto simp add: conflicting_bj_clss_add_cls\<^sub>N\<^sub>O\<^sub>T )
  ultimately have \<open>card (conflicting_bj_clss T) \<ge> card (conflicting_bj_clss S)\<close>
    using card_mono by blast

  moreover
    have fin': \<open>finite (atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T T) \<union> atm_of ` lits_of_l (trail T))\<close>
      by auto
    have 1:\<open>atms_of_ms (conflicting_bj_clss T) \<subseteq> atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T T)\<close>
      unfolding conflicting_bj_clss_def atms_of_ms_def by auto
    have 2: \<open>\<And>x. x\<in> conflicting_bj_clss T \<Longrightarrow> \<not> tautology x \<and> distinct_mset x\<close>
      unfolding conflicting_bj_clss_def by auto
    have T: \<open>conflicting_bj_clss T
    \<subseteq> simple_clss (atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T T) \<union> atm_of ` lits_of_l (trail T))\<close>
      by standard (meson 1 2 fin' \<open>finite (conflicting_bj_clss T)\<close> simple_clss_mono
        distinct_mset_set_def simplified_in_simple_clss subsetCE sup.coboundedI1)
  moreover
    then have #: \<open>3 ^ card (atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T T) \<union> atm_of ` lits_of_l (trail T))
        \<ge> card (conflicting_bj_clss T)\<close>
      by (meson Nat.le_trans simple_clss_card simple_clss_finite card_mono fin')
    have \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T T) \<union> atm_of ` lits_of_l (trail T) \<subseteq> A\<close>
      using learn\<^sub>N\<^sub>O\<^sub>TE[OF learnST] A by simp
    then have \<open>3 ^ (card A) \<ge> card (conflicting_bj_clss T)\<close>
      using # fin_A by (meson simple_clss_card simple_clss_finite
        simple_clss_mono calculation(2) card_mono dual_order.trans)
  ultimately show ?thesis
    using psubset_card_mono[OF fin_T ]
    unfolding less_than_iff lex_prod_def by clarify
      (meson \<open>conflicting_bj_clss S \<noteq> conflicting_bj_clss T\<close>
        \<open>conflicting_bj_clss S \<subseteq> conflicting_bj_clss T\<close>
        diff_less_mono2 le_less_trans not_le psubsetI)
qed

text \<open>We have to assume the following:
  \<^item> @{term \<open>inv S\<close>}: the invariant holds in the inital state.
  \<^item> @{term A} is a (finite @{term \<open>finite A\<close>}) superset of the literals in the trail
  @{term \<open>atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A\<close>}
  and in the clauses @{term \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<subseteq> atms_of_ms A\<close>}. This can the the set of all
  the literals in the starting set of clauses.
  \<^item> @{term \<open>no_dup (trail S)\<close>}: no duplicate in the trail. This is invariant along the path.\<close>
definition \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L where
\<open>\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L A T \<equiv> ((2+card (atms_of_ms A)) ^ (1+card (atms_of_ms A))
               - \<mu>\<^sub>C (1+card (atms_of_ms A)) (2+card (atms_of_ms A)) (trail_weight T),
            conflicting_bj_clss_yet (card (atms_of_ms A)) T, card (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T T)))\<close>
lemma cdcl\<^sub>N\<^sub>O\<^sub>T_decreasing_measure:
  assumes
    \<open>cdcl\<^sub>N\<^sub>O\<^sub>T S T\<close> and
    inv: \<open>inv S\<close> and
    atm_clss: \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<subseteq> atms_of_ms A\<close> and
    atm_lits: \<open>atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A\<close> and
    n_d: \<open>no_dup (trail S)\<close> and
    fin_A: \<open>finite A\<close>
  shows \<open>(\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L A T, \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L A S)
            \<in> less_than <*lex*> (less_than <*lex*> less_than)\<close>
  using assms(1)
proof induction
  case (c_dpll_bj T)
  from dpll_bj_trail_mes_decreasing_prop[OF this(1) inv atm_clss atm_lits n_d fin_A]
  show ?case unfolding \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L_def
    by (meson in_lex_prod less_than_iff)
next
  case (c_learn T) note learn = this(1)
  then have S: \<open>trail S = trail T\<close>
    using inv atm_clss atm_lits n_d fin_A
    by (elim learn\<^sub>N\<^sub>O\<^sub>TE) auto
  show ?case
    using learn_\<mu>\<^sub>L_decrease[OF learn n_d, of \<open>atms_of_ms A\<close>] atm_clss atm_lits fin_A n_d
    unfolding S \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L_def by auto
next
  case (c_forget\<^sub>N\<^sub>O\<^sub>T T) note forget\<^sub>N\<^sub>O\<^sub>T = this(1)
  have \<open>trail S = trail T\<close> using forget\<^sub>N\<^sub>O\<^sub>T by induction auto
  then show ?case
    using forget_\<mu>\<^sub>L_decrease[OF forget\<^sub>N\<^sub>O\<^sub>T] unfolding \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L_def by auto
qed

lemma wf_cdcl\<^sub>N\<^sub>O\<^sub>T_restricted_learning:
  assumes \<open>finite A\<close>
  shows \<open>wf {(T, S).
    (atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<subseteq> atms_of_ms A \<and> atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A
    \<and> no_dup (trail S)
    \<and> inv S)
    \<and> cdcl\<^sub>N\<^sub>O\<^sub>T S T }\<close>
  by (rule wf_wf_if_measure'[of \<open>less_than <*lex*> (less_than <*lex*> less_than)\<close>])
     (auto intro: cdcl\<^sub>N\<^sub>O\<^sub>T_decreasing_measure[OF _ _ _ _ _ assms])

definition \<mu>\<^sub>C' :: \<open>'v clause set \<Rightarrow> 'st \<Rightarrow> nat\<close> where
\<open>\<mu>\<^sub>C' A T \<equiv> \<mu>\<^sub>C (1+card (atms_of_ms A)) (2+card (atms_of_ms A)) (trail_weight T)\<close>

definition \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L' :: \<open>'v clause set \<Rightarrow> 'st \<Rightarrow> nat\<close> where
\<open>\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L' A T \<equiv>
  ((2+card (atms_of_ms A)) ^ (1+card (atms_of_ms A)) - \<mu>\<^sub>C' A T) * (1+ 3^card (atms_of_ms A)) * 2
  + conflicting_bj_clss_yet (card (atms_of_ms A)) T * 2
  + card (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T T))\<close>

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_decreasing_measure':
  assumes
    \<open>cdcl\<^sub>N\<^sub>O\<^sub>T S T\<close> and
    inv: \<open>inv S\<close> and
    atms_clss: \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<subseteq> atms_of_ms A\<close> and
    atms_trail: \<open>atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A\<close> and
    n_d: \<open>no_dup (trail S)\<close> and
    fin_A: \<open>finite A\<close>
  shows \<open>\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L' A T < \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L' A S\<close>
  using assms(1)
proof (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T_learn_all_induct)
  case (dpll_bj T)
  then have \<open>(2+card (atms_of_ms A)) ^ (1+card (atms_of_ms A)) - \<mu>\<^sub>C' A T
    < (2+card (atms_of_ms A)) ^ (1+card (atms_of_ms A)) - \<mu>\<^sub>C' A S\<close>
    using dpll_bj_trail_mes_decreasing_prop fin_A inv n_d atms_clss atms_trail
    unfolding \<mu>\<^sub>C'_def by blast
  then have XX: \<open>((2+card (atms_of_ms A)) ^ (1+card (atms_of_ms A)) - \<mu>\<^sub>C' A T) + 1
    \<le> (2+card (atms_of_ms A)) ^ (1+card (atms_of_ms A)) - \<mu>\<^sub>C' A S\<close>
    by auto
  from mult_le_mono1[OF this, of \<open>1 + 3 ^ card (atms_of_ms A)\<close>]
  have \<open>((2 + card (atms_of_ms A)) ^ (1 + card (atms_of_ms A)) - \<mu>\<^sub>C' A T) *
      (1 + 3 ^ card (atms_of_ms A)) + (1 + 3 ^ card (atms_of_ms A))
    \<le> ((2 + card (atms_of_ms A)) ^ (1 + card (atms_of_ms A)) - \<mu>\<^sub>C' A S)
      * (1 + 3 ^ card (atms_of_ms A))\<close>
    unfolding Nat.add_mult_distrib
    by presburger
  moreover
    have cl_T_S: \<open>clauses\<^sub>N\<^sub>O\<^sub>T T = clauses\<^sub>N\<^sub>O\<^sub>T S\<close>
      using dpll_bj.hyps inv dpll_bj_clauses by auto
    have \<open>conflicting_bj_clss_yet (card (atms_of_ms A)) S < 1+ 3 ^ card (atms_of_ms A)\<close>
    by simp
  ultimately have \<open>((2 + card (atms_of_ms A)) ^ (1 + card (atms_of_ms A)) - \<mu>\<^sub>C' A T)
      * (1 + 3 ^ card (atms_of_ms A)) + conflicting_bj_clss_yet (card (atms_of_ms A)) T
    < ((2 + card (atms_of_ms A)) ^ (1 + card (atms_of_ms A)) - \<mu>\<^sub>C' A S) *(1 + 3 ^ card (atms_of_ms A))\<close>
    by linarith
  then have \<open>((2 + card (atms_of_ms A)) ^ (1 + card (atms_of_ms A)) - \<mu>\<^sub>C' A T)
        * (1 + 3 ^ card (atms_of_ms A))
      + conflicting_bj_clss_yet (card (atms_of_ms A)) T
    < ((2 + card (atms_of_ms A)) ^ (1 + card (atms_of_ms A)) - \<mu>\<^sub>C' A S)
        * (1 + 3 ^ card (atms_of_ms A))
      + conflicting_bj_clss_yet (card (atms_of_ms A)) S\<close>
    by linarith
  then have \<open>((2 + card (atms_of_ms A)) ^ (1 + card (atms_of_ms A)) - \<mu>\<^sub>C' A T)
      * (1 + 3 ^ card (atms_of_ms A)) * 2
    + conflicting_bj_clss_yet (card (atms_of_ms A)) T * 2
    < ((2 + card (atms_of_ms A)) ^ (1 + card (atms_of_ms A)) - \<mu>\<^sub>C' A S)
      * (1 + 3 ^ card (atms_of_ms A)) * 2
    + conflicting_bj_clss_yet (card (atms_of_ms A)) S * 2\<close>
    by linarith
  then show ?case unfolding \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_def cl_T_S by presburger
next
  case (learn C F' K F C' L T) note clss_S_C = this(1) and atms_C = this(2) and dist = this(3)
    and tauto = this(4) and learn_restr = this(5) and tr_S = this(6) and C' = this(7) and
    F_C = this(8) and C_new = this(9) and T = this(10)
  have \<open>insert C (conflicting_bj_clss S) \<subseteq> simple_clss (atms_of_ms A)\<close>
    proof -
      have \<open>C \<in> simple_clss (atms_of_ms A)\<close>
        using C'
        by (metis (no_types, hide_lams) Un_subset_iff simple_clss_mono
          contra_subsetD dist distinct_mset_not_tautology_implies_in_simple_clss
          dual_order.trans atms_C atms_clss atms_trail tauto)
      moreover have \<open>conflicting_bj_clss S \<subseteq> simple_clss (atms_of_ms A)\<close>
        proof
          fix x :: \<open>'v clause\<close>
          assume \<open>x \<in> conflicting_bj_clss S\<close>
          then have \<open>x \<in># clauses\<^sub>N\<^sub>O\<^sub>T S \<and> distinct_mset x \<and> \<not> tautology x\<close>
            unfolding conflicting_bj_clss_def by blast
          then show \<open>x \<in> simple_clss (atms_of_ms A)\<close>
            by (meson atms_clss atms_of_atms_of_ms_mono atms_of_ms_finite simple_clss_mono
              distinct_mset_not_tautology_implies_in_simple_clss fin_A finite_subset
              set_rev_mp)
        qed
      ultimately show ?thesis
        by auto
    qed
  then have \<open>card (insert C (conflicting_bj_clss S)) \<le> 3 ^ (card (atms_of_ms A))\<close>
    by (meson Nat.le_trans atms_of_ms_finite simple_clss_card simple_clss_finite
      card_mono fin_A)
  moreover have [simp]: \<open>card (insert C (conflicting_bj_clss S))
    = Suc (card ((conflicting_bj_clss S)))\<close>
    by (metis (no_types) C' C_new card_insert_if conflicting_bj_clss_incl_clauses contra_subsetD
      finite_conflicting_bj_clss)
  moreover have [simp]: \<open>conflicting_bj_clss (add_cls\<^sub>N\<^sub>O\<^sub>T C S) = conflicting_bj_clss S \<union> {C}\<close>
    using dist tauto F_C by (subst conflicting_bj_clss_add_cls\<^sub>N\<^sub>O\<^sub>T[OF n_d]) (force simp: C' tr_S n_d)
  ultimately have [simp]: \<open>conflicting_bj_clss_yet (card (atms_of_ms A)) S
    = Suc (conflicting_bj_clss_yet (card (atms_of_ms A)) (add_cls\<^sub>N\<^sub>O\<^sub>T C S))\<close>
      by simp
  have 1: \<open>clauses\<^sub>N\<^sub>O\<^sub>T T = clauses\<^sub>N\<^sub>O\<^sub>T (add_cls\<^sub>N\<^sub>O\<^sub>T C S)\<close> using T by auto
  have 2: \<open>conflicting_bj_clss_yet (card (atms_of_ms A)) T
    = conflicting_bj_clss_yet (card (atms_of_ms A)) (add_cls\<^sub>N\<^sub>O\<^sub>T C S)\<close>
    using T unfolding conflicting_bj_clss_def by auto
  have 3: \<open>\<mu>\<^sub>C' A T = \<mu>\<^sub>C' A (add_cls\<^sub>N\<^sub>O\<^sub>T C S)\<close>
    using T unfolding \<mu>\<^sub>C'_def by auto
  have \<open>((2 + card (atms_of_ms A)) ^ (1 + card (atms_of_ms A)) - \<mu>\<^sub>C' A (add_cls\<^sub>N\<^sub>O\<^sub>T C S))
    * (1 + 3 ^ card (atms_of_ms A)) * 2
    = ((2 + card (atms_of_ms A)) ^ (1 + card (atms_of_ms A)) - \<mu>\<^sub>C' A S)
    * (1 + 3 ^ card (atms_of_ms A)) * 2\<close>
      using n_d unfolding \<mu>\<^sub>C'_def by auto
  moreover
    have \<open>conflicting_bj_clss_yet (card (atms_of_ms A)) (add_cls\<^sub>N\<^sub>O\<^sub>T C S)
        * 2
      + card (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T (add_cls\<^sub>N\<^sub>O\<^sub>T C S)))
      < conflicting_bj_clss_yet (card (atms_of_ms A)) S * 2
      + card (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T S))\<close>
      by (simp add: C' C_new n_d)
  ultimately show ?case unfolding \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_def 1 2 3 by presburger
next
  case (forget\<^sub>N\<^sub>O\<^sub>T C T) note T = this(4)
  have [simp]: \<open>\<mu>\<^sub>C' A (remove_cls\<^sub>N\<^sub>O\<^sub>T C S) = \<mu>\<^sub>C' A S\<close>
    unfolding \<mu>\<^sub>C'_def by auto
  have \<open>forget\<^sub>N\<^sub>O\<^sub>T S T\<close>
    apply (rule forget\<^sub>N\<^sub>O\<^sub>T.intros) using forget\<^sub>N\<^sub>O\<^sub>T by auto
  then have \<open>conflicting_bj_clss T = conflicting_bj_clss S\<close>
    using do_not_forget_before_backtrack_rule_clause_learned_clause_untouched by blast
  moreover have \<open>card (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T T)) < card (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T S))\<close>
    by (metis T card_Diff1_less clauses_remove_cls\<^sub>N\<^sub>O\<^sub>T finite_set_mset forget\<^sub>N\<^sub>O\<^sub>T.hyps(2)
      order_refl set_mset_minus_replicate_mset(1) state_eq\<^sub>N\<^sub>O\<^sub>T_clauses)
  ultimately show ?case unfolding \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_def
    using T \<open>\<mu>\<^sub>C' A (remove_cls\<^sub>N\<^sub>O\<^sub>T C S) = \<mu>\<^sub>C' A S\<close> by (metis (no_types) add_le_cancel_left
      \<mu>\<^sub>C'_def not_le state_eq\<^sub>N\<^sub>O\<^sub>T_trail)
qed

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_clauses_bound:
  assumes
    \<open>cdcl\<^sub>N\<^sub>O\<^sub>T S T\<close> and
    \<open>inv S\<close> and
    \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<subseteq> A\<close> and
    \<open>atm_of `(lits_of_l (trail S)) \<subseteq> A\<close> and
    n_d: \<open>no_dup (trail S)\<close> and
    fin_A[simp]: \<open>finite A\<close>
  shows \<open>set_mset (clauses\<^sub>N\<^sub>O\<^sub>T T) \<subseteq> set_mset (clauses\<^sub>N\<^sub>O\<^sub>T S) \<union> simple_clss A\<close>
  using assms
proof (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T_learn_all_induct)
  case dpll_bj
  then show ?case using dpll_bj_clauses by simp
next
  case forget\<^sub>N\<^sub>O\<^sub>T
  then show ?case using clauses_remove_cls\<^sub>N\<^sub>O\<^sub>T unfolding state_eq\<^sub>N\<^sub>O\<^sub>T_def by auto
next
  case (learn C F K d F' C' L) note atms_C = this(2) and dist = this(3) and tauto = this(4) and
  T = this(10) and atms_clss_S = this(12) and atms_trail_S = this(13)
  have \<open>atms_of C \<subseteq> A\<close>
    using atms_C atms_clss_S atms_trail_S by fast
  then have \<open>simple_clss (atms_of C) \<subseteq> simple_clss A\<close>
    by (simp add: simple_clss_mono)
  then have \<open>C \<in> simple_clss A\<close>
    using finite dist tauto by (auto dest: distinct_mset_not_tautology_implies_in_simple_clss)
  then show ?case using T n_d by auto
qed

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_clauses_bound:
  assumes
    \<open>cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T\<close> and
    \<open>inv S\<close> and
    \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<subseteq> A\<close> and
    \<open>atm_of `(lits_of_l (trail S)) \<subseteq> A\<close> and
    n_d: \<open>no_dup (trail S)\<close> and
    finite: \<open>finite A\<close>
  shows \<open>set_mset (clauses\<^sub>N\<^sub>O\<^sub>T T) \<subseteq> set_mset (clauses\<^sub>N\<^sub>O\<^sub>T S) \<union> simple_clss A\<close>
  using assms(1-5)
proof induction
  case base
  then show ?case by simp
next
  case (step T U) note st = this(1) and cdcl\<^sub>N\<^sub>O\<^sub>T = this(2) and IH = this(3)[OF this(4-7)] and
    inv = this(4) and atms_clss_S = this(5) and atms_trail_S = this(6) and finite_cls_S = this(7)
  have \<open>inv T\<close>
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_inv st inv by blast
  moreover have \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T T) \<subseteq> A\<close> and \<open>atm_of ` lits_of_l (trail T) \<subseteq> A\<close>
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_trail_clauses_bound[OF st] inv atms_clss_S atms_trail_S n_d by auto
  moreover have \<open>no_dup (trail T)\<close>
   using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_no_dup[OF st \<open>inv S\<close> n_d] by simp
  ultimately have \<open>set_mset (clauses\<^sub>N\<^sub>O\<^sub>T U) \<subseteq> set_mset (clauses\<^sub>N\<^sub>O\<^sub>T T) \<union> simple_clss A\<close>
    using cdcl\<^sub>N\<^sub>O\<^sub>T finite n_d by (auto simp: cdcl\<^sub>N\<^sub>O\<^sub>T_clauses_bound)
  then show ?case using IH by auto
qed

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_card_clauses_bound:
  assumes
    \<open>cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T\<close> and
    \<open>inv S\<close> and
    \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<subseteq> A\<close> and
    \<open>atm_of `(lits_of_l (trail S)) \<subseteq> A\<close> and
    n_d: \<open>no_dup (trail S)\<close> and
    finite: \<open>finite A\<close>
  shows \<open>card (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T T)) \<le> card (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T S)) + 3 ^ (card A)\<close>
  using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_clauses_bound[OF assms] finite by (meson Nat.le_trans
    simple_clss_card simple_clss_finite card_Un_le card_mono finite_UnI
    finite_set_mset nat_add_left_cancel_le)

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_card_clauses_bound':
  assumes
    \<open>cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T\<close> and
    \<open>inv S\<close> and
    \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<subseteq> A\<close> and
    \<open>atm_of `(lits_of_l (trail S)) \<subseteq> A\<close> and
    n_d: \<open>no_dup (trail S)\<close> and
    finite: \<open>finite A\<close>
  shows \<open>card {C|C. C \<in># clauses\<^sub>N\<^sub>O\<^sub>T T \<and> (tautology C \<or> \<not>distinct_mset C)}
    \<le> card {C|C. C\<in># clauses\<^sub>N\<^sub>O\<^sub>T S \<and> (tautology C \<or> \<not>distinct_mset C)} + 3 ^ (card A)\<close>
    (is \<open>card ?T \<le> card ?S + _\<close>)
  using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_clauses_bound[OF assms] finite
proof -
  have \<open>?T \<subseteq> ?S \<union> simple_clss A\<close>
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_clauses_bound[OF assms] by force
  then have \<open>card ?T \<le> card (?S \<union> simple_clss A)\<close>
    using finite by (simp add: assms(5) simple_clss_finite card_mono)
  then show ?thesis
    by (meson le_trans simple_clss_card card_Un_le local.finite nat_add_left_cancel_le)
qed

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_card_simple_clauses_bound:
  assumes
    \<open>cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T\<close> and
    \<open>inv S\<close> and
    NA: \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<subseteq> A\<close> and
    MA: \<open>atm_of ` (lits_of_l (trail S)) \<subseteq> A\<close> and
    n_d: \<open>no_dup (trail S)\<close> and
    finite: \<open>finite A\<close>
  shows \<open>card (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T T))
  \<le> card {C. C \<in># clauses\<^sub>N\<^sub>O\<^sub>T S \<and> (tautology C \<or> \<not>distinct_mset C)} + 3 ^ (card A)\<close>
    (is \<open>card ?T \<le> card ?S + _\<close>)
  using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_clauses_bound[OF assms] finite
proof -
  have \<open>\<And>x. x \<in># clauses\<^sub>N\<^sub>O\<^sub>T T \<Longrightarrow> \<not> tautology x \<Longrightarrow> distinct_mset x \<Longrightarrow> x \<in> simple_clss A\<close>
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_clauses_bound[OF assms] by (metis (no_types, hide_lams) Un_iff NA
      atms_of_atms_of_ms_mono simple_clss_mono contra_subsetD subset_trans
      distinct_mset_not_tautology_implies_in_simple_clss)
  then have \<open>set_mset (clauses\<^sub>N\<^sub>O\<^sub>T T) \<subseteq> ?S \<union> simple_clss A\<close>
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_clauses_bound[OF assms] by auto
  then have \<open>card(set_mset (clauses\<^sub>N\<^sub>O\<^sub>T T)) \<le> card (?S \<union> simple_clss A)\<close>
    using finite by (simp add: assms(5) simple_clss_finite card_mono)
  then show ?thesis
    by (meson le_trans simple_clss_card card_Un_le local.finite nat_add_left_cancel_le)
qed

definition \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound :: \<open>'v clause set \<Rightarrow> 'st \<Rightarrow> nat\<close> where
\<open>\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound A S =
  ((2 + card (atms_of_ms A)) ^ (1 + card (atms_of_ms A))) * (1 + 3 ^ card (atms_of_ms A)) * 2
     + 2*3 ^ (card (atms_of_ms A))
     + card {C. C \<in># clauses\<^sub>N\<^sub>O\<^sub>T S \<and> (tautology C \<or> \<not>distinct_mset C)} + 3 ^ (card (atms_of_ms A))\<close>

lemma \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound_reduce_trail_to\<^sub>N\<^sub>O\<^sub>T[simp]:
  \<open>\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound A (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T M S) = \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound A S\<close>
  unfolding \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound_def by auto

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound_reduce_trail_to\<^sub>N\<^sub>O\<^sub>T:
  assumes
    \<open>cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T\<close> and
    \<open>inv S\<close> and
    \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<subseteq> atms_of_ms A\<close> and
    \<open>atm_of `(lits_of_l (trail S)) \<subseteq> atms_of_ms A\<close> and
    n_d: \<open>no_dup (trail S)\<close> and
    finite: \<open>finite (atms_of_ms A)\<close> and
    U: \<open>U \<sim> reduce_trail_to\<^sub>N\<^sub>O\<^sub>T M T\<close>
  shows \<open>\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L' A U \<le> \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound A S\<close>
proof -
  have \<open> ((2 + card (atms_of_ms A)) ^ (1 + card (atms_of_ms A)) - \<mu>\<^sub>C' A U)
    \<le> (2 + card (atms_of_ms A)) ^ (1 + card (atms_of_ms A))\<close>
    by auto
  then have \<open>((2 + card (atms_of_ms A)) ^ (1 + card (atms_of_ms A)) - \<mu>\<^sub>C' A U)
        * (1 + 3 ^ card (atms_of_ms A)) * 2
    \<le> (2 + card (atms_of_ms A)) ^ (1 + card (atms_of_ms A)) * (1 + 3 ^ card (atms_of_ms A)) * 2\<close>
    using mult_le_mono1 by blast
  moreover
    have \<open>conflicting_bj_clss_yet (card (atms_of_ms A)) T * 2 \<le> 2 * 3 ^ card (atms_of_ms A)\<close>
      by linarith
  moreover have \<open>card (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T U))
      \<le> card {C. C \<in># clauses\<^sub>N\<^sub>O\<^sub>T S \<and> (tautology C \<or> \<not>distinct_mset C)} + 3 ^ card (atms_of_ms A)\<close>
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_card_simple_clauses_bound[OF assms(1-6)] U by auto
  ultimately show ?thesis
    unfolding \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_def \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound_def by linarith
qed

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound:
  assumes
    \<open>cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T\<close> and
    \<open>inv S\<close> and
    \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<subseteq> atms_of_ms A\<close> and
    \<open>atm_of `(lits_of_l (trail S)) \<subseteq> atms_of_ms A\<close> and
    n_d: \<open>no_dup (trail S)\<close> and
    finite: \<open>finite (atms_of_ms A)\<close>
  shows \<open>\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L' A T \<le> \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound A S\<close>
proof -
  have \<open>\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L' A (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T (trail T) T) = \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L' A T\<close>
    unfolding \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_def \<mu>\<^sub>C'_def conflicting_bj_clss_def by auto
  then show ?thesis using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound_reduce_trail_to\<^sub>N\<^sub>O\<^sub>T[OF assms, of _ \<open>trail T\<close>]
    state_eq\<^sub>N\<^sub>O\<^sub>T_ref by fastforce
qed

lemma rtranclp_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound_decreasing:
  assumes
    \<open>cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T\<close> and
    \<open>inv S\<close> and
    \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<subseteq> atms_of_ms A\<close> and
    \<open>atm_of `(lits_of_l (trail S)) \<subseteq> atms_of_ms A\<close> and
    n_d: \<open>no_dup (trail S)\<close> and
    finite[simp]: \<open>finite (atms_of_ms A)\<close>
  shows \<open>\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound A T \<le> \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound A S\<close>
proof -
  have \<open>{C. C \<in># clauses\<^sub>N\<^sub>O\<^sub>T T \<and> (tautology C \<or> \<not> distinct_mset C)}
    \<subseteq> {C. C \<in># clauses\<^sub>N\<^sub>O\<^sub>T S \<and> (tautology C \<or> \<not> distinct_mset C)}\<close> (is \<open>?T \<subseteq> ?S\<close>)
    proof (rule Set.subsetI)
      fix C assume \<open>C \<in> ?T\<close>
      then have C_T: \<open>C \<in># clauses\<^sub>N\<^sub>O\<^sub>T T\<close> and t_d: \<open>tautology C \<or> \<not> distinct_mset C\<close>
        by auto
      then have \<open>C \<notin> simple_clss (atms_of_ms A)\<close>
        by (auto dest: simple_clssE)
      then show \<open>C \<in> ?S\<close>
        using C_T rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_clauses_bound[OF assms] t_d by force
    qed
  then have \<open>card {C. C \<in># clauses\<^sub>N\<^sub>O\<^sub>T T \<and> (tautology C \<or> \<not> distinct_mset C)} \<le>
    card {C. C \<in># clauses\<^sub>N\<^sub>O\<^sub>T S \<and> (tautology C \<or> \<not> distinct_mset C)}\<close>
    by (simp add: card_mono)
  then show ?thesis
    unfolding \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound_def by auto
qed

end \<comment> \<open>End of the locale @{locale conflict_driven_clause_learning_learning_before_backjump_only_distinct_learnt}.\<close>


subsection \<open>CDCL with Restarts\<close>

subsubsection\<open>Definition\<close>

locale restart_ops =
  fixes
    cdcl\<^sub>N\<^sub>O\<^sub>T :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> and
    restart :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close>
begin
inductive cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> where
\<open>cdcl\<^sub>N\<^sub>O\<^sub>T S T \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart S T\<close> |
\<open>restart S T \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart S T\<close>

end

locale conflict_driven_clause_learning_with_restarts =
  conflict_driven_clause_learning trail clauses\<^sub>N\<^sub>O\<^sub>T prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T
    inv decide_conds backjump_conds propagate_conds learn_conds forget_conds
  for
    trail :: \<open>'st \<Rightarrow> ('v, unit) ann_lits\<close> and
    clauses\<^sub>N\<^sub>O\<^sub>T :: \<open>'st \<Rightarrow> 'v clauses\<close> and
    prepend_trail :: \<open>('v, unit) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    tl_trail :: \<open>'st \<Rightarrow>'st\<close> and
    add_cls\<^sub>N\<^sub>O\<^sub>T :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    remove_cls\<^sub>N\<^sub>O\<^sub>T :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    inv :: \<open>'st \<Rightarrow> bool\<close> and
    decide_conds :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> and
    backjump_conds :: \<open>'v clause \<Rightarrow> 'v clause \<Rightarrow> 'v literal \<Rightarrow> 'st \<Rightarrow> 'st \<Rightarrow> bool\<close> and
    propagate_conds :: \<open>('v, unit) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st \<Rightarrow> bool\<close> and
    learn_conds forget_conds :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> bool\<close>
begin

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_iff_cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart_no_restarts:
  \<open>cdcl\<^sub>N\<^sub>O\<^sub>T S T \<longleftrightarrow> restart_ops.cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart cdcl\<^sub>N\<^sub>O\<^sub>T (\<lambda>_ _. False) S T\<close>
  (is \<open>?C S T \<longleftrightarrow> ?R S T\<close>)
proof
  fix S T
  assume \<open>?C S T\<close>
  then show \<open>?R S T\<close> by (simp add: restart_ops.cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart.intros(1))
next
  fix S T
  assume \<open>?R S T\<close>
  then show \<open>?C S T\<close>
    apply (cases rule: restart_ops.cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart.cases)
    using \<open>?R S T\<close> by fast+
qed

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart:
  \<open>cdcl\<^sub>N\<^sub>O\<^sub>T S T \<Longrightarrow> restart_ops.cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart cdcl\<^sub>N\<^sub>O\<^sub>T restart S T\<close>
  by (simp add: restart_ops.cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart.intros(1))
end


subsubsection \<open>Increasing restarts\<close>

paragraph \<open>Definition\<close>

text \<open>
  We define our increasing restart very abstractly: the predicate (called @{term cdcl\<^sub>N\<^sub>O\<^sub>T}) does not
  have to be a CDCL calculus. We just need some assuptions to prove termination:
  \<^item> a function @{term f} that is strictly monotonic. The first step is actually only used as a
  restart to clean the state (e.g. to ensure that the trail is empty). Then we assume that
  @{term \<open>f n \<ge> 1\<close>} for @{term \<open>n \<ge> 1\<close>}: it means that between two consecutive
  restarts, at least one step will be done. This is necessary to avoid sequence. like: full --
  restart -- full -- ...
  \<^item> a measure @{term \<mu>}: it should decrease under the assumptions @{term bound_inv}, whenever a
  @{term cdcl\<^sub>N\<^sub>O\<^sub>T} or a @{term restart} is done. A parameter is given to @{term \<mu>}: for conflict-
  driven clause learning, it is an upper-bound of the clauses. We are assuming that such a bound
  can be found after a restart whenever the invariant holds.
  \<^item> we also assume that the measure decrease after any @{term cdcl\<^sub>N\<^sub>O\<^sub>T} step.
  \<^item> an invariant on the states @{term cdcl\<^sub>N\<^sub>O\<^sub>T_inv} that also holds after restarts.
  \<^item> it is \<^emph>\<open>not required\<close> that the measure decrease with respect to restarts, but the measure has to
  be bound by some function @{term \<mu>_bound} taking the same parameter as @{term \<mu>} and the initial
  state of the considered @{term cdcl\<^sub>N\<^sub>O\<^sub>T} chain.\<close>
locale cdcl\<^sub>N\<^sub>O\<^sub>T_increasing_restarts_ops =
  restart_ops cdcl\<^sub>N\<^sub>O\<^sub>T restart for
    restart :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> and
    cdcl\<^sub>N\<^sub>O\<^sub>T :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> +
  fixes
    f :: \<open>nat \<Rightarrow> nat\<close> and
    bound_inv :: \<open>'bound \<Rightarrow> 'st \<Rightarrow> bool\<close> and
    \<mu> :: \<open>'bound \<Rightarrow> 'st \<Rightarrow> nat\<close> and
    cdcl\<^sub>N\<^sub>O\<^sub>T_inv :: \<open>'st \<Rightarrow> bool\<close> and
    \<mu>_bound :: \<open>'bound \<Rightarrow> 'st \<Rightarrow> nat\<close>
  assumes
    f: \<open>unbounded f\<close> and
    f_ge_1: \<open>\<And>n. n\<ge>1 \<Longrightarrow> f n \<noteq> 0\<close> and
    bound_inv: \<open>\<And>A S T. cdcl\<^sub>N\<^sub>O\<^sub>T_inv S \<Longrightarrow> bound_inv A S \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T S T \<Longrightarrow> bound_inv A T\<close> and
    cdcl\<^sub>N\<^sub>O\<^sub>T_measure: \<open>\<And>A S T. cdcl\<^sub>N\<^sub>O\<^sub>T_inv S \<Longrightarrow> bound_inv A S \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T S T \<Longrightarrow> \<mu> A T < \<mu> A S\<close> and
    measure_bound2: \<open>\<And>A T U. cdcl\<^sub>N\<^sub>O\<^sub>T_inv T \<Longrightarrow> bound_inv A T \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* T U
       \<Longrightarrow> \<mu> A U \<le> \<mu>_bound A T\<close> and
    measure_bound4: \<open>\<And>A T U. cdcl\<^sub>N\<^sub>O\<^sub>T_inv T \<Longrightarrow> bound_inv A T \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* T U
       \<Longrightarrow> \<mu>_bound A U \<le> \<mu>_bound A T\<close> and
    cdcl\<^sub>N\<^sub>O\<^sub>T_restart_inv: \<open>\<And>A U V. cdcl\<^sub>N\<^sub>O\<^sub>T_inv U \<Longrightarrow> restart U V \<Longrightarrow> bound_inv A U \<Longrightarrow> bound_inv A V\<close>
      and
    exists_bound: \<open>\<And>R S. cdcl\<^sub>N\<^sub>O\<^sub>T_inv R \<Longrightarrow> restart R S \<Longrightarrow> \<exists>A. bound_inv A S\<close> and
    cdcl\<^sub>N\<^sub>O\<^sub>T_inv: \<open>\<And>S T. cdcl\<^sub>N\<^sub>O\<^sub>T_inv S \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T S T \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T_inv T\<close> and
    cdcl\<^sub>N\<^sub>O\<^sub>T_inv_restart: \<open>\<And>S T. cdcl\<^sub>N\<^sub>O\<^sub>T_inv S \<Longrightarrow> restart S T \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T_inv T\<close>
begin

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_cdcl\<^sub>N\<^sub>O\<^sub>T_inv:
  assumes
    \<open>(cdcl\<^sub>N\<^sub>O\<^sub>T^^n) S T\<close> and
    \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_inv S\<close>
  shows \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_inv T\<close>
  using assms by (induction n arbitrary: T) (auto intro:bound_inv cdcl\<^sub>N\<^sub>O\<^sub>T_inv)

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_bound_inv:
  assumes
    \<open>(cdcl\<^sub>N\<^sub>O\<^sub>T^^n) S T\<close> and
    \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_inv S\<close>
    \<open>bound_inv A S\<close>
  shows \<open>bound_inv A T\<close>
  using assms by (induction n arbitrary: T) (auto intro:bound_inv cdcl\<^sub>N\<^sub>O\<^sub>T_cdcl\<^sub>N\<^sub>O\<^sub>T_inv)

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_cdcl\<^sub>N\<^sub>O\<^sub>T_inv:
  assumes
    \<open>cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T\<close> and
    \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_inv S\<close>
  shows \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_inv T\<close>
  using assms by induction (auto intro: cdcl\<^sub>N\<^sub>O\<^sub>T_inv)

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_bound_inv:
  assumes
    \<open>cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T\<close> and
    \<open>bound_inv A S\<close> and
    \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_inv S\<close>
  shows \<open>bound_inv A T\<close>
  using assms by induction (auto intro:bound_inv rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_cdcl\<^sub>N\<^sub>O\<^sub>T_inv)

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_comp_n_le:
  assumes
    \<open>(cdcl\<^sub>N\<^sub>O\<^sub>T^^(Suc n)) S T\<close> and
    \<open>bound_inv A S\<close>
    \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_inv S\<close>
  shows \<open>\<mu> A T < \<mu> A S - n\<close>
  using assms
proof (induction n arbitrary: T)
  case 0
  then show ?case using cdcl\<^sub>N\<^sub>O\<^sub>T_measure by auto
next
  case (Suc n) note IH = this(1)[OF _ this(3) this(4)] and S_T = this(2) and b_inv = this(3) and
  c_inv = this(4)
  obtain U :: 'st where S_U: \<open>(cdcl\<^sub>N\<^sub>O\<^sub>T^^(Suc n)) S U\<close> and U_T: \<open>cdcl\<^sub>N\<^sub>O\<^sub>T U T\<close> using S_T by auto
  then have \<open>\<mu> A U < \<mu> A S - n\<close> using IH[of U] by simp
  moreover
    have \<open>bound_inv A U\<close>
      using S_U b_inv cdcl\<^sub>N\<^sub>O\<^sub>T_bound_inv c_inv by blast
    then have \<open>\<mu> A T < \<mu> A U\<close> using cdcl\<^sub>N\<^sub>O\<^sub>T_measure[OF _ _ U_T] S_U c_inv cdcl\<^sub>N\<^sub>O\<^sub>T_cdcl\<^sub>N\<^sub>O\<^sub>T_inv by auto
  ultimately show ?case by linarith
qed

lemma wf_cdcl\<^sub>N\<^sub>O\<^sub>T:
  \<open>wf {(T, S). cdcl\<^sub>N\<^sub>O\<^sub>T S T \<and> cdcl\<^sub>N\<^sub>O\<^sub>T_inv S \<and> bound_inv A S}\<close> (is \<open>wf ?A\<close>)
  apply (rule wfP_if_measure2[of _ _ \<open>\<mu> A\<close>])
  using cdcl\<^sub>N\<^sub>O\<^sub>T_comp_n_le[of 0 _ _ A] by auto

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_measure:
  assumes
    \<open>cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T\<close> and
    \<open>bound_inv A S\<close> and
    \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_inv S\<close>
  shows \<open>\<mu> A T \<le> \<mu> A S\<close>
  using assms
proof (induction rule: rtranclp_induct)
  case base
  then show ?case by auto
next
  case (step T U) note IH = this(3)[OF this(4) this(5)] and st = this(1) and cdcl\<^sub>N\<^sub>O\<^sub>T = this(2) and
    b_inv = this(4) and c_inv = this(5)
  have \<open>bound_inv A T\<close>
    by (meson cdcl\<^sub>N\<^sub>O\<^sub>T_bound_inv rtranclp_imp_relpowp st step.prems)
  moreover have \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_inv T\<close>
    using c_inv rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_cdcl\<^sub>N\<^sub>O\<^sub>T_inv st by blast
  ultimately have \<open>\<mu> A U < \<mu> A T\<close> using cdcl\<^sub>N\<^sub>O\<^sub>T_measure[OF _ _ cdcl\<^sub>N\<^sub>O\<^sub>T] by auto
  then show ?case using IH by linarith
qed

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_comp_bounded:
  assumes
    \<open>bound_inv A S\<close> and \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_inv S\<close> and \<open>m \<ge> 1+\<mu> A S\<close>
  shows \<open>\<not>(cdcl\<^sub>N\<^sub>O\<^sub>T ^^ m) S T\<close>
  using assms cdcl\<^sub>N\<^sub>O\<^sub>T_comp_n_le[of \<open>m-1\<close> S T A] by fastforce

text \<open>
  \<^item> @{term \<open>m > f n\<close>} ensures that at least one step has been done.\<close>
inductive cdcl\<^sub>N\<^sub>O\<^sub>T_restart where
restart_step: \<open>(cdcl\<^sub>N\<^sub>O\<^sub>T^^m) S T \<Longrightarrow> m \<ge> f n \<Longrightarrow> restart T U
  \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T_restart (S, n) (U, Suc n)\<close> |
restart_full: \<open>full1 cdcl\<^sub>N\<^sub>O\<^sub>T S T \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T_restart (S, n) (T, Suc n)\<close>

lemmas cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_induct = cdcl\<^sub>N\<^sub>O\<^sub>T_restart.induct[split_format(complete),
  OF cdcl\<^sub>N\<^sub>O\<^sub>T_increasing_restarts_ops_axioms]

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_restart_cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart:
  \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_restart S T \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart\<^sup>*\<^sup>* (fst S) (fst T)\<close>
proof (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T_restart.induct)
  case (restart_step m S T n U)
  then have \<open>cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T\<close> by (meson relpowp_imp_rtranclp)
  then have \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart\<^sup>*\<^sup>* S T\<close> using cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart.intros(1)
    rtranclp_mono[of cdcl\<^sub>N\<^sub>O\<^sub>T cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart] by blast
  moreover have \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart T U\<close>
    using \<open>restart T U\<close> cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart.intros(2) by blast
  ultimately show ?case by auto
next
  case (restart_full S T)
  then have \<open>cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T\<close> unfolding full1_def by auto
  then show ?case using cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart.intros(1)
    rtranclp_mono[of cdcl\<^sub>N\<^sub>O\<^sub>T cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart] by auto
qed

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_bound_inv:
  assumes
    \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_restart S T\<close> and
    \<open>bound_inv A (fst S)\<close> and
    \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_inv (fst S)\<close>
  shows \<open>bound_inv A (fst T)\<close>
  using assms apply (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T_restart.induct)
    prefer 2 apply (metis rtranclp_unfold fstI full1_def rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_bound_inv)
  by (metis cdcl\<^sub>N\<^sub>O\<^sub>T_bound_inv cdcl\<^sub>N\<^sub>O\<^sub>T_cdcl\<^sub>N\<^sub>O\<^sub>T_inv cdcl\<^sub>N\<^sub>O\<^sub>T_restart_inv fst_conv)

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_cdcl\<^sub>N\<^sub>O\<^sub>T_inv:
  assumes
    \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_restart S T\<close> and
    \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_inv (fst S)\<close>
  shows \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_inv (fst T)\<close>
  using assms apply induction
    apply (metis cdcl\<^sub>N\<^sub>O\<^sub>T_cdcl\<^sub>N\<^sub>O\<^sub>T_inv cdcl\<^sub>N\<^sub>O\<^sub>T_inv_restart fst_conv)
   apply (metis fstI full_def full_unfold rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_cdcl\<^sub>N\<^sub>O\<^sub>T_inv)
  done

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_cdcl\<^sub>N\<^sub>O\<^sub>T_inv:
  assumes
    \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_restart\<^sup>*\<^sup>* S T\<close> and
    \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_inv (fst S)\<close>
  shows \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_inv (fst T)\<close>
  using assms by induction (auto intro: cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_cdcl\<^sub>N\<^sub>O\<^sub>T_inv)

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_bound_inv:
  assumes
    \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_restart\<^sup>*\<^sup>* S T\<close> and
    \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_inv (fst S)\<close> and
    \<open>bound_inv A (fst S)\<close>
  shows \<open>bound_inv A (fst T)\<close>
  using assms apply induction
   apply (simp add: cdcl\<^sub>N\<^sub>O\<^sub>T_cdcl\<^sub>N\<^sub>O\<^sub>T_inv cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_bound_inv)
  using cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_bound_inv rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_cdcl\<^sub>N\<^sub>O\<^sub>T_inv by blast

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_increasing_number:
  \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_restart S T \<Longrightarrow> snd T = 1 + snd S\<close>
  by (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T_restart.induct) auto
end

locale cdcl\<^sub>N\<^sub>O\<^sub>T_increasing_restarts =
  cdcl\<^sub>N\<^sub>O\<^sub>T_increasing_restarts_ops restart cdcl\<^sub>N\<^sub>O\<^sub>T f bound_inv \<mu> cdcl\<^sub>N\<^sub>O\<^sub>T_inv \<mu>_bound +
  dpll_state trail clauses\<^sub>N\<^sub>O\<^sub>T prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T
  for
    trail :: \<open>'st \<Rightarrow> ('v, unit) ann_lits\<close> and
    clauses\<^sub>N\<^sub>O\<^sub>T :: \<open>'st \<Rightarrow> 'v clauses\<close> and
    prepend_trail :: \<open>('v, unit) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    tl_trail :: \<open>'st \<Rightarrow>'st\<close> and
    add_cls\<^sub>N\<^sub>O\<^sub>T :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    remove_cls\<^sub>N\<^sub>O\<^sub>T :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    f :: \<open>nat \<Rightarrow> nat\<close> and
    restart :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> and
    bound_inv :: \<open>'bound \<Rightarrow> 'st \<Rightarrow> bool\<close> and
    \<mu> :: \<open>'bound \<Rightarrow> 'st \<Rightarrow> nat\<close> and
    cdcl\<^sub>N\<^sub>O\<^sub>T :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> and
    cdcl\<^sub>N\<^sub>O\<^sub>T_inv :: \<open>'st \<Rightarrow> bool\<close> and
    \<mu>_bound :: \<open>'bound \<Rightarrow> 'st \<Rightarrow> nat\<close> +
  assumes
    measure_bound: \<open>\<And>A T V n. cdcl\<^sub>N\<^sub>O\<^sub>T_inv T \<Longrightarrow> bound_inv A T
      \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T_restart (T, n) (V, Suc n) \<Longrightarrow> \<mu> A V \<le> \<mu>_bound A T\<close> and
    cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart_\<mu>_bound:
      \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_restart (T, a) (V, b) \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T_inv T \<Longrightarrow> bound_inv A T
        \<Longrightarrow> \<mu>_bound A V \<le> \<mu>_bound A T\<close>
begin

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart_\<mu>_bound:
  \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_restart\<^sup>*\<^sup>* (T, a) (V, b) \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T_inv T \<Longrightarrow> bound_inv A T
    \<Longrightarrow> \<mu>_bound A V \<le> \<mu>_bound A T\<close>
  apply (induction rule: rtranclp_induct2)
   apply simp
  by (metis cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart_\<mu>_bound dual_order.trans fst_conv
    rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_bound_inv rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_cdcl\<^sub>N\<^sub>O\<^sub>T_inv)

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart_measure_bound:
  \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_restart (T, a) (V, b) \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T_inv T \<Longrightarrow> bound_inv A T
    \<Longrightarrow> \<mu> A V \<le> \<mu>_bound A T\<close>
  apply (cases rule: cdcl\<^sub>N\<^sub>O\<^sub>T_restart.cases)
     apply simp
    using measure_bound relpowp_imp_rtranclp apply fastforce
   by (metis full_def full_unfold measure_bound2 prod.inject)

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart_measure_bound:
  \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_restart\<^sup>*\<^sup>* (T, a) (V, b) \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T_inv T \<Longrightarrow> bound_inv A T
    \<Longrightarrow> \<mu> A V \<le> \<mu>_bound A T\<close>
  apply (induction rule: rtranclp_induct2)
    apply (simp add: measure_bound2)
  by (metis dual_order.trans fst_conv measure_bound2 r_into_rtranclp rtranclp.rtrancl_refl
    rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_bound_inv rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_cdcl\<^sub>N\<^sub>O\<^sub>T_inv
    rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart_\<mu>_bound)

lemma wf_cdcl\<^sub>N\<^sub>O\<^sub>T_restart:
  \<open>wf {(T, S). cdcl\<^sub>N\<^sub>O\<^sub>T_restart S T \<and> cdcl\<^sub>N\<^sub>O\<^sub>T_inv (fst S)}\<close> (is \<open>wf ?A\<close>)
proof (rule ccontr)
  assume \<open>\<not> ?thesis\<close>
  then obtain g where
    g: \<open>\<And>i. cdcl\<^sub>N\<^sub>O\<^sub>T_restart (g i) (g (Suc i))\<close> and
    cdcl\<^sub>N\<^sub>O\<^sub>T_inv_g: \<open>\<And>i. cdcl\<^sub>N\<^sub>O\<^sub>T_inv (fst (g i))\<close>
    unfolding wf_iff_no_infinite_down_chain by fast

  have snd_g: \<open>\<And>i. snd (g i) = i + snd (g 0)\<close>
    apply (induct_tac i)
      apply simp
      by (metis Suc_eq_plus1_left add.commute add.left_commute
        cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_increasing_number g)
  then have snd_g_0: \<open>\<And>i. i > 0 \<Longrightarrow> snd (g i) = i + snd (g 0)\<close>
    by blast
  have unbounded_f_g: \<open>unbounded (\<lambda>i. f (snd (g i)))\<close>
    using f unfolding bounded_def by (metis add.commute f less_or_eq_imp_le snd_g
      not_bounded_nat_exists_larger not_le le_iff_add)

  { fix i
    have H: \<open>\<And>T Ta m. (cdcl\<^sub>N\<^sub>O\<^sub>T ^^ m) T Ta \<Longrightarrow> no_step cdcl\<^sub>N\<^sub>O\<^sub>T T \<Longrightarrow> m = 0\<close>
      apply (case_tac m) by simp (meson relpowp_E2)
    have \<open>\<exists> T m. (cdcl\<^sub>N\<^sub>O\<^sub>T ^^ m) (fst (g i)) T \<and> m \<ge> f (snd (g i))\<close>
      using g[of i] apply (cases rule: cdcl\<^sub>N\<^sub>O\<^sub>T_restart.cases)
        apply auto[]
      using g[of \<open>Suc i\<close>] f_ge_1 apply (cases rule: cdcl\<^sub>N\<^sub>O\<^sub>T_restart.cases)
      apply (auto simp add: full1_def full_def dest: H dest: tranclpD)
      using H Suc_leI leD by blast
  } note H = this
  obtain A where \<open>bound_inv A (fst (g 1))\<close>
    using g[of 0] cdcl\<^sub>N\<^sub>O\<^sub>T_inv_g[of 0] apply (cases rule: cdcl\<^sub>N\<^sub>O\<^sub>T_restart.cases)
      apply (metis One_nat_def cdcl\<^sub>N\<^sub>O\<^sub>T_inv exists_bound fst_conv relpowp_imp_rtranclp
        rtranclp_induct)
      using H[of 1] unfolding full1_def by (metis One_nat_def Suc_eq_plus1 diff_is_0_eq' diff_zero
        f_ge_1 fst_conv le_add2 relpowp_E2 snd_conv)
  let ?j = \<open>\<mu>_bound A (fst (g 1)) + 1\<close>
  obtain j where
    j: \<open>f (snd (g j)) > ?j\<close> and \<open>j > 1\<close>
    using unbounded_f_g not_bounded_nat_exists_larger by blast
  {
     fix i j
     have cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart: \<open>j \<ge> i \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T_restart\<^sup>*\<^sup>* (g i) (g j)\<close>
       apply (induction j)
         apply simp
       by (metis g le_Suc_eq rtranclp.rtrancl_into_rtrancl rtranclp.rtrancl_refl)
  } note cdcl\<^sub>N\<^sub>O\<^sub>T_restart = this
  have \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_inv (fst (g (Suc 0)))\<close>
    by (simp add: cdcl\<^sub>N\<^sub>O\<^sub>T_inv_g)
  have \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_restart\<^sup>*\<^sup>* (fst (g 1), snd (g 1)) (fst (g j), snd (g j))\<close>
    using \<open>j> 1\<close> by (simp add: cdcl\<^sub>N\<^sub>O\<^sub>T_restart)
  have \<open>\<mu> A (fst (g j)) \<le> \<mu>_bound A (fst (g 1))\<close>
    apply (rule rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart_measure_bound)
    using \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_restart\<^sup>*\<^sup>* (fst (g 1), snd (g 1)) (fst (g j), snd (g j))\<close> apply blast
        apply (simp add: cdcl\<^sub>N\<^sub>O\<^sub>T_inv_g)
       using \<open>bound_inv A (fst (g 1))\<close> apply simp
    done
  then have \<open>\<mu> A (fst (g j)) \<le> ?j\<close>
    by auto
  have inv: \<open>bound_inv A (fst (g j))\<close>
    using \<open>bound_inv A (fst (g 1))\<close> \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_inv (fst (g (Suc 0)))\<close>
    \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_restart\<^sup>*\<^sup>* (fst (g 1), snd (g 1)) (fst (g j), snd (g j))\<close>
    rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_bound_inv by auto
  obtain T m where
    cdcl\<^sub>N\<^sub>O\<^sub>T_m: \<open>(cdcl\<^sub>N\<^sub>O\<^sub>T ^^ m) (fst (g j)) T\<close> and
    f_m: \<open>f (snd (g j)) \<le> m\<close>
    using H[of j] by blast
  have \<open>?j < m\<close>
    using f_m j Nat.le_trans by linarith

  then show False
    using \<open>\<mu> A (fst (g j)) \<le> \<mu>_bound A (fst (g 1))\<close>
    cdcl\<^sub>N\<^sub>O\<^sub>T_comp_bounded[OF inv cdcl\<^sub>N\<^sub>O\<^sub>T_inv_g, of ] cdcl\<^sub>N\<^sub>O\<^sub>T_inv_g cdcl\<^sub>N\<^sub>O\<^sub>T_m
    \<open>?j < m\<close> by auto
qed

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_restart_steps_bigger_than_bound:
  assumes
    \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_restart S T\<close> and
    \<open>bound_inv A (fst S)\<close> and
    \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_inv (fst S)\<close> and
    \<open>f (snd S) > \<mu>_bound A (fst S)\<close>
  shows \<open>full1 cdcl\<^sub>N\<^sub>O\<^sub>T (fst S) (fst T)\<close>
  using assms
proof (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T_restart.induct)
  case restart_full
  then show ?case by auto
next
  case (restart_step m S T n U) note st = this(1) and f = this(2) and bound_inv = this(4) and
    cdcl\<^sub>N\<^sub>O\<^sub>T_inv = this(5) and \<mu> = this(6)
  then obtain m' where m: \<open>m = Suc m'\<close> by (cases m) auto
  have \<open>\<mu> A S - m' = 0\<close>
    using f bound_inv cdcl\<^sub>N\<^sub>O\<^sub>T_inv \<mu> m rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart_measure_bound by fastforce
  then have False using cdcl\<^sub>N\<^sub>O\<^sub>T_comp_n_le[of m' S T A] restart_step unfolding m by simp
  then show ?case by fast
qed

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_inv_inv_rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T:
  assumes
    inv: \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_inv S\<close> and
    binv: \<open>bound_inv A S\<close>
  shows \<open>(\<lambda>S T. cdcl\<^sub>N\<^sub>O\<^sub>T S T \<and> cdcl\<^sub>N\<^sub>O\<^sub>T_inv S \<and> bound_inv A S)\<^sup>*\<^sup>* S T \<longleftrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T\<close>
    (is \<open>?A\<^sup>*\<^sup>* S T \<longleftrightarrow> ?B\<^sup>*\<^sup>* S T\<close>)
  apply (rule iffI)
    using rtranclp_mono[of ?A ?B] apply blast
  apply (induction rule: rtranclp_induct)
    using inv binv apply simp
  by (metis (mono_tags, lifting) binv inv rtranclp.simps rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_bound_inv
    rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_cdcl\<^sub>N\<^sub>O\<^sub>T_inv)

lemma no_step_cdcl\<^sub>N\<^sub>O\<^sub>T_restart_no_step_cdcl\<^sub>N\<^sub>O\<^sub>T:
  assumes
    n_s: \<open>no_step cdcl\<^sub>N\<^sub>O\<^sub>T_restart S\<close> and
    inv: \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_inv (fst S)\<close> and
    binv: \<open>bound_inv A (fst S)\<close>
  shows \<open>no_step cdcl\<^sub>N\<^sub>O\<^sub>T (fst S)\<close>
proof (rule ccontr)
  assume \<open>\<not> ?thesis\<close>
  then obtain T where T: \<open>cdcl\<^sub>N\<^sub>O\<^sub>T (fst S) T\<close>
    by blast
  then obtain U where U: \<open>full (\<lambda>S T. cdcl\<^sub>N\<^sub>O\<^sub>T S T \<and> cdcl\<^sub>N\<^sub>O\<^sub>T_inv S \<and> bound_inv A S) T U\<close>
     using wf_exists_normal_form_full[OF wf_cdcl\<^sub>N\<^sub>O\<^sub>T, of A T] by auto
  moreover have inv_T: \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_inv T\<close>
    using \<open>cdcl\<^sub>N\<^sub>O\<^sub>T (fst S) T\<close> cdcl\<^sub>N\<^sub>O\<^sub>T_inv inv by blast
  moreover have b_inv_T: \<open>bound_inv A T\<close>
    using \<open>cdcl\<^sub>N\<^sub>O\<^sub>T (fst S) T\<close> binv bound_inv inv by blast
  ultimately have \<open>full cdcl\<^sub>N\<^sub>O\<^sub>T T U\<close>
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_inv_inv_rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_bound_inv
    rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_cdcl\<^sub>N\<^sub>O\<^sub>T_inv unfolding full_def by blast
  then have \<open>full1 cdcl\<^sub>N\<^sub>O\<^sub>T (fst S) U\<close>
    using T full_fullI by metis
  then show False by (metis n_s prod.collapse restart_full)
qed

end

subsection \<open>Merging backjump and learning\<close>
locale cdcl\<^sub>N\<^sub>O\<^sub>T_merge_bj_learn_ops =
  decide_ops trail clauses\<^sub>N\<^sub>O\<^sub>T prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T decide_conds +
  forget_ops trail clauses\<^sub>N\<^sub>O\<^sub>T prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T forget_conds +
  propagate_ops trail clauses\<^sub>N\<^sub>O\<^sub>T prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T propagate_conds
  for
    trail :: \<open>'st \<Rightarrow> ('v, unit) ann_lits\<close> and
    clauses\<^sub>N\<^sub>O\<^sub>T :: \<open>'st \<Rightarrow> 'v clauses\<close> and
    prepend_trail :: \<open>('v, unit) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    tl_trail :: \<open>'st \<Rightarrow>'st\<close> and
    add_cls\<^sub>N\<^sub>O\<^sub>T :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    remove_cls\<^sub>N\<^sub>O\<^sub>T :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    decide_conds :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> and
    propagate_conds :: \<open>('v, unit) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st \<Rightarrow> bool\<close> and
    forget_conds :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> bool\<close> +
  fixes backjump_l_cond :: \<open>'v clause \<Rightarrow> 'v clause \<Rightarrow> 'v literal \<Rightarrow> 'st \<Rightarrow> 'st \<Rightarrow> bool\<close>
begin

text \<open>We have a new backjump that combines the backjumping on the trail and the learning of the
  used clause (called @{term C''} below)\<close>
inductive backjump_l where
backjump_l: \<open>trail S = F' @ Decided K # F
   \<Longrightarrow> T \<sim> prepend_trail (Propagated L ()) (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F (add_cls\<^sub>N\<^sub>O\<^sub>T C'' S))
   \<Longrightarrow> C \<in># clauses\<^sub>N\<^sub>O\<^sub>T S
   \<Longrightarrow> trail S \<Turnstile>as CNot C
   \<Longrightarrow> undefined_lit F L
   \<Longrightarrow> atm_of L \<in> atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<union> atm_of ` (lits_of_l (trail S))
   \<Longrightarrow> clauses\<^sub>N\<^sub>O\<^sub>T S \<Turnstile>pm add_mset L C'
   \<Longrightarrow> C'' = add_mset L C'
   \<Longrightarrow> F \<Turnstile>as CNot C'
   \<Longrightarrow> backjump_l_cond C C' L S T
   \<Longrightarrow> backjump_l S T\<close>

text \<open>Avoid (meaningless) simplification in the theorem generated by \<open>inductive_cases\<close>:\<close>
declare reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_length_ne[simp del] Set.Un_iff[simp del] Set.insert_iff[simp del]
inductive_cases backjump_lE: \<open>backjump_l S T\<close>
thm backjump_lE
declare reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_length_ne[simp] Set.Un_iff[simp] Set.insert_iff[simp]

inductive cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> for S :: 'st where
cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_decide\<^sub>N\<^sub>O\<^sub>T: \<open>decide\<^sub>N\<^sub>O\<^sub>T S S' \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn S S'\<close> |
cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_propagate\<^sub>N\<^sub>O\<^sub>T: \<open>propagate\<^sub>N\<^sub>O\<^sub>T S S' \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn S S'\<close> |
cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_backjump_l: \<open>backjump_l S S' \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn S S'\<close> |
cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_forget\<^sub>N\<^sub>O\<^sub>T: \<open>forget\<^sub>N\<^sub>O\<^sub>T S S' \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn S S'\<close>

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_no_dup_inv:
  \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn S T \<Longrightarrow> no_dup (trail S) \<Longrightarrow> no_dup (trail T)\<close>
  apply (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn.induct)
      using defined_lit_map apply fastforce
    using defined_lit_map apply fastforce
   apply (force simp: defined_lit_map elim!: backjump_lE dest: no_dup_appendD)[]
  using forget\<^sub>N\<^sub>O\<^sub>T.simps apply (auto; fail)
  done
end

locale cdcl\<^sub>N\<^sub>O\<^sub>T_merge_bj_learn_proxy =
  cdcl\<^sub>N\<^sub>O\<^sub>T_merge_bj_learn_ops trail clauses\<^sub>N\<^sub>O\<^sub>T prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T
    decide_conds propagate_conds forget_conds
    \<open>\<lambda>C C' L' S T. backjump_l_cond C C' L' S T
    \<and> distinct_mset C' \<and> L' \<notin># C' \<and> \<not>tautology (add_mset L' C')\<close>
  for
    trail :: \<open>'st \<Rightarrow> ('v, unit) ann_lits\<close> and
    clauses\<^sub>N\<^sub>O\<^sub>T :: \<open>'st \<Rightarrow> 'v clauses\<close> and
    prepend_trail :: \<open>('v, unit) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    tl_trail :: \<open>'st \<Rightarrow>'st\<close> and
    add_cls\<^sub>N\<^sub>O\<^sub>T :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    remove_cls\<^sub>N\<^sub>O\<^sub>T :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    decide_conds :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> and
    propagate_conds :: \<open>('v, unit) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st \<Rightarrow> bool\<close> and
    forget_conds :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> bool\<close> and
    backjump_l_cond :: \<open>'v clause \<Rightarrow> 'v clause \<Rightarrow> 'v literal \<Rightarrow> 'st \<Rightarrow> 'st \<Rightarrow> bool\<close> +
  fixes
    inv :: \<open>'st \<Rightarrow> bool\<close>
begin

abbreviation backjump_conds :: \<open>'v clause \<Rightarrow> 'v clause \<Rightarrow> 'v literal \<Rightarrow> 'st \<Rightarrow> 'st \<Rightarrow> bool\<close>
  where
\<open>backjump_conds \<equiv> \<lambda>C C' L' S T. distinct_mset C' \<and> L' \<notin># C' \<and> \<not>tautology (add_mset L' C')\<close>

sublocale backjumping_ops trail clauses\<^sub>N\<^sub>O\<^sub>T prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T
  backjump_conds
  by standard

end

locale cdcl\<^sub>N\<^sub>O\<^sub>T_merge_bj_learn =
  cdcl\<^sub>N\<^sub>O\<^sub>T_merge_bj_learn_proxy trail clauses\<^sub>N\<^sub>O\<^sub>T prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T
    decide_conds propagate_conds forget_conds backjump_l_cond inv
  for
    trail :: \<open>'st \<Rightarrow> ('v, unit) ann_lits\<close> and
    clauses\<^sub>N\<^sub>O\<^sub>T :: \<open>'st \<Rightarrow> 'v clauses\<close> and
    prepend_trail :: \<open>('v, unit) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    tl_trail :: \<open>'st \<Rightarrow>'st\<close> and
    add_cls\<^sub>N\<^sub>O\<^sub>T :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    remove_cls\<^sub>N\<^sub>O\<^sub>T :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    decide_conds :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> and
    propagate_conds :: \<open>('v, unit) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st \<Rightarrow> bool\<close> and
    forget_conds :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> bool\<close> and
    backjump_l_cond :: \<open>'v clause \<Rightarrow> 'v clause \<Rightarrow> 'v literal \<Rightarrow> 'st \<Rightarrow> 'st \<Rightarrow> bool\<close> and
    inv :: \<open>'st \<Rightarrow> bool\<close> +
  assumes
     bj_merge_can_jump:
     \<open>\<And>S C F' K F L.
       inv S
       \<Longrightarrow> trail S = F' @ Decided K # F
       \<Longrightarrow> C \<in># clauses\<^sub>N\<^sub>O\<^sub>T S
       \<Longrightarrow> trail S \<Turnstile>as CNot C
       \<Longrightarrow> undefined_lit F L
       \<Longrightarrow> atm_of L \<in> atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<union> atm_of ` (lits_of_l (F' @ Decided K # F))
       \<Longrightarrow> clauses\<^sub>N\<^sub>O\<^sub>T S \<Turnstile>pm add_mset L C'
       \<Longrightarrow> F \<Turnstile>as CNot C'
       \<Longrightarrow> \<not>no_step backjump_l S\<close> and
     cdcl_merged_inv: \<open>\<And>S T. cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn S T \<Longrightarrow> inv S \<Longrightarrow> inv T\<close>  and
     can_propagate_or_decide_or_backjump_l:
       \<open>atm_of L \<in> atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<Longrightarrow>
       undefined_lit (trail S) L \<Longrightarrow>
       inv S \<Longrightarrow>
       satisfiable (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T S)) \<Longrightarrow>
       \<exists>T. decide\<^sub>N\<^sub>O\<^sub>T S T \<or> propagate\<^sub>N\<^sub>O\<^sub>T S T \<or> backjump_l S T\<close>
begin

lemma backjump_no_step_backjump_l:
  \<open>backjump S T \<Longrightarrow> inv S \<Longrightarrow> \<not>no_step backjump_l S\<close>
  apply (elim backjumpE)
  apply (rule bj_merge_can_jump)
    apply auto[7]
  by blast

lemma tautology_single_add:
  \<open>tautology (L + {#a#}) \<longleftrightarrow> tautology L \<or> -a \<in># L\<close>
  unfolding tautology_decomp by (cases a) auto

lemma backjump_l_implies_exists_backjump:
  assumes bj: \<open>backjump_l S T\<close> and \<open>inv S\<close> and n_d: \<open>no_dup (trail S)\<close>
  shows \<open>\<exists>U. backjump S U\<close>
proof -
  obtain C F' K F L C' where
    tr: \<open>trail S = F' @ Decided K # F\<close> and
    C: \<open>C \<in># clauses\<^sub>N\<^sub>O\<^sub>T S\<close> and
    T: \<open>T \<sim> prepend_trail (Propagated L ()) (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F (add_cls\<^sub>N\<^sub>O\<^sub>T (add_mset L C') S))\<close> and
    tr_C: \<open>trail S \<Turnstile>as CNot C\<close> and
    undef: \<open>undefined_lit F L\<close> and
    L: \<open>atm_of L \<in> atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<union> atm_of ` (lits_of_l (trail S))\<close> and
    S_C_L: \<open>clauses\<^sub>N\<^sub>O\<^sub>T S \<Turnstile>pm add_mset L C'\<close> and
    F_C': \<open>F \<Turnstile>as CNot C'\<close> and
    cond: \<open>backjump_l_cond C C' L S T\<close> and
    dist: \<open>distinct_mset (add_mset L C')\<close> and
    taut: \<open>\<not> tautology (add_mset L C')\<close>
    using bj by (elim backjump_lE) force
  have \<open>L \<notin># C'\<close>
    using dist by auto
  show ?thesis
    using backjump.intros[OF tr _ C tr_C undef L S_C_L F_C'] cond dist taut
    by auto
qed

text \<open>Without additional knowledge on @{term backjump_l_cond}, it is impossible to have the same
  invariant.\<close>
sublocale dpll_with_backjumping_ops trail clauses\<^sub>N\<^sub>O\<^sub>T prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T
  inv decide_conds backjump_conds propagate_conds
proof (unfold_locales, goal_cases)
  case 1
  { fix S S'
    assume bj: \<open>backjump_l S S'\<close>
    then obtain F' K F L C' C D where
      S': \<open>S' \<sim> prepend_trail (Propagated L ()) (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F (add_cls\<^sub>N\<^sub>O\<^sub>T D S))\<close>
        and
      tr_S: \<open>trail S = F' @ Decided K # F\<close> and
      C: \<open>C \<in># clauses\<^sub>N\<^sub>O\<^sub>T S\<close> and
      tr_S_C: \<open>trail S \<Turnstile>as CNot C\<close> and
      undef_L: \<open>undefined_lit F L\<close> and
      atm_L:
       \<open>atm_of L \<in> insert (atm_of K) (atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<union> atm_of ` (lits_of_l F' \<union> lits_of_l F))\<close>
       and
      cls_S_C': \<open>clauses\<^sub>N\<^sub>O\<^sub>T S \<Turnstile>pm add_mset L C'\<close> and
      F_C': \<open>F \<Turnstile>as CNot C'\<close> and
      dist: \<open>distinct_mset (add_mset L C')\<close> and
      not_tauto: \<open>\<not> tautology (add_mset L C')\<close> and
      cond: \<open>backjump_l_cond C C' L S S'\<close>
      \<open>D = add_mset L C'\<close>
      by (elim backjump_lE) simp
    interpret backjumping_ops trail clauses\<^sub>N\<^sub>O\<^sub>T prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T
    backjump_conds
      by unfold_locales
    have \<open>\<exists>T. backjump S T\<close>
      apply rule
      apply (rule backjump.intros)
               using tr_S apply simp
              apply (rule state_eq\<^sub>N\<^sub>O\<^sub>T_ref)
             using C apply simp
            using tr_S_C apply simp
          using undef_L apply simp
         using atm_L tr_S apply simp
        using cls_S_C' apply simp
       using F_C' apply simp
      using dist not_tauto cond by simp
    }
  then show ?case using 1 bj_merge_can_jump by meson
next
  case 2
  then show ?case
    using can_propagate_or_decide_or_backjump_l backjump_l_implies_exists_backjump by blast
qed

sublocale conflict_driven_clause_learning_ops trail clauses\<^sub>N\<^sub>O\<^sub>T prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T
  remove_cls\<^sub>N\<^sub>O\<^sub>T inv decide_conds backjump_conds propagate_conds
  \<open>\<lambda>C _. distinct_mset C \<and> \<not>tautology C\<close>
  forget_conds
  by unfold_locales

lemma backjump_l_learn_backjump:
  assumes bt: \<open>backjump_l S T\<close> and inv: \<open>inv S\<close>
  shows \<open>\<exists>C' L D. learn S (add_cls\<^sub>N\<^sub>O\<^sub>T D S)
    \<and> D = add_mset L C'
    \<and> backjump (add_cls\<^sub>N\<^sub>O\<^sub>T D S) T
    \<and> atms_of (add_mset L C') \<subseteq> atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<union> atm_of ` (lits_of_l (trail S))\<close>
proof -
   obtain C F' K F L l C' D where
     tr_S: \<open>trail S = F' @ Decided K # F\<close> and
     T: \<open>T \<sim> prepend_trail (Propagated L l) (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F (add_cls\<^sub>N\<^sub>O\<^sub>T D S))\<close> and
     C_cls_S: \<open>C \<in># clauses\<^sub>N\<^sub>O\<^sub>T S\<close> and
     tr_S_CNot_C: \<open>trail S \<Turnstile>as CNot C\<close> and
     undef: \<open>undefined_lit F L\<close> and
     atm_L: \<open>atm_of L \<in> atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<union> atm_of ` (lits_of_l (trail S))\<close> and
     clss_C: \<open>clauses\<^sub>N\<^sub>O\<^sub>T S \<Turnstile>pm D\<close> and
     D: \<open>D = add_mset L C'\<close>
     \<open>F \<Turnstile>as CNot C'\<close> and
     distinct: \<open>distinct_mset D\<close> and
     not_tauto: \<open>\<not> tautology D\<close> and
     cond: \<open>backjump_l_cond C C' L S T\<close>
     using bt inv by (elim backjump_lE) simp
   have atms_C': \<open>atms_of C' \<subseteq> atm_of ` (lits_of_l F)\<close>
     by (metis D(2) atms_of_def image_subsetI true_annots_CNot_all_atms_defined)
   then have \<open>atms_of (add_mset L C') \<subseteq> atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<union> atm_of ` (lits_of_l (trail S))\<close>
     using atm_L tr_S by auto
   moreover have learn: \<open>learn S (add_cls\<^sub>N\<^sub>O\<^sub>T D S)\<close>
     apply (rule learn.intros)
         apply (rule clss_C)
       using atms_C' atm_L D apply (fastforce simp add: tr_S in_plus_implies_atm_of_on_atms_of_ms)
     apply standard
      apply (rule distinct)
      apply (rule not_tauto)
      apply simp
     done
   moreover have bj: \<open>backjump (add_cls\<^sub>N\<^sub>O\<^sub>T D S) T\<close>
     apply (rule backjump.intros[of _ _ _ _ _ L C C'])
     using \<open>F \<Turnstile>as CNot C'\<close> C_cls_S tr_S_CNot_C undef T distinct not_tauto D cond
     by (auto simp: tr_S state_eq\<^sub>N\<^sub>O\<^sub>T_def simp del: state_simp\<^sub>N\<^sub>O\<^sub>T)
   ultimately show ?thesis using D by blast
qed

lemma backjump_l_backjump_learn:
  assumes bt: \<open>backjump_l S T\<close> and inv: \<open>inv S\<close>
  shows \<open>\<exists>C' L D S'. backjump S S'
    \<and> learn S' T
    \<and> D = (add_mset L C')
    \<and> T \<sim> add_cls\<^sub>N\<^sub>O\<^sub>T D S'
    \<and> atms_of (add_mset L C') \<subseteq> atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<union> atm_of ` (lits_of_l (trail S))
    \<and> clauses\<^sub>N\<^sub>O\<^sub>T S \<Turnstile>pm D\<close>
proof -
   obtain C F' K F L l C' D where
     tr_S: \<open>trail S = F' @ Decided K # F\<close> and
     T: \<open>T \<sim> prepend_trail (Propagated L l) (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F (add_cls\<^sub>N\<^sub>O\<^sub>T D S))\<close> and
     C_cls_S: \<open>C \<in># clauses\<^sub>N\<^sub>O\<^sub>T S\<close> and
     tr_S_CNot_C: \<open>trail S \<Turnstile>as CNot C\<close> and
     undef: \<open>undefined_lit F L\<close> and
     atm_L: \<open>atm_of L \<in> atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<union> atm_of ` (lits_of_l (trail S))\<close> and
     clss_C: \<open>clauses\<^sub>N\<^sub>O\<^sub>T S \<Turnstile>pm D\<close> and
     D: \<open>D = add_mset L C'\<close>
     \<open>F \<Turnstile>as CNot C'\<close> and
     distinct: \<open>distinct_mset D\<close> and
     not_tauto: \<open>\<not> tautology D\<close> and
     cond: \<open>backjump_l_cond C C' L S T\<close>
     using bt inv by (elim backjump_lE) simp
   let ?S' = \<open>prepend_trail (Propagated L ()) (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S)\<close>
   have atms_C': \<open>atms_of C' \<subseteq> atm_of ` (lits_of_l F)\<close>
     by (metis D(2) atms_of_def image_subsetI true_annots_CNot_all_atms_defined)
   then have \<open>atms_of (add_mset L C') \<subseteq> atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<union> atm_of ` (lits_of_l (trail S))\<close>
     using atm_L tr_S by auto
   moreover have learn: \<open>learn ?S' T\<close>
     apply (rule learn.intros)
         using clss_C apply auto[]
       using atms_C' atm_L D apply (fastforce simp add: tr_S in_plus_implies_atm_of_on_atms_of_ms)
     apply standard
      apply (rule distinct)
      apply (rule not_tauto)
      using T apply (auto simp: tr_S state_eq\<^sub>N\<^sub>O\<^sub>T_def simp del: state_simp\<^sub>N\<^sub>O\<^sub>T)
     done
   moreover have bj: \<open>backjump S (prepend_trail (Propagated L ()) (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S))\<close>
     apply (rule backjump.intros[of S F' K F _ L])
     using \<open>F \<Turnstile>as CNot C'\<close> C_cls_S tr_S_CNot_C undef T distinct not_tauto D cond clss_C atm_L
     by (auto simp: tr_S)
   moreover have \<open>T \<sim> (add_cls\<^sub>N\<^sub>O\<^sub>T D ?S')\<close>
     using T by (auto simp: tr_S state_eq\<^sub>N\<^sub>O\<^sub>T_def simp del: state_simp\<^sub>N\<^sub>O\<^sub>T)
   ultimately show ?thesis
     using D clss_C by blast
qed

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_is_tranclp_cdcl\<^sub>N\<^sub>O\<^sub>T:
  \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn S T \<Longrightarrow> inv S \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>+\<^sup>+ S T\<close>
proof (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn.induct)
  case (cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_decide\<^sub>N\<^sub>O\<^sub>T T)
  then have \<open>cdcl\<^sub>N\<^sub>O\<^sub>T S T\<close>
    using bj_decide\<^sub>N\<^sub>O\<^sub>T cdcl\<^sub>N\<^sub>O\<^sub>T.simps by fastforce
  then show ?case by auto
next
  case (cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_propagate\<^sub>N\<^sub>O\<^sub>T T)
  then have \<open>cdcl\<^sub>N\<^sub>O\<^sub>T S T\<close>
    using bj_propagate\<^sub>N\<^sub>O\<^sub>T cdcl\<^sub>N\<^sub>O\<^sub>T.simps by fastforce
  then show ?case by auto
next
   case (cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_forget\<^sub>N\<^sub>O\<^sub>T T)
   then have \<open>cdcl\<^sub>N\<^sub>O\<^sub>T S T\<close>
     using c_forget\<^sub>N\<^sub>O\<^sub>T by blast
   then show ?case by auto
next
   case (cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_backjump_l T) note bt = this(1) and inv = this(2)
   obtain C' :: \<open>'v clause\<close> and L :: \<open>'v literal\<close> and D :: \<open>'v clause\<close> where
     f3: \<open>learn S (add_cls\<^sub>N\<^sub>O\<^sub>T D S) \<and>
       backjump (add_cls\<^sub>N\<^sub>O\<^sub>T D S) T \<and>
       atms_of (add_mset L C') \<subseteq> atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<union> atm_of ` lits_of_l (trail S)\<close> and
     D: \<open>D = add_mset L C'\<close>
     using backjump_l_learn_backjump[OF bt inv] by blast
   then have f4: \<open>cdcl\<^sub>N\<^sub>O\<^sub>T S (add_cls\<^sub>N\<^sub>O\<^sub>T D S)\<close>
     using c_learn by blast
   have \<open>cdcl\<^sub>N\<^sub>O\<^sub>T (add_cls\<^sub>N\<^sub>O\<^sub>T D S) T\<close>
     using f3 bj_backjump c_dpll_bj by blast
   then show ?case
     using f4 by (meson tranclp.r_into_trancl tranclp.trancl_into_trancl)
qed

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_is_rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_and_inv:
  \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn\<^sup>*\<^sup>* S T \<Longrightarrow> inv S \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T \<and> inv T\<close>
proof (induction rule: rtranclp_induct)
  case base
  then show ?case by auto
next
  case (step T U) note st = this(1) and cdcl\<^sub>N\<^sub>O\<^sub>T = this(2) and IH = this(3)[OF this(4-)] and
    inv = this(4)
  have \<open>cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* T U\<close>
    using cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_is_tranclp_cdcl\<^sub>N\<^sub>O\<^sub>T[OF cdcl\<^sub>N\<^sub>O\<^sub>T] IH
     inv by auto
  then have \<open>cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S U\<close> using IH by fastforce
  moreover have \<open>inv U\<close> using IH cdcl\<^sub>N\<^sub>O\<^sub>T cdcl_merged_inv inv by blast
  ultimately show ?case using st by fast
qed

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_is_rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T:
  \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn\<^sup>*\<^sup>* S T \<Longrightarrow> inv S \<Longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T\<close>
  using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_is_rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_and_inv by blast

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_inv:
  \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn\<^sup>*\<^sup>* S T \<Longrightarrow> inv S \<Longrightarrow> inv T\<close>
  using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_is_rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_and_inv by blast

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_no_dup_inv:
  \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn\<^sup>*\<^sup>* S T \<Longrightarrow> no_dup (trail S) \<Longrightarrow> no_dup (trail T)\<close>
  by (induction rule: rtranclp_induct) (auto simp: cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_no_dup_inv)

definition \<mu>\<^sub>C' :: \<open>'v clause set \<Rightarrow> 'st \<Rightarrow> nat\<close> where
\<open>\<mu>\<^sub>C' A T \<equiv> \<mu>\<^sub>C (1+card (atms_of_ms A)) (2+card (atms_of_ms A)) (trail_weight T)\<close>

definition \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_merged :: \<open>'v clause set \<Rightarrow> 'st \<Rightarrow> nat\<close> where
\<open>\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_merged A T \<equiv>
  ((2+card (atms_of_ms A)) ^ (1+card (atms_of_ms A)) - \<mu>\<^sub>C' A T) * 2 + card (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T T))\<close>

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_decreasing_measure':
  assumes
    \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn S T\<close> and
    inv: \<open>inv S\<close> and
    atm_clss: \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<subseteq> atms_of_ms A\<close> and
    atm_trail: \<open>atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A\<close> and
    n_d: \<open>no_dup (trail S)\<close> and
    fin_A: \<open>finite A\<close>
  shows \<open>\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_merged A T < \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_merged A S\<close>
  using assms(1)
proof induction
  case (cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_decide\<^sub>N\<^sub>O\<^sub>T T)
  have \<open>clauses\<^sub>N\<^sub>O\<^sub>T S = clauses\<^sub>N\<^sub>O\<^sub>T T\<close>
    using cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_decide\<^sub>N\<^sub>O\<^sub>T.hyps by auto
  moreover have
    \<open>(2 + card (atms_of_ms A)) ^ (1 + card (atms_of_ms A))
       - \<mu>\<^sub>C (1 + card (atms_of_ms A)) (2 + card (atms_of_ms A)) (trail_weight T)
     < (2 + card (atms_of_ms A)) ^ (1 + card (atms_of_ms A))
       - \<mu>\<^sub>C (1 + card (atms_of_ms A)) (2 + card (atms_of_ms A)) (trail_weight S)\<close>
    apply (rule dpll_bj_trail_mes_decreasing_prop)
    using cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_decide\<^sub>N\<^sub>O\<^sub>T fin_A atm_clss atm_trail n_d inv
    by (simp_all add: bj_decide\<^sub>N\<^sub>O\<^sub>T cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_decide\<^sub>N\<^sub>O\<^sub>T.hyps)
  ultimately show ?case
    unfolding \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_merged_def \<mu>\<^sub>C'_def by simp
next
  case (cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_propagate\<^sub>N\<^sub>O\<^sub>T T)
  have \<open>clauses\<^sub>N\<^sub>O\<^sub>T S = clauses\<^sub>N\<^sub>O\<^sub>T T\<close>
    using cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_propagate\<^sub>N\<^sub>O\<^sub>T.hyps
    by (simp add: bj_propagate\<^sub>N\<^sub>O\<^sub>T inv dpll_bj_clauses)
  moreover have
    \<open>(2 + card (atms_of_ms A)) ^ (1 + card (atms_of_ms A))
       - \<mu>\<^sub>C (1 + card (atms_of_ms A)) (2 + card (atms_of_ms A)) (trail_weight T)
     < (2 + card (atms_of_ms A)) ^ (1 + card (atms_of_ms A))
       - \<mu>\<^sub>C (1 + card (atms_of_ms A)) (2 + card (atms_of_ms A)) (trail_weight S)\<close>
    apply (rule dpll_bj_trail_mes_decreasing_prop)
    using inv n_d atm_clss atm_trail fin_A by (simp_all add: bj_propagate\<^sub>N\<^sub>O\<^sub>T
      cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_propagate\<^sub>N\<^sub>O\<^sub>T.hyps)
  ultimately show ?case
    unfolding \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_merged_def \<mu>\<^sub>C'_def by simp
next
  case (cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_forget\<^sub>N\<^sub>O\<^sub>T T)
  have \<open>card (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T T)) < card (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T S))\<close>
    using \<open>forget\<^sub>N\<^sub>O\<^sub>T S T\<close> by (metis card_Diff1_less clauses_remove_cls\<^sub>N\<^sub>O\<^sub>T finite_set_mset
      forget\<^sub>N\<^sub>O\<^sub>T.cases linear set_mset_minus_replicate_mset(1) state_eq\<^sub>N\<^sub>O\<^sub>T_def)
  moreover
    have \<open>trail S = trail T\<close>
      using \<open>forget\<^sub>N\<^sub>O\<^sub>T S T\<close> by (auto elim: forget\<^sub>N\<^sub>O\<^sub>TE)
    then have
      \<open>(2 + card (atms_of_ms A)) ^ (1 + card (atms_of_ms A))
        - \<mu>\<^sub>C (1 + card (atms_of_ms A)) (2 + card (atms_of_ms A)) (trail_weight T)
 = (2 + card (atms_of_ms A)) ^ (1 + card (atms_of_ms A))
        - \<mu>\<^sub>C (1 + card (atms_of_ms A)) (2 + card (atms_of_ms A)) (trail_weight S)\<close>
       by auto
  ultimately show ?case
    unfolding \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_merged_def \<mu>\<^sub>C'_def by simp
next
  case (cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_backjump_l T) note bj_l = this(1)
  obtain C' L D S' where
    learn: \<open>learn S' T\<close> and
    bj: \<open>backjump S S'\<close> and
    atms_C: \<open>atms_of (add_mset L C') \<subseteq> atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<union> atm_of ` (lits_of_l (trail S))\<close> and
    D: \<open>D = add_mset L C'\<close> and
    T: \<open>T \<sim> add_cls\<^sub>N\<^sub>O\<^sub>T D S'\<close>
    using bj_l inv backjump_l_backjump_learn [of S] n_d atm_clss atm_trail by blast
  have card_T_S: \<open>card (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T T)) \<le> 1+ card (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T S))\<close>
    using bj_l inv by (force elim!: backjump_lE simp: card_insert_if)
  have tr_S_T: \<open>trail_weight S' = trail_weight T\<close>
    using T by auto
  have
    \<open>((2 + card (atms_of_ms A)) ^ (1 + card (atms_of_ms A))
      - \<mu>\<^sub>C (1 + card (atms_of_ms A)) (2 + card (atms_of_ms A)) (trail_weight S'))
    < ((2 + card (atms_of_ms A)) ^ (1 + card (atms_of_ms A))
      - \<mu>\<^sub>C (1 + card (atms_of_ms A)) (2 + card (atms_of_ms A))
           (trail_weight S))\<close>
    apply (rule dpll_bj_trail_mes_decreasing_prop)
         using bj bj_backjump apply blast
        using inv apply blast
       using atms_C atm_clss atm_trail D apply (simp add: n_d; fail)
      using atm_trail n_d apply (simp; fail)
     apply (simp add: n_d; fail)
    using fin_A apply (simp; fail)
    done
  then show ?case
    using card_T_S unfolding \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_merged_def \<mu>\<^sub>C'_def tr_S_T by linarith
qed

lemma wf_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn:
  assumes
    fin_A: \<open>finite A\<close>
  shows \<open>wf {(T, S).
    (inv S \<and> atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<subseteq> atms_of_ms A \<and> atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A
    \<and> no_dup (trail S))
    \<and> cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn S T}\<close>
  apply (rule wfP_if_measure[of _ _ \<open>\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_merged A\<close>])
  using cdcl\<^sub>N\<^sub>O\<^sub>T_decreasing_measure' fin_A by simp

lemma in_atms_neg_defined: \<open>x \<in> atms_of C' \<Longrightarrow> F \<Turnstile>as CNot C' \<Longrightarrow> x \<in> atm_of ` lits_of_l F\<close>
  by (metis (no_types, lifting) atms_of_def imageE true_annots_CNot_all_atms_defined)

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_atms_of_ms_clauses_decreasing:
  assumes \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn S T\<close>and \<open>inv S\<close>
  shows \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T T) \<subseteq> atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<union> atm_of ` (lits_of_l (trail S))\<close>
  using assms
  apply (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn.induct)
      prefer 4 apply (auto dest!: dpll_bj_atms_of_ms_clauses_inv set_mp
        simp add: atms_of_ms_def Union_eq
        elim!: decide\<^sub>N\<^sub>O\<^sub>TE propagate\<^sub>N\<^sub>O\<^sub>TE forget\<^sub>N\<^sub>O\<^sub>TE)[3]
  apply (elim backjump_lE)
  by (auto dest!: in_atms_neg_defined simp del:)

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_atms_in_trail_in_set:
  assumes
    \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn S T\<close> and \<open>inv S\<close> and
    \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<subseteq> A\<close> and
    \<open>atm_of ` (lits_of_l (trail S)) \<subseteq> A\<close>
  shows \<open>atm_of ` (lits_of_l (trail T)) \<subseteq> A\<close>
  using assms
  apply (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn.induct)
      apply (meson bj_decide\<^sub>N\<^sub>O\<^sub>T dpll_bj_atms_in_trail_in_set)
     apply (meson bj_propagate\<^sub>N\<^sub>O\<^sub>T dpll_bj_atms_in_trail_in_set)
    defer
    apply (metis forget\<^sub>N\<^sub>O\<^sub>TE state_eq\<^sub>N\<^sub>O\<^sub>T_trail trail_remove_cls\<^sub>N\<^sub>O\<^sub>T)
  by (metis (no_types, lifting) backjump_l_backjump_learn bj_backjump dpll_bj_atms_in_trail_in_set
      state_eq\<^sub>N\<^sub>O\<^sub>T_trail trail_add_cls\<^sub>N\<^sub>O\<^sub>T)

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_trail_clauses_bound:
  assumes
    cdcl: \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn\<^sup>*\<^sup>* S T\<close> and
    inv: \<open>inv S\<close> and
    atms_clauses_S: \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<subseteq> A\<close> and
    atms_trail_S: \<open>atm_of `(lits_of_l (trail S)) \<subseteq> A\<close>
  shows \<open>atm_of ` (lits_of_l (trail T)) \<subseteq> A \<and> atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T T) \<subseteq> A\<close>
  using cdcl
proof (induction rule: rtranclp_induct)
  case base
  then show ?case using atms_clauses_S atms_trail_S by simp
next
  case (step T U) note st = this(1) and cdcl\<^sub>N\<^sub>O\<^sub>T = this(2) and IH = this(3)
  have \<open>inv T\<close> using inv st rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_is_rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_and_inv by blast
  then have \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T U) \<subseteq> A\<close>
    using cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_atms_of_ms_clauses_decreasing cdcl\<^sub>N\<^sub>O\<^sub>T IH \<open>inv T\<close> by fast
  moreover
    have \<open>atm_of `(lits_of_l (trail U)) \<subseteq> A\<close>
      using cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_atms_in_trail_in_set[of _ _ A] \<open>inv T\<close> cdcl\<^sub>N\<^sub>O\<^sub>T step.IH by auto
  ultimately show ?case by fast
qed

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_trail_clauses_bound:
  assumes
    cdcl: \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn S T\<close> and
    inv: \<open>inv S\<close> and
    atms_clauses_S: \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<subseteq> A\<close> and
    atms_trail_S: \<open>atm_of `(lits_of_l (trail S)) \<subseteq> A\<close>
  shows \<open>atm_of ` (lits_of_l (trail T)) \<subseteq> A \<and> atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T T) \<subseteq> A\<close>
  using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_trail_clauses_bound[of S T] assms by auto

lemma tranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_cdcl\<^sub>N\<^sub>O\<^sub>T_tranclp:
  assumes
    \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn\<^sup>+\<^sup>+ S T\<close> and
    inv: \<open>inv S\<close> and
    atm_clss: \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<subseteq> atms_of_ms A\<close> and
    atm_trail: \<open>atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A\<close> and
    n_d: \<open>no_dup (trail S)\<close> and
    fin_A[simp]: \<open>finite A\<close>
  shows \<open>(T, S) \<in> {(T, S).
    (inv S \<and> atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<subseteq> atms_of_ms A \<and> atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A
    \<and> no_dup (trail S))
    \<and> cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn S T}\<^sup>+\<close> (is \<open>_ \<in> ?P\<^sup>+\<close>)
  using assms(1)
proof (induction rule: tranclp_induct)
  case base
  then show ?case using n_d atm_clss atm_trail inv by auto
next
  case (step T U) note st = this(1) and cdcl\<^sub>N\<^sub>O\<^sub>T = this(2) and IH = this(3)
  have st: \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn\<^sup>*\<^sup>* S T\<close>
    using [[simp_trace]]
    by (simp add: rtranclp_unfold st)
  have \<open>cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T\<close>
    apply (rule rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_is_rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T)
    using st cdcl\<^sub>N\<^sub>O\<^sub>T inv n_d atm_clss atm_trail inv by auto
  have \<open>inv T\<close>
    apply (rule rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_inv)
      using inv st cdcl\<^sub>N\<^sub>O\<^sub>T n_d atm_clss atm_trail inv by auto
  moreover have \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T T) \<subseteq> atms_of_ms A\<close>
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_trail_clauses_bound[OF st inv atm_clss atm_trail]
    by fast
  moreover have \<open>atm_of ` (lits_of_l (trail T))\<subseteq> atms_of_ms A\<close>
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_trail_clauses_bound[OF st inv atm_clss atm_trail]
    by fast
  moreover have \<open>no_dup (trail T)\<close>
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_no_dup_inv[OF st n_d] by fast
  ultimately have \<open>(U, T) \<in> ?P\<close>
    using cdcl\<^sub>N\<^sub>O\<^sub>T by auto
  then show ?case using IH by (simp add: trancl_into_trancl2)
qed

lemma wf_tranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn:
  assumes \<open>finite A\<close>
  shows \<open>wf {(T, S).
    (inv S \<and> atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<subseteq> atms_of_ms A \<and> atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A
    \<and> no_dup (trail S))
    \<and> cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn\<^sup>+\<^sup>+ S T}\<close>
  apply (rule wf_subset)
   apply (rule wf_trancl[OF wf_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn])
   using assms apply simp
  using tranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_cdcl\<^sub>N\<^sub>O\<^sub>T_tranclp[OF _ _ _ _ _ \<open>finite A\<close>] by auto

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_final_state:
  fixes A :: \<open>'v clause set\<close> and S T :: \<open>'st\<close>
  assumes
    n_s: \<open>no_step cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn S\<close> and
    atms_S: \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<subseteq> atms_of_ms A\<close> and
    atms_trail: \<open>atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A\<close> and
    n_d: \<open>no_dup (trail S)\<close> and
    \<open>finite A\<close> and
    inv: \<open>inv S\<close> and
    decomp: \<open>all_decomposition_implies_m (clauses\<^sub>N\<^sub>O\<^sub>T S) (get_all_ann_decomposition (trail S))\<close>
  shows \<open>unsatisfiable (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T S))
    \<or> (trail S \<Turnstile>asm clauses\<^sub>N\<^sub>O\<^sub>T S \<and> satisfiable (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T S)))\<close>
proof -
  let ?N = \<open>set_mset (clauses\<^sub>N\<^sub>O\<^sub>T S)\<close>
  let ?M = \<open>trail S\<close>
  consider
      (sat) \<open>satisfiable ?N\<close> and \<open>?M \<Turnstile>as ?N\<close>
    | (sat') \<open>satisfiable ?N\<close> and \<open>\<not> ?M \<Turnstile>as ?N\<close>
    | (unsat) \<open>unsatisfiable ?N\<close>
    by auto
  then show ?thesis
    proof cases
      case sat' note sat = this(1) and M = this(2)
      obtain C where \<open>C \<in> ?N\<close> and \<open>\<not>?M \<Turnstile>a C\<close> using M unfolding true_annots_def by auto
      obtain I :: \<open>'v literal set\<close> where
        \<open>I \<Turnstile>s ?N\<close> and
        cons: \<open>consistent_interp I\<close> and
        tot: \<open>total_over_m I ?N\<close> and
        atm_I_N: \<open>atm_of `I \<subseteq> atms_of_ms ?N\<close>
        using sat unfolding satisfiable_def_min by auto
      let ?I = \<open>I \<union> {P| P. P \<in> lits_of_l ?M \<and> atm_of P \<notin> atm_of ` I}\<close>
      let ?O = \<open>{unmark L |L. is_decided L \<and> L \<in> set ?M \<and> atm_of (lit_of L) \<notin> atms_of_ms ?N}\<close>
      have cons_I': \<open>consistent_interp ?I\<close>
        using cons using \<open>no_dup ?M\<close> unfolding consistent_interp_def
        by (auto simp add: atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set lits_of_def
          dest!: no_dup_cannot_not_lit_and_uminus)
      have tot_I': \<open>total_over_m ?I (?N \<union> unmark_l ?M)\<close>
        using tot atms_of_s_def unfolding total_over_m_def total_over_set_def
        by (fastforce simp: image_iff)
      have \<open>{P |P. P \<in> lits_of_l ?M \<and> atm_of P \<notin> atm_of ` I} \<Turnstile>s ?O\<close>
        using \<open>I\<Turnstile>s ?N\<close> atm_I_N by (auto simp add: atm_of_eq_atm_of true_clss_def lits_of_def)
      then have I'_N: \<open>?I \<Turnstile>s ?N \<union> ?O\<close>
        using \<open>I\<Turnstile>s ?N\<close> true_clss_union_increase by force
      have tot': \<open>total_over_m ?I (?N\<union>?O)\<close>
        using atm_I_N tot unfolding total_over_m_def total_over_set_def
        by (force simp: lits_of_def elim!: is_decided_ex_Decided)

      have atms_N_M: \<open>atms_of_ms ?N \<subseteq> atm_of ` lits_of_l ?M\<close>
        proof (rule ccontr)
          assume \<open>\<not> ?thesis\<close>
          then obtain l :: 'v where
            l_N: \<open>l \<in> atms_of_ms ?N\<close> and
            l_M: \<open>l \<notin> atm_of ` lits_of_l ?M\<close>
            by auto
          have \<open>undefined_lit ?M (Pos l)\<close>
            using l_M by (metis Decided_Propagated_in_iff_in_lits_of_l
              atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set literal.sel(1))
          then show False
            using can_propagate_or_decide_or_backjump_l[of \<open>Pos l\<close> S] l_N
            cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_decide\<^sub>N\<^sub>O\<^sub>T n_s inv sat
            by (auto dest!: cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn.intros)
        qed

      have \<open>?M \<Turnstile>as CNot C\<close>
      apply (rule all_variables_defined_not_imply_cnot)
        using atms_N_M \<open>C \<in> ?N\<close> \<open>\<not> ?M \<Turnstile>a C\<close> atms_of_atms_of_ms_mono[OF \<open>C \<in> ?N\<close>]
        by (auto dest: atms_of_atms_of_ms_mono)
      have \<open>\<exists>l \<in> set ?M. is_decided l\<close>
        proof (rule ccontr)
          let ?O = \<open>{unmark L |L. is_decided L \<and> L \<in> set ?M \<and> atm_of (lit_of L) \<notin> atms_of_ms ?N}\<close>
          have \<theta>[iff]: \<open>\<And>I. total_over_m I (?N \<union> ?O \<union> unmark_l ?M)
            \<longleftrightarrow> total_over_m I (?N \<union>unmark_l ?M)\<close>
            unfolding total_over_set_def total_over_m_def atms_of_ms_def by blast
          assume \<open>\<not> ?thesis\<close>
          then have [simp]:\<open>{unmark L |L. is_decided L \<and> L \<in> set ?M}
   = {unmark L |L. is_decided L \<and> L \<in> set ?M \<and> atm_of (lit_of L) \<notin> atms_of_ms ?N}\<close>
            by auto
          then have \<open>?N \<union> ?O \<Turnstile>ps unmark_l ?M\<close>
            using all_decomposition_implies_propagated_lits_are_implied[OF decomp] by auto

          then have \<open>?I \<Turnstile>s unmark_l ?M\<close>
            using cons_I' I'_N tot_I' \<open>?I \<Turnstile>s ?N \<union> ?O\<close> unfolding \<theta> true_clss_clss_def by blast
          then have \<open>lits_of_l ?M \<subseteq> ?I\<close>
            unfolding true_clss_def lits_of_def by auto
          then have \<open>?M \<Turnstile>as ?N\<close>
            using I'_N \<open>C \<in> ?N\<close> \<open>\<not> ?M \<Turnstile>a C\<close> cons_I' atms_N_M
            by (meson \<open>trail S \<Turnstile>as CNot C\<close> consistent_CNot_not rev_subsetD sup_ge1 true_annot_def
              true_annots_def true_cls_mono_set_mset_l true_clss_def)
          then show False using M by fast
        qed
      from List.split_list_first_propE[OF this] obtain K :: \<open>'v literal\<close> and d :: unit and
        F F' :: \<open>('v, unit) ann_lits\<close> where
        M_K: \<open>?M = F' @ Decided K # F\<close> and
        nm: \<open>\<forall>f\<in>set F'. \<not>is_decided f\<close>
        by (metis (full_types) is_decided_ex_Decided old.unit.exhaust)
      let ?K = \<open>Decided K::('v, unit) ann_lit\<close>
      have \<open>?K \<in> set ?M\<close>
        unfolding M_K by auto
      let ?C = \<open>image_mset lit_of {#L\<in>#mset ?M. is_decided L \<and> L\<noteq>?K#} :: 'v clause\<close>
      let ?C' = \<open>set_mset (image_mset (\<lambda>L::'v literal. {#L#}) (?C + unmark ?K))\<close>
      have \<open>?N \<union> {unmark L |L. is_decided L \<and> L \<in> set ?M} \<Turnstile>ps unmark_l ?M\<close>
        using all_decomposition_implies_propagated_lits_are_implied[OF decomp] .
      moreover have C': \<open>?C' = {unmark L |L. is_decided L \<and> L \<in> set ?M}\<close>
        unfolding M_K apply standard
          apply force
        by auto
      ultimately have N_C_M: \<open>?N \<union> ?C' \<Turnstile>ps unmark_l ?M\<close>
        by auto
      have N_M_False: \<open>?N \<union> (\<lambda>L. unmark L) ` (set ?M) \<Turnstile>ps {{#}}\<close>
        unfolding true_clss_clss_def true_annots_def Ball_def true_annot_def
      proof (intro allI impI)
        fix LL :: "'v literal set"
        assume
          tot: \<open>total_over_m LL (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T S) \<union> unmark_l (trail S) \<union> {{#}})\<close> and
          cons: \<open>consistent_interp LL\<close> and
          LL: \<open>LL \<Turnstile>s set_mset (clauses\<^sub>N\<^sub>O\<^sub>T S) \<union> unmark_l (trail S)\<close>
        have \<open>total_over_m LL (CNot C)\<close>
          by (metis \<open>C \<in># clauses\<^sub>N\<^sub>O\<^sub>T S\<close> insert_absorb tot total_over_m_CNot_toal_over_m
              total_over_m_insert total_over_m_union)
        then have "total_over_m LL (unmark_l (trail S) \<union> CNot C)"
          using tot by force
        then show "LL \<Turnstile>s {{#}}"
          using tot cons LL
          by (metis (no_types) \<open>C \<in># clauses\<^sub>N\<^sub>O\<^sub>T S\<close> \<open>trail S \<Turnstile>as CNot C\<close> consistent_CNot_not
              true_annots_true_clss_clss true_clss_clss_def true_clss_def true_clss_union)
      qed

      have \<open>undefined_lit F K\<close> using \<open>no_dup ?M\<close> unfolding M_K by (auto simp: defined_lit_map)
      moreover {
        have \<open>?N \<union> ?C' \<Turnstile>ps {{#}}\<close>
          proof -
            have A: \<open>?N \<union> ?C' \<union> unmark_l ?M = ?N \<union> unmark_l ?M\<close>
              unfolding M_K by auto
            show ?thesis
              using true_clss_clss_left_right[OF N_C_M, of \<open>{{#}}\<close>] N_M_False unfolding A by auto
          qed
        have \<open>?N \<Turnstile>p image_mset uminus ?C + {#-K#}\<close>
          unfolding true_clss_cls_def true_clss_clss_def total_over_m_def
          proof (intro allI impI)
            fix I
            assume
              tot: \<open>total_over_set I (atms_of_ms (?N \<union> {image_mset uminus ?C+ {#- K#}}))\<close> and
              cons: \<open>consistent_interp I\<close> and
              \<open>I \<Turnstile>s ?N\<close>
            have \<open>(K \<in> I \<and> -K \<notin> I) \<or> (-K \<in> I \<and> K \<notin> I)\<close>
              using cons tot unfolding consistent_interp_def by (cases K) auto
            have \<open>{a \<in> set (trail S). is_decided a \<and> a \<noteq> Decided K} =
             set (trail S) \<inter> {L. is_decided L \<and> L \<noteq> Decided K}\<close>
             by auto
            then have tot': \<open>total_over_set I
               (atm_of ` lit_of ` (set ?M \<inter> {L. is_decided L \<and> L \<noteq> Decided K}))\<close>
              using tot by (auto simp add: atms_of_uminus_lit_atm_of_lit_of)
            { fix x :: \<open>('v, unit) ann_lit\<close>
              assume
                a3: \<open>lit_of x \<notin> I\<close> and
                a1: \<open>x \<in> set ?M\<close> and
                a4: \<open>is_decided x\<close> and
                a5: \<open>x \<noteq> Decided K\<close>
              then have \<open>Pos (atm_of (lit_of x)) \<in> I \<or> Neg (atm_of (lit_of x)) \<in> I\<close>
                using a5 a4 tot' a1 unfolding total_over_set_def atms_of_s_def by blast
              moreover have f6: \<open>Neg (atm_of (lit_of x)) = - Pos (atm_of (lit_of x))\<close>
                by simp
              ultimately have \<open>- lit_of x \<in> I\<close>
                using f6 a3 by (metis (no_types) atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set
                  literal.sel(1))
            } note H = this

            have \<open>\<not>I \<Turnstile>s ?C'\<close>
              using \<open>?N \<union> ?C' \<Turnstile>ps {{#}}\<close> tot cons \<open>I \<Turnstile>s ?N\<close>
              unfolding true_clss_clss_def total_over_m_def
              by (simp add: atms_of_uminus_lit_atm_of_lit_of atms_of_ms_single_image_atm_of_lit_of)
            then show \<open>I \<Turnstile> image_mset uminus ?C + {#- K#}\<close>
              unfolding true_clss_def true_cls_def Bex_def
              using \<open>(K \<in> I \<and> -K \<notin> I) \<or> (-K \<in> I \<and> K \<notin> I)\<close>
              by (auto dest!: H)
          qed }
      moreover have \<open>F \<Turnstile>as CNot (image_mset uminus ?C)\<close>
        using nm unfolding true_annots_def CNot_def M_K by (auto simp add: lits_of_def)
      ultimately have False
        using bj_merge_can_jump[of S F' K F C \<open>-K\<close>
          \<open>image_mset uminus (image_mset lit_of {# L :# mset ?M. is_decided L \<and> L \<noteq> Decided K#})\<close>]
          \<open>C\<in>?N\<close> n_s \<open>?M \<Turnstile>as CNot C\<close> bj_backjump inv sat unfolding M_K
          by (auto simp: cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn.simps)
        then show ?thesis by fast
    qed auto
qed

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_all_decomposition_implies:
  assumes \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn S T\<close> and inv: \<open>inv S\<close>
    \<open>all_decomposition_implies_m (clauses\<^sub>N\<^sub>O\<^sub>T S) (get_all_ann_decomposition (trail S))\<close>
  shows
    \<open>all_decomposition_implies_m (clauses\<^sub>N\<^sub>O\<^sub>T T) (get_all_ann_decomposition (trail T))\<close>
    using assms
proof (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn.induct)
  case (cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_backjump_l T) note bj_l = this(1)
  obtain C' L D S' where
    learn: \<open>learn S' T\<close> and
    bj: \<open>backjump S S'\<close> and
    atms_C: \<open>atms_of (add_mset L C') \<subseteq> atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<union> atm_of ` (lits_of_l (trail S))\<close> and
    D: \<open>D = add_mset L C'\<close> and
    T: \<open>T \<sim> add_cls\<^sub>N\<^sub>O\<^sub>T D S'\<close>
    using bj_l inv backjump_l_backjump_learn [of S] by blast
  have \<open>all_decomposition_implies_m (clauses\<^sub>N\<^sub>O\<^sub>T S') (get_all_ann_decomposition (trail S'))\<close>
    using bj bj_backjump dpll_bj_clauses inv(1) inv(2)
    by (fastforce simp: dpll_bj_all_decomposition_implies_inv)
  then show ?case
    using T by (auto simp: all_decomposition_implies_insert_single)
qed (auto simp: dpll_bj_all_decomposition_implies_inv cdcl\<^sub>N\<^sub>O\<^sub>T_all_decomposition_implies
    dest!: dpll_bj.intros cdcl\<^sub>N\<^sub>O\<^sub>T.intros)

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_all_decomposition_implies:
  assumes \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn\<^sup>*\<^sup>* S T\<close> and inv: \<open>inv S\<close>
    \<open>all_decomposition_implies_m (clauses\<^sub>N\<^sub>O\<^sub>T S) (get_all_ann_decomposition (trail S))\<close>
  shows
    \<open>all_decomposition_implies_m (clauses\<^sub>N\<^sub>O\<^sub>T T) (get_all_ann_decomposition (trail T))\<close>
  using assms
  apply (induction rule: rtranclp_induct)
    apply simp
  using cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_all_decomposition_implies
    rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_is_rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_and_inv by blast

lemma full_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_final_state:
  fixes A :: \<open>'v clause set\<close> and S T :: \<open>'st\<close>
  assumes
    full: \<open>full cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn S T\<close> and
    atms_S: \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<subseteq> atms_of_ms A\<close> and
    atms_trail: \<open>atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A\<close> and
    n_d: \<open>no_dup (trail S)\<close> and
    \<open>finite A\<close> and
    inv: \<open>inv S\<close> and
    decomp: \<open>all_decomposition_implies_m (clauses\<^sub>N\<^sub>O\<^sub>T S) (get_all_ann_decomposition (trail S))\<close>
  shows \<open>unsatisfiable (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T T))
    \<or> (trail T \<Turnstile>asm clauses\<^sub>N\<^sub>O\<^sub>T T \<and> satisfiable (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T T)))\<close>
proof -
  have st: \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn\<^sup>*\<^sup>* S T\<close> and n_s: \<open>no_step cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn T\<close>
    using full unfolding full_def by blast+
  then have st': \<open>cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T\<close>
    using inv rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_is_rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_and_inv n_d by auto
  have \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T T) \<subseteq> atms_of_ms A\<close> and \<open>atm_of ` lits_of_l (trail T) \<subseteq> atms_of_ms A\<close>
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_trail_clauses_bound[OF st inv atms_S atms_trail] by blast+
  moreover have \<open>no_dup (trail T)\<close>
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_no_dup_inv inv n_d st by blast
  moreover have \<open>inv T\<close>
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_inv inv st by blast
  moreover have \<open>all_decomposition_implies_m (clauses\<^sub>N\<^sub>O\<^sub>T T) (get_all_ann_decomposition (trail T))\<close>
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_all_decomposition_implies inv st decomp n_d by blast
  ultimately show ?thesis
    using cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_final_state[of T A] \<open>finite A\<close> n_s by fast
qed

end

subsection \<open>Instantiations\<close>
text \<open>In this section, we instantiate the previous locales to ensure that the assumption are not
  contradictory.\<close>
locale cdcl\<^sub>N\<^sub>O\<^sub>T_with_backtrack_and_restarts =
  conflict_driven_clause_learning_learning_before_backjump_only_distinct_learnt
    trail clauses\<^sub>N\<^sub>O\<^sub>T prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T
    inv decide_conds backjump_conds propagate_conds learn_restrictions forget_restrictions
  for
    trail :: \<open>'st \<Rightarrow> ('v, unit) ann_lits\<close> and
    clauses\<^sub>N\<^sub>O\<^sub>T :: \<open>'st \<Rightarrow> 'v clauses\<close> and
    prepend_trail :: \<open>('v, unit) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    tl_trail :: \<open>'st \<Rightarrow>'st\<close> and
    add_cls\<^sub>N\<^sub>O\<^sub>T :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    remove_cls\<^sub>N\<^sub>O\<^sub>T :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    inv :: \<open>'st \<Rightarrow> bool\<close> and
    decide_conds :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> and
    backjump_conds :: \<open>'v clause \<Rightarrow> 'v clause \<Rightarrow> 'v literal \<Rightarrow> 'st \<Rightarrow> 'st \<Rightarrow> bool\<close> and
    propagate_conds :: \<open>('v, unit) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st \<Rightarrow> bool\<close> and
    learn_restrictions forget_restrictions :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> bool\<close>
    +
  fixes f :: \<open>nat \<Rightarrow> nat\<close>
  assumes
    unbounded: \<open>unbounded f\<close> and f_ge_1: \<open>\<And>n. n \<ge> 1 \<Longrightarrow> f n \<ge> 1\<close> and
    inv_restart:\<open>\<And>S T. inv S \<Longrightarrow> T \<sim> reduce_trail_to\<^sub>N\<^sub>O\<^sub>T ([]::'a list) S \<Longrightarrow> inv T\<close>
begin

lemma bound_inv_inv:
  assumes
    \<open>inv S\<close> and
    n_d: \<open>no_dup (trail S)\<close> and
    atms_clss_S_A: \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<subseteq> atms_of_ms A\<close> and
    atms_trail_S_A:\<open>atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A\<close> and
    \<open>finite A\<close> and
    cdcl\<^sub>N\<^sub>O\<^sub>T: \<open>cdcl\<^sub>N\<^sub>O\<^sub>T S T\<close>
  shows
    \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T T) \<subseteq> atms_of_ms A\<close> and
    \<open>atm_of ` lits_of_l (trail T) \<subseteq> atms_of_ms A\<close> and
    \<open>finite A\<close>
proof -
  have \<open>cdcl\<^sub>N\<^sub>O\<^sub>T S T\<close>
    using \<open>inv S\<close> cdcl\<^sub>N\<^sub>O\<^sub>T by linarith
  then have \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T T) \<subseteq> atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<union> atm_of ` lits_of_l (trail S)\<close>
    using \<open>inv S\<close>
    by (meson conflict_driven_clause_learning_ops.cdcl\<^sub>N\<^sub>O\<^sub>T_atms_of_ms_clauses_decreasing
      conflict_driven_clause_learning_ops_axioms n_d)
  then show \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T T) \<subseteq> atms_of_ms A\<close>
    using atms_clss_S_A atms_trail_S_A by blast
next
  show \<open>atm_of ` lits_of_l (trail T) \<subseteq> atms_of_ms A\<close>
    by (meson \<open>inv S\<close> atms_clss_S_A atms_trail_S_A cdcl\<^sub>N\<^sub>O\<^sub>T cdcl\<^sub>N\<^sub>O\<^sub>T_atms_in_trail_in_set n_d)
next
  show \<open>finite A\<close>
    using \<open>finite A\<close> by simp
qed

sublocale cdcl\<^sub>N\<^sub>O\<^sub>T_increasing_restarts_ops \<open>\<lambda>S T. T \<sim> reduce_trail_to\<^sub>N\<^sub>O\<^sub>T ([]::'a list) S\<close> cdcl\<^sub>N\<^sub>O\<^sub>T f
  \<open>\<lambda>A S. atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<subseteq> atms_of_ms A \<and> atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A \<and>
  finite A\<close>
  \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L' \<open>\<lambda>S. inv S \<and> no_dup (trail S)\<close>
  \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound
  apply unfold_locales
           apply (simp add: unbounded)
          using f_ge_1 apply force
         using bound_inv_inv apply meson
        apply (rule cdcl\<^sub>N\<^sub>O\<^sub>T_decreasing_measure'; simp)
        apply (rule rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound; simp)
       apply (rule rtranclp_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound_decreasing; simp)
      apply auto[]
    apply auto[]
   using cdcl\<^sub>N\<^sub>O\<^sub>T_inv cdcl\<^sub>N\<^sub>O\<^sub>T_no_dup apply blast
  using inv_restart apply auto[]
  done

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_le_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound:
  assumes
    cdcl\<^sub>N\<^sub>O\<^sub>T: \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_restart (T, a) (V, b)\<close> and
    cdcl\<^sub>N\<^sub>O\<^sub>T_inv:
      \<open>inv T\<close>
      \<open>no_dup (trail T)\<close> and
    bound_inv:
      \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T T) \<subseteq> atms_of_ms A\<close>
      \<open>atm_of ` lits_of_l (trail T) \<subseteq> atms_of_ms A\<close>
      \<open>finite A\<close>
  shows \<open>\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L' A V \<le> \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound A T\<close>
  using cdcl\<^sub>N\<^sub>O\<^sub>T_inv bound_inv
proof (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_induct[OF cdcl\<^sub>N\<^sub>O\<^sub>T])
  case (1 m S T n U) note U = this(3)
  show ?case
    apply (rule rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound_reduce_trail_to\<^sub>N\<^sub>O\<^sub>T[of S T])
         using \<open>(cdcl\<^sub>N\<^sub>O\<^sub>T ^^ m) S T\<close> apply (fastforce dest!: relpowp_imp_rtranclp)
        using 1 by auto
next
  case (2 S T n) note full = this(2)
  show ?case
    apply (rule rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound)
    using full 2 unfolding full1_def by force+
qed

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound_le_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound:
  assumes
    cdcl\<^sub>N\<^sub>O\<^sub>T: \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_restart (T, a) (V, b)\<close> and
    cdcl\<^sub>N\<^sub>O\<^sub>T_inv:
      \<open>inv T\<close>
      \<open>no_dup (trail T)\<close> and
    bound_inv:
      \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T T) \<subseteq> atms_of_ms A\<close>
      \<open>atm_of ` lits_of_l (trail T) \<subseteq> atms_of_ms A\<close>
      \<open>finite A\<close>
  shows \<open>\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound A V \<le> \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound A T\<close>
  using cdcl\<^sub>N\<^sub>O\<^sub>T_inv bound_inv
proof (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_induct[OF cdcl\<^sub>N\<^sub>O\<^sub>T])
  case (1 m S T n U) note U = this(3)
  have \<open>\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound A T \<le> \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound A S\<close>
     apply (rule rtranclp_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound_decreasing)
         using \<open>(cdcl\<^sub>N\<^sub>O\<^sub>T ^^ m) S T\<close> apply (fastforce dest: relpowp_imp_rtranclp)
        using 1 by auto
  then show ?case using U unfolding \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound_def by auto
next
  case (2 S T n) note full = this(2)
  show ?case
    apply (rule rtranclp_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound_decreasing)
    using full 2 unfolding full1_def by force+
qed

sublocale cdcl\<^sub>N\<^sub>O\<^sub>T_increasing_restarts _ _ _ _ _ _
    f
   (* restart *) \<open>\<lambda>S T. T \<sim> reduce_trail_to\<^sub>N\<^sub>O\<^sub>T ([]::'a list) S\<close>
   (* bound_inv *)\<open>\<lambda>A S. atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<subseteq> atms_of_ms A
     \<and> atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A \<and> finite A\<close>
   \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L' cdcl\<^sub>N\<^sub>O\<^sub>T
   (* inv *) \<open>\<lambda>S. inv S \<and> no_dup (trail S)\<close>
   \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound
  apply unfold_locales
   using cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_le_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound apply simp
  using cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound_le_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound apply simp
  done

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_restart_all_decomposition_implies:
  assumes \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_restart S T\<close> and
    \<open>inv (fst S)\<close> and
    \<open>no_dup (trail (fst S))\<close>
    \<open>all_decomposition_implies_m (clauses\<^sub>N\<^sub>O\<^sub>T (fst S)) (get_all_ann_decomposition (trail (fst S)))\<close>
  shows
    \<open>all_decomposition_implies_m (clauses\<^sub>N\<^sub>O\<^sub>T (fst T)) (get_all_ann_decomposition (trail (fst T)))\<close>
  using assms apply (induction)
  using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_all_decomposition_implies by (auto dest!: tranclp_into_rtranclp
    simp: full1_def)

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_restart_all_decomposition_implies:
  assumes \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_restart\<^sup>*\<^sup>* S T\<close> and
    inv: \<open>inv (fst S)\<close> and
    n_d: \<open>no_dup (trail (fst S))\<close> and
    decomp:
      \<open>all_decomposition_implies_m (clauses\<^sub>N\<^sub>O\<^sub>T (fst S)) (get_all_ann_decomposition (trail (fst S)))\<close>
  shows
    \<open>all_decomposition_implies_m (clauses\<^sub>N\<^sub>O\<^sub>T (fst T)) (get_all_ann_decomposition (trail (fst T)))\<close>
  using assms(1)
proof (induction rule: rtranclp_induct)
  case base
  then show ?case using decomp by simp
next
  case (step T u) note st = this(1) and r = this(2) and IH = this(3)
  have \<open>inv (fst T)\<close>
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_cdcl\<^sub>N\<^sub>O\<^sub>T_inv[OF st] inv n_d by blast
  moreover have \<open>no_dup (trail (fst T))\<close>
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_cdcl\<^sub>N\<^sub>O\<^sub>T_inv[OF st] inv n_d by blast
  ultimately show ?case
    using cdcl\<^sub>N\<^sub>O\<^sub>T_restart_all_decomposition_implies r IH n_d by fast
qed

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_restart_sat_ext_iff:
  assumes
    st: \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_restart S T\<close> and
    n_d: \<open>no_dup (trail (fst S))\<close> and
    inv: \<open>inv (fst S)\<close>
  shows \<open>I \<Turnstile>sextm clauses\<^sub>N\<^sub>O\<^sub>T (fst S) \<longleftrightarrow> I \<Turnstile>sextm clauses\<^sub>N\<^sub>O\<^sub>T (fst T)\<close>
  using assms
proof (induction)
  case (restart_step m S T n U)
  then show ?case
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_bj_sat_ext_iff n_d by (fastforce dest!: relpowp_imp_rtranclp)
next
  case restart_full
  then show ?case using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_bj_sat_ext_iff unfolding full1_def
  by (fastforce dest!: tranclp_into_rtranclp)
qed

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_restart_sat_ext_iff:
  fixes S T :: \<open>'st \<times> nat\<close>
  assumes
    st: \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_restart\<^sup>*\<^sup>* S T\<close> and
    n_d: \<open>no_dup (trail (fst S))\<close> and
    inv: \<open>inv (fst S)\<close>
  shows \<open>I \<Turnstile>sextm clauses\<^sub>N\<^sub>O\<^sub>T (fst S) \<longleftrightarrow> I \<Turnstile>sextm clauses\<^sub>N\<^sub>O\<^sub>T (fst T)\<close>
  using st
proof (induction)
  case base
  then show ?case by simp
next
  case (step T U) note st = this(1) and r = this(2) and IH = this(3)
  have \<open>inv (fst T)\<close>
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_cdcl\<^sub>N\<^sub>O\<^sub>T_inv[OF st] inv n_d by blast+
  moreover have \<open>no_dup (trail (fst T))\<close>
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_cdcl\<^sub>N\<^sub>O\<^sub>T_inv rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_no_dup st inv n_d by blast
  ultimately show ?case
    using cdcl\<^sub>N\<^sub>O\<^sub>T_restart_sat_ext_iff[OF r] IH by blast
qed

theorem full_cdcl\<^sub>N\<^sub>O\<^sub>T_restart_backjump_final_state:
  fixes A :: \<open>'v clause set\<close> and S T :: \<open>'st\<close>
  assumes
    full: \<open>full cdcl\<^sub>N\<^sub>O\<^sub>T_restart (S, n) (T, m)\<close> and
    atms_S: \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<subseteq> atms_of_ms A\<close> and
    atms_trail: \<open>atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A\<close> and
    n_d: \<open>no_dup (trail S)\<close> and
    fin_A[simp]: \<open>finite A\<close> and
    inv: \<open>inv S\<close> and
    decomp: \<open>all_decomposition_implies_m (clauses\<^sub>N\<^sub>O\<^sub>T S) (get_all_ann_decomposition (trail S))\<close>
  shows \<open>unsatisfiable (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T S))
    \<or> (lits_of_l (trail T) \<Turnstile>sextm clauses\<^sub>N\<^sub>O\<^sub>T S \<and> satisfiable (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T S)))\<close>
proof -
  have st: \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_restart\<^sup>*\<^sup>* (S, n) (T, m)\<close> and
    n_s: \<open>no_step cdcl\<^sub>N\<^sub>O\<^sub>T_restart (T, m)\<close>
    using full unfolding full_def by fast+
  have binv_T: \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T T) \<subseteq> atms_of_ms A\<close>
    \<open>atm_of ` lits_of_l (trail T) \<subseteq> atms_of_ms A\<close>
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_bound_inv[OF st, of A] inv n_d atms_S atms_trail
    by auto
  moreover have inv_T: \<open>no_dup (trail T)\<close> \<open>inv T\<close>
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_cdcl\<^sub>N\<^sub>O\<^sub>T_inv[OF st] inv n_d by auto
  moreover have \<open>all_decomposition_implies_m (clauses\<^sub>N\<^sub>O\<^sub>T T) (get_all_ann_decomposition (trail T))\<close>
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_restart_all_decomposition_implies[OF st] inv n_d
    decomp by auto
  ultimately have T: \<open>unsatisfiable (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T T))
    \<or> (trail T \<Turnstile>asm clauses\<^sub>N\<^sub>O\<^sub>T T \<and> satisfiable (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T T)))\<close>
    using no_step_cdcl\<^sub>N\<^sub>O\<^sub>T_restart_no_step_cdcl\<^sub>N\<^sub>O\<^sub>T[of \<open>(T, m)\<close> A] n_s
    cdcl\<^sub>N\<^sub>O\<^sub>T_final_state[of T A] unfolding cdcl\<^sub>N\<^sub>O\<^sub>T_NOT_all_inv_def by auto
  have eq_sat_S_T:\<open>\<And>I. I \<Turnstile>sextm clauses\<^sub>N\<^sub>O\<^sub>T S \<longleftrightarrow> I \<Turnstile>sextm clauses\<^sub>N\<^sub>O\<^sub>T T\<close>
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_restart_sat_ext_iff[OF st] inv n_d atms_S
        atms_trail by auto
  have cons_T: \<open>consistent_interp (lits_of_l (trail T))\<close>
    using inv_T(1) distinct_consistent_interp by blast
  consider
      (unsat) \<open>unsatisfiable (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T T))\<close>
    | (sat) \<open>trail T \<Turnstile>asm clauses\<^sub>N\<^sub>O\<^sub>T T\<close> and \<open>satisfiable (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T T))\<close>
    using T by blast
  then show ?thesis
    proof cases
      case unsat
      then have \<open>unsatisfiable (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T S))\<close>
        using eq_sat_S_T consistent_true_clss_ext_satisfiable true_clss_imp_true_cls_ext
        unfolding satisfiable_def by blast
      then show ?thesis by fast
    next
      case sat
      then have \<open>lits_of_l (trail T) \<Turnstile>sextm clauses\<^sub>N\<^sub>O\<^sub>T S\<close>
        using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_restart_sat_ext_iff[OF st] inv n_d atms_S
        atms_trail by (auto simp: true_clss_imp_true_cls_ext true_annots_true_cls)
      moreover then have \<open>satisfiable (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T S))\<close>
          using cons_T consistent_true_clss_ext_satisfiable by blast
      ultimately show ?thesis by blast
    qed
qed
end \<comment> \<open>End of the locale @{locale cdcl\<^sub>N\<^sub>O\<^sub>T_with_backtrack_and_restarts}.\<close>

text \<open>The restart does only reset the trail, contrary to Weidenbach's version where
  forget and restart are always combined. But there is a forget rule.\<close>
locale cdcl\<^sub>N\<^sub>O\<^sub>T_merge_bj_learn_with_backtrack_restarts =
  cdcl\<^sub>N\<^sub>O\<^sub>T_merge_bj_learn trail clauses\<^sub>N\<^sub>O\<^sub>T prepend_trail tl_trail add_cls\<^sub>N\<^sub>O\<^sub>T remove_cls\<^sub>N\<^sub>O\<^sub>T
    decide_conds propagate_conds forget_conds
    \<open>\<lambda>C C' L' S T. distinct_mset C' \<and> L' \<notin># C' \<and> backjump_l_cond C C' L' S T\<close> inv
  for
    trail :: \<open>'st \<Rightarrow> ('v, unit) ann_lits\<close> and
    clauses\<^sub>N\<^sub>O\<^sub>T :: \<open>'st \<Rightarrow> 'v clauses\<close> and
    prepend_trail :: \<open>('v, unit) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    tl_trail :: \<open>'st \<Rightarrow>'st\<close> and
    add_cls\<^sub>N\<^sub>O\<^sub>T :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    remove_cls\<^sub>N\<^sub>O\<^sub>T :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    decide_conds :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> and
    propagate_conds :: \<open>('v, unit) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st \<Rightarrow> bool\<close> and
    inv :: \<open>'st \<Rightarrow> bool\<close> and
    forget_conds :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> bool\<close> and
    backjump_l_cond :: \<open>'v clause \<Rightarrow> 'v clause \<Rightarrow> 'v literal \<Rightarrow> 'st \<Rightarrow> 'st \<Rightarrow> bool\<close>
    +
  fixes f :: \<open>nat \<Rightarrow> nat\<close>
  assumes
    unbounded: \<open>unbounded f\<close> and f_ge_1: \<open>\<And>n. n \<ge> 1 \<Longrightarrow> f n \<ge> 1\<close> and
    inv_restart:\<open>\<And>S T. inv S \<Longrightarrow> T \<sim> reduce_trail_to\<^sub>N\<^sub>O\<^sub>T [] S \<Longrightarrow> inv T\<close>
begin

definition not_simplified_cls :: \<open>'b clause multiset \<Rightarrow> 'b clauses\<close>
where
\<open>not_simplified_cls A \<equiv> {#C \<in># A. C \<notin> simple_clss (atms_of_mm A)#}\<close>

lemma not_simplified_cls_tautology_distinct_mset:
  \<open>not_simplified_cls A = {#C \<in># A. tautology C \<or> \<not>distinct_mset C#}\<close>
  unfolding not_simplified_cls_def by (rule filter_mset_cong) (auto simp: simple_clss_def)

lemma simple_clss_or_not_simplified_cls:
  assumes \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<subseteq> atms_of_ms A\<close> and
    \<open>x \<in># clauses\<^sub>N\<^sub>O\<^sub>T S\<close> and \<open>finite A\<close>
  shows \<open>x \<in> simple_clss (atms_of_ms A) \<or> x \<in># not_simplified_cls (clauses\<^sub>N\<^sub>O\<^sub>T S)\<close>
proof -
  consider
      (simpl) \<open>\<not>tautology x\<close> and \<open>distinct_mset x\<close>
    | (n_simp) \<open>tautology x \<or> \<not>distinct_mset x\<close>
    by auto
  then show ?thesis
    proof cases
      case simpl
      then have \<open>x \<in> simple_clss (atms_of_ms A)\<close>
        by (meson assms atms_of_atms_of_ms_mono atms_of_ms_finite simple_clss_mono
          distinct_mset_not_tautology_implies_in_simple_clss finite_subset
          subsetCE)
      then show ?thesis by blast
    next
      case n_simp
      then have \<open>x \<in># not_simplified_cls (clauses\<^sub>N\<^sub>O\<^sub>T S)\<close>
        using \<open>x \<in># clauses\<^sub>N\<^sub>O\<^sub>T S\<close> unfolding not_simplified_cls_tautology_distinct_mset by auto
      then show ?thesis by blast
    qed
qed

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_clauses_bound:
  assumes
    \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn S T\<close> and
    inv: \<open>inv S\<close> and
    atms_clss: \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<subseteq> atms_of_ms A\<close> and
    atms_trail: \<open>atm_of `(lits_of_l (trail S)) \<subseteq> atms_of_ms A\<close> and
    fin_A[simp]: \<open>finite A\<close>
  shows \<open>set_mset (clauses\<^sub>N\<^sub>O\<^sub>T T) \<subseteq> set_mset (not_simplified_cls (clauses\<^sub>N\<^sub>O\<^sub>T S))
    \<union> simple_clss (atms_of_ms A)\<close>
  using assms(1-4)
proof (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn.induct)
  case cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_decide\<^sub>N\<^sub>O\<^sub>T
  then show ?case using dpll_bj_clauses by (force dest!: simple_clss_or_not_simplified_cls)
next
  case cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_propagate\<^sub>N\<^sub>O\<^sub>T
  then show ?case using dpll_bj_clauses by (force dest!: simple_clss_or_not_simplified_cls)
next
  case cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_forget\<^sub>N\<^sub>O\<^sub>T
  then show ?case using clauses_remove_cls\<^sub>N\<^sub>O\<^sub>T unfolding state_eq\<^sub>N\<^sub>O\<^sub>T_def
    by (force elim!: forget\<^sub>N\<^sub>O\<^sub>TE dest: simple_clss_or_not_simplified_cls)
next
  case (cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_backjump_l T) note bj = this(1) and inv = this(2) and
    atms_clss = this(3) and atms_trail = this(4)

  have st: \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn\<^sup>*\<^sup>* S T\<close>
    using bj inv cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn.simps by blast+
  have \<open>atm_of `(lits_of_l (trail T)) \<subseteq> atms_of_ms A\<close> and \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T T) \<subseteq> atms_of_ms A\<close>
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_trail_clauses_bound[OF st] inv atms_trail atms_clss
    by auto

  obtain F' K F L l C' C D where
    tr_S: \<open>trail S = F' @ Decided K # F\<close> and
    T: \<open>T \<sim> prepend_trail (Propagated L l) (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F (add_cls\<^sub>N\<^sub>O\<^sub>T D S))\<close> and
    \<open>C \<in># clauses\<^sub>N\<^sub>O\<^sub>T S\<close> and
    \<open>trail S \<Turnstile>as CNot C\<close> and
    undef: \<open>undefined_lit F L\<close> and
    \<open>clauses\<^sub>N\<^sub>O\<^sub>T S \<Turnstile>pm add_mset L C'\<close> and
    \<open>F \<Turnstile>as CNot C'\<close> and
    D: \<open>D = add_mset L C'\<close> and
    dist: \<open>distinct_mset (add_mset L C')\<close> and
    tauto: \<open>\<not> tautology (add_mset L C')\<close> and
    \<open>backjump_l_cond C C' L S T\<close>
    using \<open>backjump_l S T\<close> apply (elim backjump_lE) by auto

  have \<open>atms_of C' \<subseteq> atm_of ` (lits_of_l F)\<close>
    using \<open>F \<Turnstile>as CNot C'\<close> by (simp add: atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set
      atms_of_def image_subset_iff in_CNot_implies_uminus(2))
  then have \<open>atms_of (C'+{#L#}) \<subseteq> atms_of_ms A\<close>
    using T \<open>atm_of ` lits_of_l (trail T) \<subseteq> atms_of_ms A\<close> tr_S undef by auto
  then have \<open>simple_clss (atms_of (add_mset L C')) \<subseteq> simple_clss (atms_of_ms A)\<close>
    apply - by (rule simple_clss_mono) (simp_all)
  then have \<open>add_mset L C' \<in> simple_clss (atms_of_ms A)\<close>
    using distinct_mset_not_tautology_implies_in_simple_clss[OF dist tauto]
    by auto
  then show ?case
    using T inv atms_clss undef tr_S D by (force dest!: simple_clss_or_not_simplified_cls)
qed

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_not_simplified_decreasing:
  assumes \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn S T\<close>
  shows \<open>not_simplified_cls (clauses\<^sub>N\<^sub>O\<^sub>T T) \<subseteq># not_simplified_cls (clauses\<^sub>N\<^sub>O\<^sub>T S)\<close>
  using assms apply induction
  prefer 4
  unfolding not_simplified_cls_tautology_distinct_mset apply (auto elim!: backjump_lE forget\<^sub>N\<^sub>O\<^sub>TE)[3]
  by (elim backjump_lE) auto

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_not_simplified_decreasing:
  assumes \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn\<^sup>*\<^sup>* S T\<close>
  shows \<open>not_simplified_cls (clauses\<^sub>N\<^sub>O\<^sub>T T) \<subseteq># not_simplified_cls (clauses\<^sub>N\<^sub>O\<^sub>T S)\<close>
  using assms apply induction
    apply simp
   by (drule cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_not_simplified_decreasing) auto

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_clauses_bound:
  assumes
    \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn\<^sup>*\<^sup>* S T\<close> and
    \<open>inv S\<close> and
    \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<subseteq> atms_of_ms A\<close> and
    \<open>atm_of `(lits_of_l (trail S)) \<subseteq> atms_of_ms A\<close> and
    finite[simp]: \<open>finite A\<close>
  shows \<open>set_mset (clauses\<^sub>N\<^sub>O\<^sub>T T) \<subseteq> set_mset (not_simplified_cls (clauses\<^sub>N\<^sub>O\<^sub>T S))
    \<union> simple_clss (atms_of_ms A)\<close>
  using assms(1-4)
proof induction
  case base
  then show ?case by (auto dest!: simple_clss_or_not_simplified_cls)
next
  case (step T U) note st = this(1) and cdcl\<^sub>N\<^sub>O\<^sub>T = this(2) and IH = this(3)[OF this(4-6)] and
    inv = this(4) and atms_clss_S = this(5) and atms_trail_S = this(6)
  have st': \<open>cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T\<close>
    using inv rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_is_rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_and_inv st by blast
  have \<open>inv T\<close>
    using inv rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_inv st by blast
  moreover
    have \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T T) \<subseteq> atms_of_ms A\<close> and
      \<open>atm_of ` lits_of_l (trail T) \<subseteq> atms_of_ms A\<close>
      using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_trail_clauses_bound[OF st] inv atms_clss_S
        atms_trail_S by blast+
  ultimately have \<open>set_mset (clauses\<^sub>N\<^sub>O\<^sub>T U)
    \<subseteq> set_mset (not_simplified_cls (clauses\<^sub>N\<^sub>O\<^sub>T T)) \<union> simple_clss (atms_of_ms A)\<close>
    using cdcl\<^sub>N\<^sub>O\<^sub>T finite cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_clauses_bound
    by (auto intro!: cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_clauses_bound)
  moreover have \<open>set_mset (not_simplified_cls (clauses\<^sub>N\<^sub>O\<^sub>T T))
    \<subseteq> set_mset (not_simplified_cls (clauses\<^sub>N\<^sub>O\<^sub>T S))\<close>
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_not_simplified_decreasing[OF st] by auto
  ultimately show ?case using IH inv atms_clss_S
    by (auto dest!: simple_clss_or_not_simplified_cls)
qed

abbreviation \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound where
\<open>\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound A T \<equiv> ((2+card (atms_of_ms A)) ^ (1+card (atms_of_ms A))) * 2
     + card (set_mset (not_simplified_cls(clauses\<^sub>N\<^sub>O\<^sub>T T)))
     + 3 ^ card (atms_of_ms A)\<close>

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_clauses_bound_card:
  assumes
    \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn\<^sup>*\<^sup>* S T\<close> and
    \<open>inv S\<close> and
    \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<subseteq> atms_of_ms A\<close> and
    \<open>atm_of `(lits_of_l (trail S)) \<subseteq> atms_of_ms A\<close> and
    finite: \<open>finite A\<close>
  shows \<open>\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_merged A T \<le> \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound A S\<close>
proof -
  have \<open>set_mset (clauses\<^sub>N\<^sub>O\<^sub>T T) \<subseteq> set_mset (not_simplified_cls(clauses\<^sub>N\<^sub>O\<^sub>T S))
    \<union> simple_clss (atms_of_ms A)\<close>
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_clauses_bound[OF assms] .
  moreover have \<open>card (set_mset (not_simplified_cls(clauses\<^sub>N\<^sub>O\<^sub>T S))
      \<union> simple_clss (atms_of_ms A))
    \<le> card (set_mset (not_simplified_cls(clauses\<^sub>N\<^sub>O\<^sub>T S))) + 3 ^ card (atms_of_ms A)\<close>
    by (meson Nat.le_trans atms_of_ms_finite simple_clss_card card_Un_le finite
      nat_add_left_cancel_le)
  ultimately have \<open>card (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T T))
    \<le> card (set_mset (not_simplified_cls(clauses\<^sub>N\<^sub>O\<^sub>T S))) + 3 ^ card (atms_of_ms A)\<close>
    by (meson Nat.le_trans atms_of_ms_finite simple_clss_finite card_mono
      finite_UnI finite_set_mset local.finite)
  moreover have \<open>((2 + card (atms_of_ms A)) ^ (1 + card (atms_of_ms A)) - \<mu>\<^sub>C' A T) * 2
    \<le> (2 + card (atms_of_ms A)) ^ (1 + card (atms_of_ms A)) * 2\<close>
    by auto
  ultimately show ?thesis unfolding \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_merged_def by auto
qed

sublocale cdcl\<^sub>N\<^sub>O\<^sub>T_increasing_restarts_ops \<open>\<lambda>S T. T \<sim> reduce_trail_to\<^sub>N\<^sub>O\<^sub>T ([]::'a list) S\<close>
   cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn f
   (* bound_inv *)\<open>\<lambda>A S. atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<subseteq> atms_of_ms A
     \<and> atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A \<and> finite A\<close>
   \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_merged
   (* inv *) \<open>\<lambda>S. inv S \<and> no_dup (trail S)\<close>
   \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound
   apply unfold_locales
              using unbounded apply simp
             using f_ge_1 apply force
            using cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_trail_clauses_bound apply meson
           apply (simp add: cdcl\<^sub>N\<^sub>O\<^sub>T_decreasing_measure')
          using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_clauses_bound_card apply blast
          apply (drule rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_not_simplified_decreasing)
          apply (auto simp: card_mono set_mset_mono)[]
       apply simp
      apply auto[]
     using cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_no_dup_inv cdcl_merged_inv apply blast
    apply (auto simp: inv_restart)[]
    done

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_restart_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_merged_le_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound:
  assumes
    \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_restart T V\<close>
    \<open>inv (fst T)\<close> and
    \<open>no_dup (trail (fst T))\<close> and
    \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T (fst T)) \<subseteq> atms_of_ms A\<close> and
    \<open>atm_of ` lits_of_l (trail (fst T)) \<subseteq> atms_of_ms A\<close> and
    \<open>finite A\<close>
  shows \<open>\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_merged A (fst V) \<le> \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound A (fst T)\<close>
  using assms
proof induction
  case (restart_full S T n)
  show ?case
    unfolding fst_conv
    apply (rule rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_clauses_bound_card)
    using restart_full unfolding full1_def by (force dest!: tranclp_into_rtranclp)+
next
  case (restart_step m S T n U) note st = this(1) and U = this(3) and inv = this(4) and
    n_d = this(5) and atms_clss = this(6) and atms_trail = this(7) and finite = this(8)
  then have st': \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn\<^sup>*\<^sup>* S T\<close>
    by (blast dest: relpowp_imp_rtranclp)
  then have st'': \<open>cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T\<close>
    using inv n_d apply - by (rule rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_is_rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T) auto
  have \<open>inv T\<close>
    apply (rule rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_inv)
      using inv st' n_d by auto
  then have \<open>inv U\<close>
    using U by (auto simp: inv_restart)
  have \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T T) \<subseteq> atms_of_ms A\<close>
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_trail_clauses_bound[OF st'] inv atms_clss atms_trail n_d
    by simp
  then have \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T U) \<subseteq> atms_of_ms A\<close>
    using U by simp
  have \<open>not_simplified_cls (clauses\<^sub>N\<^sub>O\<^sub>T U) \<subseteq># not_simplified_cls (clauses\<^sub>N\<^sub>O\<^sub>T T)\<close>
    using \<open>U \<sim> reduce_trail_to\<^sub>N\<^sub>O\<^sub>T [] T\<close> by auto
  moreover have \<open>not_simplified_cls (clauses\<^sub>N\<^sub>O\<^sub>T T) \<subseteq># not_simplified_cls (clauses\<^sub>N\<^sub>O\<^sub>T S)\<close>
    apply (rule rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_not_simplified_decreasing)
    using \<open>(cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn ^^ m) S T\<close> by (auto dest!: relpowp_imp_rtranclp)
  ultimately have U_S: \<open>not_simplified_cls (clauses\<^sub>N\<^sub>O\<^sub>T U) \<subseteq># not_simplified_cls (clauses\<^sub>N\<^sub>O\<^sub>T S)\<close>
    by auto

  have \<open>(set_mset (clauses\<^sub>N\<^sub>O\<^sub>T U))
    \<subseteq> set_mset (not_simplified_cls (clauses\<^sub>N\<^sub>O\<^sub>T U)) \<union> simple_clss (atms_of_ms A)\<close>
    apply (rule rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_clauses_bound)
         apply simp
        using \<open>inv U\<close> apply simp
       using \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T U) \<subseteq> atms_of_ms A\<close> apply simp
      using U apply simp
    using finite apply simp
    done
  then have f1: \<open>card (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T U)) \<le> card (set_mset (not_simplified_cls (clauses\<^sub>N\<^sub>O\<^sub>T U))
    \<union> simple_clss (atms_of_ms A))\<close>
    by (simp add: simple_clss_finite card_mono local.finite)

  moreover have \<open>set_mset (not_simplified_cls (clauses\<^sub>N\<^sub>O\<^sub>T U)) \<union> simple_clss (atms_of_ms A)
    \<subseteq> set_mset (not_simplified_cls (clauses\<^sub>N\<^sub>O\<^sub>T S)) \<union> simple_clss (atms_of_ms A)\<close>
    using U_S by auto
  then have f2:
    \<open>card (set_mset (not_simplified_cls (clauses\<^sub>N\<^sub>O\<^sub>T U)) \<union> simple_clss (atms_of_ms A))
      \<le> card (set_mset (not_simplified_cls (clauses\<^sub>N\<^sub>O\<^sub>T S)) \<union> simple_clss (atms_of_ms A))\<close>
    by (simp add: simple_clss_finite card_mono local.finite)

  moreover have \<open>card (set_mset (not_simplified_cls (clauses\<^sub>N\<^sub>O\<^sub>T S))
      \<union> simple_clss (atms_of_ms A))
    \<le> card (set_mset (not_simplified_cls (clauses\<^sub>N\<^sub>O\<^sub>T S))) + card (simple_clss (atms_of_ms A))\<close>
    using card_Un_le by blast
  moreover have \<open>card (simple_clss (atms_of_ms A)) \<le> 3 ^ card (atms_of_ms A)\<close>
    using atms_of_ms_finite simple_clss_card local.finite by blast
  ultimately have \<open>card (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T U))
    \<le> card (set_mset (not_simplified_cls (clauses\<^sub>N\<^sub>O\<^sub>T S))) + 3 ^ card (atms_of_ms A)\<close>
    by linarith
  then show ?case unfolding \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_merged_def by auto
qed

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_restart_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound_le_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound:
  assumes
    \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_restart T V\<close> and
    \<open>no_dup (trail (fst T))\<close> and
    \<open>inv (fst T)\<close> and
    fin: \<open>finite A\<close>
  shows \<open>\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound A (fst V) \<le> \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound A (fst T)\<close>
  using assms(1-3)
proof induction
  case (restart_full S T n)
  have \<open>not_simplified_cls (clauses\<^sub>N\<^sub>O\<^sub>T T) \<subseteq># not_simplified_cls (clauses\<^sub>N\<^sub>O\<^sub>T S)\<close>
    apply (rule rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_not_simplified_decreasing)
    using \<open>full1 cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn S T\<close> unfolding full1_def
    by (auto dest: tranclp_into_rtranclp)
  then show ?case by (auto simp: card_mono set_mset_mono)
next
  case (restart_step m S T n U) note st = this(1) and U = this(3) and n_d = this(4) and
    inv = this(5)
  then have st': \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn\<^sup>*\<^sup>* S T\<close>
    by (blast dest: relpowp_imp_rtranclp)
  then have st'': \<open>cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T\<close>
    using inv n_d apply - by (rule rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_is_rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T) auto
  have \<open>inv T\<close>
    apply (rule rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_inv)
      using inv st' n_d by auto
  then have \<open>inv U\<close>
    using U by (auto simp: inv_restart)
  have \<open>not_simplified_cls (clauses\<^sub>N\<^sub>O\<^sub>T U) \<subseteq># not_simplified_cls (clauses\<^sub>N\<^sub>O\<^sub>T T)\<close>
    using \<open>U \<sim> reduce_trail_to\<^sub>N\<^sub>O\<^sub>T [] T\<close> by auto
  moreover have \<open>not_simplified_cls (clauses\<^sub>N\<^sub>O\<^sub>T T) \<subseteq># not_simplified_cls (clauses\<^sub>N\<^sub>O\<^sub>T S)\<close>
    apply (rule rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_not_simplified_decreasing)
    using \<open>(cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn ^^ m) S T\<close> by (auto dest!: relpowp_imp_rtranclp)
  ultimately have U_S: \<open>not_simplified_cls (clauses\<^sub>N\<^sub>O\<^sub>T U) \<subseteq># not_simplified_cls (clauses\<^sub>N\<^sub>O\<^sub>T S)\<close>
    by auto
  then show ?case by (auto simp: card_mono set_mset_mono)
qed


sublocale cdcl\<^sub>N\<^sub>O\<^sub>T_increasing_restarts _ _ _ _ _ _ f
   \<open>\<lambda>S T. T \<sim> reduce_trail_to\<^sub>N\<^sub>O\<^sub>T ([]::'a list) S\<close>
   (* bound_inv *)\<open>\<lambda>A S. atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<subseteq> atms_of_ms A
     \<and> atm_of ` lits_of_l (trail S) \<subseteq> atms_of_ms A \<and> finite A\<close>
   \<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_merged cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn
   (* inv *) \<open>\<lambda>S. inv S \<and> no_dup (trail S)\<close>
   \<open>\<lambda>A T. ((2+card (atms_of_ms A)) ^ (1+card (atms_of_ms A))) * 2
     + card (set_mset (not_simplified_cls(clauses\<^sub>N\<^sub>O\<^sub>T T)))
     + 3 ^ card (atms_of_ms A)\<close>
   apply unfold_locales
     using cdcl\<^sub>N\<^sub>O\<^sub>T_restart_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_merged_le_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound apply force
    using cdcl\<^sub>N\<^sub>O\<^sub>T_restart_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound_le_\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_bound by fastforce

lemma true_clss_ext_decrease_right_insert: \<open>I \<Turnstile>sext insert C (set_mset M) \<Longrightarrow> I \<Turnstile>sextm M\<close>
  by (metis Diff_insert_absorb insert_absorb true_clss_ext_decrease_right_remove_r)

lemma true_clss_ext_decrease_add_implied:
  assumes \<open>M \<Turnstile>pm C\<close>
  shows \<open>I\<Turnstile>sext insert C (set_mset M) \<longleftrightarrow> I\<Turnstile>sextm M\<close>
proof -
  { fix J
    assume
      \<open>I \<Turnstile>sextm M\<close> and
      \<open>I \<subseteq> J\<close> and
      tot: \<open>total_over_m J (set_mset ({#C#} + M))\<close> and
      cons: \<open>consistent_interp J\<close>
    then have \<open>J \<Turnstile>sm M\<close> unfolding true_clss_ext_def by auto

    moreover
      with \<open>M \<Turnstile>pm C\<close> have \<open>J \<Turnstile> C\<close>
        using tot cons unfolding true_clss_cls_def by auto
    ultimately have \<open>J \<Turnstile>sm {#C#} + M\<close> by auto
  }
  then have H: \<open>I \<Turnstile>sextm M \<Longrightarrow> I \<Turnstile>sext insert C (set_mset M)\<close>
    unfolding true_clss_ext_def by auto
  then show ?thesis
    by (auto simp: true_clss_ext_decrease_right_insert)
qed

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_bj_sat_ext_iff:
  assumes \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn S T\<close> and inv: \<open>inv S\<close>
  shows \<open>I\<Turnstile>sextm clauses\<^sub>N\<^sub>O\<^sub>T S \<longleftrightarrow> I\<Turnstile>sextm clauses\<^sub>N\<^sub>O\<^sub>T T\<close>
  using assms
proof (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn.induct)
  case (cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_backjump_l T) note bj_l = this(1)
  obtain C' L D S' where
    learn: \<open>learn S' T\<close> and
    bj: \<open>backjump S S'\<close> and
    atms_C: \<open>atms_of (add_mset L C') \<subseteq> atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T S) \<union> atm_of ` (lits_of_l (trail S))\<close> and
    D: \<open>D = add_mset L C'\<close> and
    T: \<open>T \<sim> add_cls\<^sub>N\<^sub>O\<^sub>T D S'\<close> and
    clss_D: \<open>clauses\<^sub>N\<^sub>O\<^sub>T S \<Turnstile>pm D\<close>
    using bj_l inv backjump_l_backjump_learn [of S] by blast
  have [simp]: \<open>clauses\<^sub>N\<^sub>O\<^sub>T S' = clauses\<^sub>N\<^sub>O\<^sub>T S\<close>
    using bj by (auto elim: backjumpE)
  have \<open>(I \<Turnstile>sextm clauses\<^sub>N\<^sub>O\<^sub>T S) \<longleftrightarrow> (I \<Turnstile>sextm clauses\<^sub>N\<^sub>O\<^sub>T S')\<close>
    using bj bj_backjump dpll_bj_clauses inv by fastforce
  then show ?case
    using clss_D T by (auto simp: true_clss_ext_decrease_add_implied)
qed (auto simp: cdcl\<^sub>N\<^sub>O\<^sub>T_bj_sat_ext_iff
    dest!: dpll_bj.intros cdcl\<^sub>N\<^sub>O\<^sub>T.intros)

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_bj_sat_ext_iff:
  assumes \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn\<^sup>*\<^sup>* S T\<close>and \<open>inv S\<close>
  shows \<open>I\<Turnstile>sextm clauses\<^sub>N\<^sub>O\<^sub>T S \<longleftrightarrow> I\<Turnstile>sextm clauses\<^sub>N\<^sub>O\<^sub>T T\<close>
  using assms apply (induction rule: rtranclp_induct)
    apply simp
  using cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_bj_sat_ext_iff
    rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_is_rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_and_inv by blast

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_restart_eq_sat_iff:
  assumes
    \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_restart S T\<close> and
    inv: \<open>inv (fst S)\<close>
  shows \<open>I\<Turnstile>sextm clauses\<^sub>N\<^sub>O\<^sub>T (fst S) \<longleftrightarrow> I \<Turnstile>sextm clauses\<^sub>N\<^sub>O\<^sub>T (fst T)\<close>
  using assms
proof (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T_restart.induct)
  case (restart_full S T n)
  then have \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn\<^sup>*\<^sup>* S T \<close>
    by (simp add: tranclp_into_rtranclp full1_def)
  then show ?case
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_bj_sat_ext_iff restart_full.prems by auto
next
  case (restart_step m S T n U)
  then have \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn\<^sup>*\<^sup>* S T\<close>
    by (auto simp: tranclp_into_rtranclp full1_def dest!: relpowp_imp_rtranclp)
  then have \<open>I \<Turnstile>sextm clauses\<^sub>N\<^sub>O\<^sub>T S \<longleftrightarrow> I \<Turnstile>sextm clauses\<^sub>N\<^sub>O\<^sub>T T\<close>
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_bj_sat_ext_iff restart_step.prems by auto
  moreover have \<open>I \<Turnstile>sextm clauses\<^sub>N\<^sub>O\<^sub>T T \<longleftrightarrow> I \<Turnstile>sextm clauses\<^sub>N\<^sub>O\<^sub>T U\<close>
    using restart_step.hyps(3) by auto
  ultimately show ?case by auto
qed

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_restart_eq_sat_iff:
  assumes
    \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_restart\<^sup>*\<^sup>* S T\<close> and
    inv: \<open>inv (fst S)\<close> and n_d: \<open>no_dup(trail (fst S))\<close>
  shows \<open>I\<Turnstile>sextm clauses\<^sub>N\<^sub>O\<^sub>T (fst S) \<longleftrightarrow> I \<Turnstile>sextm clauses\<^sub>N\<^sub>O\<^sub>T (fst T)\<close>
  using assms(1)
proof (induction rule: rtranclp_induct)
  case base
  then show ?case by simp
next
  case (step T U) note st = this(1) and cdcl = this(2) and IH = this(3)
  have \<open>inv (fst T)\<close> and \<open>no_dup (trail (fst T))\<close>
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_cdcl\<^sub>N\<^sub>O\<^sub>T_inv using st inv n_d by blast+
  then have \<open>I\<Turnstile>sextm clauses\<^sub>N\<^sub>O\<^sub>T (fst T) \<longleftrightarrow> I \<Turnstile>sextm clauses\<^sub>N\<^sub>O\<^sub>T (fst U)\<close>
    using cdcl\<^sub>N\<^sub>O\<^sub>T_restart_eq_sat_iff cdcl by blast
  then show ?case using IH by blast
qed

lemma cdcl\<^sub>N\<^sub>O\<^sub>T_restart_all_decomposition_implies_m:
  assumes
    \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_restart S T\<close> and
    inv: \<open>inv (fst S)\<close> and n_d: \<open>no_dup(trail (fst S))\<close> and
    \<open>all_decomposition_implies_m (clauses\<^sub>N\<^sub>O\<^sub>T (fst S))
      (get_all_ann_decomposition (trail (fst S)))\<close>
  shows \<open>all_decomposition_implies_m (clauses\<^sub>N\<^sub>O\<^sub>T (fst T))
      (get_all_ann_decomposition (trail (fst T)))\<close>
  using assms
proof induction
  case (restart_full S T n) note full = this(1) and inv = this(2) and n_d = this(3) and
    decomp = this(4)
  have st: \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn\<^sup>*\<^sup>* S T\<close> and
    n_s: \<open>no_step cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn T\<close>
    using full unfolding full1_def by (fast dest: tranclp_into_rtranclp)+
  have st': \<open>cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T\<close>
    using inv rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_is_rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_and_inv st n_d by auto
  have \<open>inv T\<close>
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_cdcl\<^sub>N\<^sub>O\<^sub>T_inv[OF st] inv n_d by auto
  then show ?case
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_all_decomposition_implies[OF _ _ decomp] st inv by auto
next
  case (restart_step m S T n U) note st = this(1) and U = this(3) and inv = this(4) and
    n_d = this(5) and decomp = this(6)
  show ?case using U by auto
qed

lemma rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_restart_all_decomposition_implies_m:
  assumes
    \<open>cdcl\<^sub>N\<^sub>O\<^sub>T_restart\<^sup>*\<^sup>* S T\<close> and
    inv: \<open>inv (fst S)\<close> and n_d: \<open>no_dup(trail (fst S))\<close> and
    decomp: \<open>all_decomposition_implies_m (clauses\<^sub>N\<^sub>O\<^sub>T (fst S))
      (get_all_ann_decomposition (trail (fst S)))\<close>
  shows \<open>all_decomposition_implies_m (clauses\<^sub>N\<^sub>O\<^sub>T (fst T))
      (get_all_ann_decomposition (trail (fst T)))\<close>
  using assms
proof induction
  case base
  then show ?case using decomp by simp
next
  case (step T U) note st = this(1) and cdcl = this(2) and IH = this(3)[OF this(4-)] and
    inv = this(4) and n_d = this(5) and decomp = this(6)
  have \<open>inv (fst T)\<close> and \<open>no_dup (trail (fst T))\<close>
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_cdcl\<^sub>N\<^sub>O\<^sub>T_inv using st inv n_d by blast+
  then show ?case
    using cdcl\<^sub>N\<^sub>O\<^sub>T_restart_all_decomposition_implies_m[OF cdcl] IH by auto
qed

lemma full_cdcl\<^sub>N\<^sub>O\<^sub>T_restart_normal_form:
  assumes
    full: \<open>full cdcl\<^sub>N\<^sub>O\<^sub>T_restart S T\<close> and
    inv: \<open>inv (fst S)\<close> and n_d: \<open>no_dup(trail (fst S))\<close> and
    decomp: \<open>all_decomposition_implies_m (clauses\<^sub>N\<^sub>O\<^sub>T (fst S))
      (get_all_ann_decomposition (trail (fst S)))\<close> and
    atms_cls: \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T (fst S)) \<subseteq> atms_of_ms A\<close> and
    atms_trail: \<open>atm_of ` lits_of_l (trail (fst S)) \<subseteq> atms_of_ms A\<close> and
    fin: \<open>finite A\<close>
  shows \<open>unsatisfiable (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T (fst S)))
    \<or> lits_of_l (trail (fst T)) \<Turnstile>sextm clauses\<^sub>N\<^sub>O\<^sub>T (fst S) \<and>
       satisfiable (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T (fst S)))\<close>
proof -
  have inv_T: \<open>inv (fst T)\<close> and n_d_T: \<open>no_dup (trail (fst T))\<close>
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_cdcl\<^sub>N\<^sub>O\<^sub>T_inv using full inv n_d unfolding full_def by blast+
  moreover have
    atms_cls_T: \<open>atms_of_mm (clauses\<^sub>N\<^sub>O\<^sub>T (fst T)) \<subseteq> atms_of_ms A\<close> and
    atms_trail_T: \<open>atm_of ` lits_of_l (trail (fst T)) \<subseteq> atms_of_ms A\<close>
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_with_restart_bound_inv[of S T A] full atms_cls atms_trail fin inv n_d
    unfolding full_def by blast+
  ultimately have \<open>no_step cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn (fst T)\<close>
    apply -
    apply (rule no_step_cdcl\<^sub>N\<^sub>O\<^sub>T_restart_no_step_cdcl\<^sub>N\<^sub>O\<^sub>T[of _ A])
       using full unfolding full_def apply simp
      apply simp
    using fin apply simp
    done
  moreover have \<open>all_decomposition_implies_m (clauses\<^sub>N\<^sub>O\<^sub>T (fst T))
    (get_all_ann_decomposition (trail (fst T)))\<close>
    using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_restart_all_decomposition_implies_m[of S T] inv n_d decomp
    full unfolding full_def by auto
  ultimately have \<open>unsatisfiable (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T (fst T)))
    \<or> trail (fst T) \<Turnstile>asm clauses\<^sub>N\<^sub>O\<^sub>T (fst T) \<and> satisfiable (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T (fst T)))\<close>
    apply -
    apply (rule cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_final_state)
    using atms_cls_T atms_trail_T fin n_d_T fin inv_T by blast+
  then consider
      (unsat) \<open>unsatisfiable (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T (fst T)))\<close>
    | (sat) \<open>trail (fst T) \<Turnstile>asm clauses\<^sub>N\<^sub>O\<^sub>T (fst T)\<close> and \<open>satisfiable (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T (fst T)))\<close>
    by auto
  then show \<open>unsatisfiable (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T (fst S)))
    \<or> lits_of_l (trail (fst T)) \<Turnstile>sextm clauses\<^sub>N\<^sub>O\<^sub>T (fst S) \<and>
       satisfiable (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T (fst S)))\<close>
    proof cases
      case unsat
      then have \<open>unsatisfiable (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T (fst S)))\<close>
        unfolding satisfiable_def apply auto
        using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_restart_eq_sat_iff[of S T ] full inv n_d
        consistent_true_clss_ext_satisfiable true_clss_imp_true_cls_ext
        unfolding satisfiable_def full_def by blast
      then show ?thesis by blast
    next
      case sat
      then have \<open>lits_of_l (trail (fst T)) \<Turnstile>sextm clauses\<^sub>N\<^sub>O\<^sub>T (fst T)\<close>
        using true_clss_imp_true_cls_ext by (auto simp: true_annots_true_cls)
      then have \<open>lits_of_l (trail (fst T)) \<Turnstile>sextm clauses\<^sub>N\<^sub>O\<^sub>T (fst S)\<close>
        using rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_restart_eq_sat_iff[of S T] full inv n_d unfolding full_def by blast
      moreover then have \<open>satisfiable (set_mset (clauses\<^sub>N\<^sub>O\<^sub>T (fst S)))\<close>
        using consistent_true_clss_ext_satisfiable distinct_consistent_interp n_d_T by fast
      ultimately show ?thesis by fast
    qed
qed

corollary full_cdcl\<^sub>N\<^sub>O\<^sub>T_restart_normal_form_init_state:
  assumes
    init_state: \<open>trail S = []\<close> \<open>clauses\<^sub>N\<^sub>O\<^sub>T S = N\<close> and
    full: \<open>full cdcl\<^sub>N\<^sub>O\<^sub>T_restart (S, 0) T\<close> and
    inv: \<open>inv S\<close>
  shows \<open>unsatisfiable (set_mset N)
    \<or> lits_of_l (trail (fst T)) \<Turnstile>sextm N \<and> satisfiable (set_mset N)\<close>
  using full_cdcl\<^sub>N\<^sub>O\<^sub>T_restart_normal_form[of \<open>(S, 0)\<close> T] assms by auto

end \<comment> \<open>End of locale @{locale cdcl\<^sub>N\<^sub>O\<^sub>T_merge_bj_learn_with_backtrack_restarts}.\<close>

end
