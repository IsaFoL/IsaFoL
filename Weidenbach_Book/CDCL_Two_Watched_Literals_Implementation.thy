(*  Title: Implementation of CDCL with Two Watched Literals
    Author: Mathias Fleury <mathias.fleury@mpi-inf.mpg.de>
*)

subsection \<open>Implementation for 2 Watched-Literals\<close>

theory CDCL_Two_Watched_Literals_Implementation
imports CDCL_W_Abstract_State
begin
text \<open>The difference between an implementation and the core described in the previous sections are
  the following:
  \<^item> the candidates are cached while updating the data structure.
  \<^item> instead of updating with respect to the trail only, we update with respect to the trail \<^emph>\<open>and\<close>
  the candidates (referred as propagate queue later).\<close>
text \<open>The latter change means that we do not do the propagation as single steps where the state
  well-founded as described in the previous paragraph, but we do all the propagation and identify
  the propagation \<^emph>\<open>before\<close> the invariants hold again.

  The general idea is the following:
  \<^enum> Build a ``propagate'' queue and a conflict clause.
  \<^enum> While updating the data-structure: if you find a conflicting clause, update the conflict
  clause. Otherwise prepend the propagated clause.
  \<^enum> While updating, when looking for conflicts and propagation, work with respect to the
  trail of the state and the propagate queue (and not only the trail of the state).
  \<^enum> As long as the propagate queue is not empty, dequeue the first element, push it on the
  trail (with the @{const conflict_driven_clause_learning\<^sub>W.propagate} rule), propagate, and update
  the data-structure.
  \<^enum> If a conflict has been found such that it is entailed by the trail only (i.e.\ without
  the propagate queue), then apply the @{const conflict_driven_clause_learning\<^sub>W.conflict} rule.\<close>
text \<open>It is important to remember that a conflicting clause with respect to the trail and the queue
  might not be the earliest conflicting clause, meaning that the proof of non-redundancy should not
  work anymore.

  However, once a conflict has been found, we can stop adding literals to the queue: we just have to
  finish updating the data-structure (both to keep the invariant and find a potentially better
  conflict). A conflict is better when it involves less literals, i.e.\ less propagations are needed
  before finding the conflict.\<close>
(* datatype 'v candidate =
  Prop_Or_Conf
    (prop_queue: "('v literal \<times> 'v literal list twl_clause) list")
    (conflict: "'v twl_clause option") *)

datatype 'v twl_clause =
  TWL_Clause (watched: 'v) (unwatched: 'v)

fun clause :: "'a twl_clause \<Rightarrow> 'a :: {plus}"  where
"clause (TWL_Clause W UW) = W + UW"

locale abstract_clause_representation_ops =
  fixes
    lit_lookup :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'v literal option" and
    lit_keys :: "'cls \<Rightarrow> 'lit multiset" and

    twl_cls :: "'cls \<Rightarrow> 'lit multiset twl_clause" and
    swap_lit :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'lit \<Rightarrow> 'cls" and
    it_of_other_watched :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'lit option" and
    cls_ot_twl_list :: "'v literal list twl_clause \<Rightarrow> 'cls"
begin

abbreviation twl_clause :: "'cls \<Rightarrow> 'v literal multiset twl_clause" where
"twl_clause C \<equiv> map_twl_clause (image_mset (\<lambda>L. the (lit_lookup C L))) (twl_cls C)"

abbreviation clause_of_cls :: "'cls \<Rightarrow> 'v clause" where
"clause_of_cls C \<equiv> clause (twl_clause C)"

end

locale abstract_clause_representation =
  abstract_clause_representation_ops lit_lookup lit_keys twl_cls swap_lit
    it_of_other_watched cls_ot_twl_list
  for
    lit_lookup :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'v literal option" and
    lit_keys :: "'cls \<Rightarrow> 'lit multiset" and

    twl_cls :: "'cls \<Rightarrow> 'lit multiset twl_clause" and
    swap_lit :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'lit \<Rightarrow> 'cls" and
    it_of_other_watched :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'lit option" and
    cls_ot_twl_list :: "'v literal list twl_clause \<Rightarrow> 'cls" +
  assumes
    distinct_lit_keys[simp]: "distinct_mset (lit_keys C)" and
    get_all_it: "i \<in># keys C \<longleftrightarrow> lit_lookup C i \<noteq> None" and
    swap_lit:
      "j \<in># watched (twl_cls C) \<Longrightarrow> k \<in># unwatched (twl_cls C) \<Longrightarrow>
        twl_cls (swap_lit C j k) =
          TWL_Clause
            ({#k#} + remove1_mset j (watched (twl_cls C)))
            ({#j#} + remove1_mset k (unwatched (twl_cls C)))" and

    it_of_other_watched:
      "lit_lookup C j \<noteq> None \<Longrightarrow> it_of_other_watched C j = Some k \<Longrightarrow>
         lit_lookup C k \<noteq> None \<and> k \<in># remove1_mset j (watched (twl_cls C))" and

    twl_cls_valid:
      "keys C = clause (twl_cls C)" and

    cls_ot_twl_list:
      "distinct (watched D @ unwatched D) \<Longrightarrow>
        twl_clause (cls_ot_twl_list D) = map_twl_clause mset D"
begin

end

locale abstract_clauses_representation =
  fixes
    cls_lookup :: "'clss \<Rightarrow> 'cls_it \<Rightarrow> 'cls option" and
    cls_keys :: "'clss \<Rightarrow> 'cls_it multiset" and
    clss_update :: "'clss \<Rightarrow> 'cls_it \<Rightarrow> 'cls \<Rightarrow> 'clss" and
    add_cls :: "'clss \<Rightarrow> 'cls \<Rightarrow> 'clss \<times> 'cls_it"
  assumes
    cls_keys_distinct[simp]: "distinct_mset (cls_keys Cs)" and
    cls_keys: "i \<in># cls_keys Cs \<longleftrightarrow> cls_lookup Cs i \<noteq> None" and
    clss_update:
      "cls_lookup Cs i \<noteq> None \<Longrightarrow> cls_lookup (clss_update Cs i C) = (cls_lookup Cs) (i := Some C)"
      and
    add_cls:
      "add_cls Cs C = (Cs', i) \<Longrightarrow> cls_lookup Cs' = (cls_lookup Cs) (i := Some C)"  and
    add_cls_new_keys:
      "add_cls Cs C = (Cs', i) \<Longrightarrow> i \<notin># cls_keys Cs"
begin

lemma add_cls_new_key:
  "add_cls Cs C = (Cs', i) \<Longrightarrow> i \<in># cls_keys Cs'"
  unfolding cls_keys by (simp add: add_cls)

abbreviation raw_clss :: "'clss \<Rightarrow> 'cls multiset" where
"raw_clss Cs \<equiv> image_mset (\<lambda>L. the (cls_lookup Cs L)) (cls_keys Cs)"

lemma cls_keys_clss_update[simp]:
  "cls_lookup Cs i \<noteq> None \<Longrightarrow> cls_keys (clss_update Cs i E) = cls_keys Cs"
  by (rule distinct_set_mset_eq) (auto simp: cls_keys clss_update split: if_splits)

end

locale abstract_clause_clauses_representation =
  abstract_clause_representation lit_lookup lit_keys twl_cls swap_lit
    it_of_other_watched cls_ot_twl_list +
  abstract_clauses_representation cls_lookup cls_keys clss_update add_cls
  for
    lit_lookup :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'v literal option" and
    lit_keys :: "'cls \<Rightarrow> 'lit multiset" and

    twl_cls :: "'cls \<Rightarrow> 'lit multiset twl_clause" and
    swap_lit :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'lit \<Rightarrow> 'cls" and
    it_of_other_watched :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'lit option" and

    cls_ot_twl_list :: "'v literal list twl_clause \<Rightarrow> 'cls" and
    cls_lookup :: "'clss \<Rightarrow> 'cls_it \<Rightarrow> 'cls option" and
    cls_keys :: "'clss \<Rightarrow> 'cls_it multiset" and
    clss_update :: "'clss \<Rightarrow> 'cls_it \<Rightarrow> 'cls \<Rightarrow> 'clss" and
    add_cls :: "'clss \<Rightarrow> 'cls \<Rightarrow> 'clss \<times> 'cls_it"
begin

definition clauses_of_clss :: "'clss \<Rightarrow> 'v literal multiset multiset" where
"clauses_of_clss N \<equiv> image_mset clause_of_cls (raw_clss N)"

text \<open>The following abbreviation are useful to write shorter formula. Kill?\<close>
definition the_lit_lookup :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'v literal" (infix "\<down>" 49) where
"C \<down> a \<equiv> the (lit_lookup C a)"

definition the_cls_lookup :: "'clss \<Rightarrow> 'cls_it \<Rightarrow> 'cls" (infix "\<Down>" 49) where
"C \<Down> a \<equiv> the (cls_lookup C a)"

definition valid_lit_lookup :: "'lit \<Rightarrow> 'cls \<Rightarrow> bool" (infix "\<in>\<down>" 49) where
"a \<in>\<down> Cs \<equiv> lit_lookup Cs a \<noteq> None"

definition valid_cls_lookup :: "'cls_it \<Rightarrow> 'clss \<Rightarrow> bool" (infix "\<in>\<Down>" 49) where
"a \<in>\<Down> Cs \<equiv> cls_lookup Cs a \<noteq> None"

end

locale abs_state\<^sub>W_clss_twl_ops =
  abstract_clause_clauses_representation
    lit_lookup lit_keys twl_cls swap_lit
    it_of_other_watched cls_ot_twl_list

    cls_lookup cls_keys clss_update add_cls
    +
  raw_cls mset_ccls
  for
    \<comment> \<open>Clause:\<close>
    lit_lookup :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'v literal option" and
    lit_keys :: "'cls \<Rightarrow> 'lit multiset" and

    twl_cls :: "'cls \<Rightarrow> 'lit multiset twl_clause" and
    swap_lit :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'lit \<Rightarrow> 'cls" and
    it_of_other_watched :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'lit option" and

    \<comment> \<open>Clauses\<close>
    cls_ot_twl_list :: "'v literal list twl_clause \<Rightarrow> 'cls" and
    cls_lookup :: "'clss \<Rightarrow> 'cls_it \<Rightarrow> 'cls option" and
    cls_keys :: "'clss \<Rightarrow> 'cls_it multiset" and
    clss_update :: "'clss \<Rightarrow> 'cls_it \<Rightarrow> 'cls \<Rightarrow> 'clss" and
    add_cls :: "'clss \<Rightarrow> 'cls \<Rightarrow> 'clss \<times> 'cls_it" and

    \<comment> \<open>Conflicting clause:\<close>
    mset_ccls :: "'ccls \<Rightarrow> 'v clause"
begin

fun mmset_of_mlit :: "'clss \<Rightarrow> ('v, 'cls_it) ann_lit \<Rightarrow> ('v, 'v clause) ann_lit"
  where
"mmset_of_mlit Cs (Propagated L C) = Propagated L (clause_of_cls (Cs \<Down> C))" |
"mmset_of_mlit _ (Decided L) = Decided L"

lemma lit_of_mmset_of_mlit[simp]:
  "lit_of (mmset_of_mlit Cs a) = lit_of a"
  by (cases a) auto

lemma lit_of_mmset_of_mlit_set_lit_of_l[simp]:
  "lit_of ` mmset_of_mlit Cs ` set M' = lits_of_l M'"
  by (induction M') auto

lemma map_mmset_of_mlit_true_annots_true_cls[simp]:
  "map (mmset_of_mlit Cs) M' \<Turnstile>as C \<longleftrightarrow> M' \<Turnstile>as C"
  by (simp add: true_annots_true_cls lits_of_def)

end


locale abs_state\<^sub>W_twl_ops =
  abs_state\<^sub>W_clss_twl_ops
    \<comment> \<open>functions for clauses: \<close>
    lit_lookup lit_keys twl_cls swap_lit
    it_of_other_watched cls_ot_twl_list

    cls_lookup cls_keys clss_update add_cls

    \<comment> \<open>functions for the conflicting clause:\<close>
    mset_ccls
  for
    \<comment> \<open>Clause:\<close>
    lit_lookup :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'v literal option" and
    lit_keys :: "'cls \<Rightarrow> 'lit multiset" and

    twl_cls :: "'cls \<Rightarrow> 'lit multiset twl_clause" and
    swap_lit :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'lit \<Rightarrow> 'cls" and
    it_of_other_watched :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'lit option" and

    \<comment> \<open>Clauses\<close>
    cls_ot_twl_list :: "'v literal list twl_clause \<Rightarrow> 'cls" and
    cls_lookup :: "'clss \<Rightarrow> 'cls_it \<Rightarrow> 'cls option" and
    cls_keys :: "'clss \<Rightarrow> 'cls_it multiset" and
    clss_update :: "'clss \<Rightarrow> 'cls_it \<Rightarrow> 'cls \<Rightarrow> 'clss" and
    add_cls :: "'clss \<Rightarrow> 'cls \<Rightarrow> 'clss \<times> 'cls_it" and

    \<comment> \<open>Conflicting clause:\<close>
    mset_ccls :: "'ccls \<Rightarrow> 'v clause" +
  fixes
    find_undef_in_unwatched :: "'st \<Rightarrow> 'cls \<Rightarrow> 'lit option" and
    conc_trail :: "'st \<Rightarrow> ('v, 'v clause) ann_lits" and
    hd_raw_conc_trail :: "'st \<Rightarrow> ('v, 'cls_it) ann_lit" and
    prop_queue :: "'st \<Rightarrow> ('v, 'v clause) ann_lits" and
    raw_clauses :: "'st \<Rightarrow> 'clss" and
    conc_backtrack_lvl :: "'st \<Rightarrow> nat" and
    raw_conc_conflicting :: "'st \<Rightarrow> 'ccls option" and

    conc_learned_clss :: "'st \<Rightarrow> 'v clauses" and

    cons_conc_trail :: "('v, 'cls_it) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    tl_conc_trail :: "'st \<Rightarrow> 'st" and
    reduce_conc_trail_to :: "('v, 'v clause) ann_lits \<Rightarrow> 'st \<Rightarrow> 'st" and

    cons_prop_queue :: "('v, 'cls_it) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    hd_prop_queue_to_trail :: "'st \<Rightarrow> 'st" and
    prop_queue_to_trail :: "'st \<Rightarrow> 'st" and

    add_conc_confl_to_learned_cls :: "'st \<Rightarrow> 'st" and
    conc_remove_cls :: "'cls \<Rightarrow> 'st \<Rightarrow> 'st" and

    update_conc_backtrack_lvl :: "nat \<Rightarrow> 'st \<Rightarrow> 'st" and

    mark_conflicting :: "'cls_it \<Rightarrow> 'st \<Rightarrow> 'st" and
    resolve_conflicting :: "'v literal \<Rightarrow> 'cls \<Rightarrow> 'st \<Rightarrow> 'st" and

    get_undecided_lit :: "'st \<Rightarrow> 'v literal option" and
    get_clause_watched_by :: "'st \<Rightarrow> 'v literal \<Rightarrow> 'cls_it list" and
    update_clause :: "'st \<Rightarrow> 'cls_it \<Rightarrow> 'cls \<Rightarrow> 'st" and

    conc_init_state :: "'clss \<Rightarrow> 'st" and
    restart_state :: "'st \<Rightarrow> 'st"
begin

definition full_trail :: "'st \<Rightarrow> ('v, 'v clause) ann_lits" where
"full_trail S = prop_queue S @ conc_trail S"

definition conc_clauses :: "'st \<Rightarrow> 'v clauses" where
"conc_clauses S \<equiv> clauses_of_clss (raw_clauses S)"

definition conc_init_clss  :: "'st \<Rightarrow> 'v literal multiset multiset" where
"conc_init_clss = (\<lambda>S. conc_clauses S - conc_learned_clss S)"

abbreviation conc_conflicting :: "'st \<Rightarrow> 'v clause option" where
"conc_conflicting \<equiv> \<lambda>S. map_option mset_ccls (raw_conc_conflicting S)"

definition state :: "'st \<Rightarrow> 'v cdcl\<^sub>W_mset" where
"state = (\<lambda>S. (full_trail S, conc_init_clss S, conc_learned_clss S, conc_backtrack_lvl S,
  conc_conflicting S))"

fun valid_annotation :: "'st \<Rightarrow> ('a, 'cls_it) ann_lit \<Rightarrow> bool" where
"valid_annotation S (Propagated _ E) \<longleftrightarrow> E \<in>\<Down> (raw_clauses S)" |
"valid_annotation S (Decided _) \<longleftrightarrow> True"

end


lemma image_mset_if_eq_index:
  "{#if x = i then P x else Q x. x \<in># M#} =
  {#Q x. x \<in># removeAll_mset i M#} + replicate_mset (count M i) (P i)" (is "?M M = _")
proof -
  have M: "M = filter_mset (op = i) M + filter_mset (op \<noteq> i) M"
    by (auto simp: multiset_eq_iff)
  have "?M M = ?M (filter_mset (op = i) M) + ?M (filter_mset (op \<noteq> i) M)"
     by (subst M) simp
  moreover have "?M (filter_mset (op = i) M) = replicate_mset (count M i) (P i)"
    by (simp add: filter_mset_eq)
  moreover have "?M (filter_mset (op \<noteq> i) M) = {#Q x. x \<in># removeAll_mset i M#}"
    apply (subst removeAll_mset_filter_mset)
    apply (rule image_mset_cong2)
    by auto
  ultimately show ?thesis
    by (auto simp: ac_simps not_in_iff)
qed

locale abs_state\<^sub>W_twl =
  abs_state\<^sub>W_twl_ops
    \<comment> \<open>functions for clauses: \<close>
    lit_lookup lit_keys twl_cls swap_lit
    it_of_other_watched cls_ot_twl_list

    cls_lookup cls_keys clss_update add_cls

    \<comment> \<open>functions for the conflicting clause:\<close>
    mset_ccls

    find_undef_in_unwatched

    conc_trail hd_raw_conc_trail prop_queue raw_clauses conc_backtrack_lvl raw_conc_conflicting

    conc_learned_clss

    cons_conc_trail tl_conc_trail reduce_conc_trail_to

    cons_prop_queue hd_prop_queue_to_trail prop_queue_to_trail

    add_conc_confl_to_learned_cls conc_remove_cls

    update_conc_backtrack_lvl mark_conflicting resolve_conflicting

    get_undecided_lit get_clause_watched_by update_clause

    conc_init_state restart_state

  for
    \<comment> \<open>Clause:\<close>
    lit_lookup :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'v literal option" and
    lit_keys :: "'cls \<Rightarrow> 'lit multiset" and

    twl_cls :: "'cls \<Rightarrow> 'lit multiset twl_clause" and
    swap_lit :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'lit \<Rightarrow> 'cls" and
    it_of_other_watched :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'lit option" and

    \<comment> \<open>Clauses\<close>
    cls_ot_twl_list :: "'v literal list twl_clause \<Rightarrow> 'cls" and
    cls_lookup :: "'clss \<Rightarrow> 'cls_it \<Rightarrow> 'cls option" and
    cls_keys :: "'clss \<Rightarrow> 'cls_it multiset" and
    clss_update :: "'clss \<Rightarrow> 'cls_it \<Rightarrow> 'cls \<Rightarrow> 'clss" and
    add_cls :: "'clss \<Rightarrow> 'cls \<Rightarrow> 'clss \<times> 'cls_it" and

    \<comment> \<open>Conflicting clause:\<close>
    mset_ccls :: "'ccls \<Rightarrow> 'v clause" and

    find_undef_in_unwatched :: "'st \<Rightarrow> 'cls \<Rightarrow> 'lit option" and

    conc_trail :: "'st \<Rightarrow> ('v, 'v clause) ann_lits" and
    hd_raw_conc_trail :: "'st \<Rightarrow> ('v, 'cls_it) ann_lit" and
    prop_queue :: "'st \<Rightarrow> ('v, 'v clause) ann_lits" and
    raw_clauses :: "'st \<Rightarrow> 'clss" and
    conc_backtrack_lvl :: "'st \<Rightarrow> nat" and
    raw_conc_conflicting :: "'st \<Rightarrow> 'ccls option" and

    conc_learned_clss :: "'st \<Rightarrow> 'v clauses" and

    cons_conc_trail :: "('v, 'cls_it) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    tl_conc_trail :: "'st \<Rightarrow> 'st" and
    reduce_conc_trail_to :: "('v, 'v clause) ann_lits \<Rightarrow> 'st \<Rightarrow> 'st" and

    cons_prop_queue :: "('v, 'cls_it) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    hd_prop_queue_to_trail :: "'st \<Rightarrow> 'st" and
    prop_queue_to_trail :: "'st \<Rightarrow> 'st" and

    add_conc_confl_to_learned_cls :: "'st \<Rightarrow> 'st" and
    conc_remove_cls :: "'cls \<Rightarrow> 'st \<Rightarrow> 'st" and

    update_conc_backtrack_lvl :: "nat \<Rightarrow> 'st \<Rightarrow> 'st" and

    mark_conflicting :: "'cls_it \<Rightarrow> 'st \<Rightarrow> 'st" and
    resolve_conflicting :: "'v literal \<Rightarrow> 'cls \<Rightarrow> 'st \<Rightarrow> 'st" and

    get_undecided_lit :: "'st \<Rightarrow> 'v literal option" and
    get_clause_watched_by :: "'st \<Rightarrow> 'v literal \<Rightarrow> 'cls_it list" and
    update_clause :: "'st \<Rightarrow> 'cls_it \<Rightarrow> 'cls \<Rightarrow> 'st" and

    conc_init_state :: "'clss \<Rightarrow> 'st" and
    restart_state :: "'st \<Rightarrow> 'st" +
  assumes
    state_cons_prop_queue:
      "undefined_lit (conc_trail T @ prop_queue T) (lit_of L) \<Longrightarrow>
        state (cons_prop_queue L T) = state T" and
    cons_prop_queue_prop_queue:
      "undefined_lit (conc_trail T @ prop_queue T) (lit_of L) \<Longrightarrow>
         prop_queue (cons_prop_queue L T) = mmset_of_mlit (raw_clauses T) L # prop_queue T" and
    hd_prop_queue_to_trail_state:
      "prop_queue T \<noteq> [] \<Longrightarrow>
        state T = (M, N, U, k, C) \<Longrightarrow>
        state (hd_prop_queue_to_trail T) =
           (hd (prop_queue T) # M, N, U, k, C)" and
    hd_prop_queue_to_trail:
      "prop_queue T \<noteq> [] \<Longrightarrow>
        prop_queue (hd_prop_queue_to_trail T) =
           tl (prop_queue T)" and
    prop_queue_to_trail_state:
      "state T = (M, N, U, k, C) \<Longrightarrow>
        state (prop_queue_to_trail T) = (prop_queue (prop_queue_to_trail T) @ M, N, U, k, C)" and
    prop_queue_to_trail:
      "prop_queue (prop_queue_to_trail T) = []" and

    get_undecided_lit_Some:
      "get_undecided_lit T = Some L' \<Longrightarrow> undefined_lit (conc_trail T) L' \<and>
        atm_of L' \<in> atms_of_mm (conc_clauses T)" and
    get_undecided_lit_None:
      "get_undecided_lit T = None \<longleftrightarrow>
         (\<forall>L'. atm_of L' \<in> atms_of_mm (conc_clauses T) \<longrightarrow> \<not>undefined_lit (conc_trail T) L')" and
    get_clause_watched_by:
      "i \<in> set (get_clause_watched_by T K) \<longleftrightarrow> K \<in># watched (twl_clause (raw_clauses T \<Down> i))" and
    get_clause_watched_by_distinct:
      "distinct (get_clause_watched_by T K)" and

    update_clause:
      "i \<in>\<Down> raw_clauses S \<Longrightarrow>
        raw_clauses (update_clause S i E) = clss_update (raw_clauses S) i E" and
    update_clause_state:
      "i \<in>\<Down> raw_clauses S \<Longrightarrow> state S = (M, N, U, k, C) \<Longrightarrow>
        state (update_clause S i E) = (M, conc_init_clss S, conc_learned_clss S, k, C)" and

    find_undef_in_unwatched_Some:
      "find_undef_in_unwatched S E = Some j \<Longrightarrow> j \<in>\<down> E \<and> undefined_lit (full_trail S) (E\<down>j) \<and>
        (E\<down>j) \<in># unwatched (twl_clause E)" and
    find_undef_in_unwatched_None:
      "find_undef_in_unwatched S E = None \<longleftrightarrow>
        (\<forall>j. j \<in>\<down> E \<longrightarrow> (E\<down>j) \<in># unwatched (twl_clause E) \<longrightarrow>
           \<not>undefined_lit (full_trail S) (E\<down>j))"
begin

lemma conc_clauses_update_clause:
  assumes
    i: "i \<in>\<Down> raw_clauses S"
  shows
    "conc_clauses (update_clause S i E) =
       remove1_mset (clause_of_cls (raw_clauses S \<Down> i)) (conc_clauses S) + {#clause_of_cls E#}"
     (is "?conc = ?r")
proof-
  have XX: "\<And>x. clause_of_cls (the (if x = i then Some E else cls_lookup (raw_clauses S) x)) =
    (if x = i then clause_of_cls E else clause_of_cls (the (cls_lookup (raw_clauses S) x)))"
     by (auto simp: update_clause[OF i] clss_update split: if_splits)
  have YY: "remove1_mset (clause_of_cls (raw_clauses S \<Down> i))
    {#clause_of_cls (the (cls_lookup (raw_clauses S) x)). x \<in># cls_keys (raw_clauses S)#} =
    {#clause_of_cls (the (cls_lookup (raw_clauses S) x)).
       x \<in># remove1_mset i (cls_keys (raw_clauses S))#}"
     apply (subst subseteq_image_mset_minus)
     using i by (auto simp: valid_cls_lookup_def cls_keys the_cls_lookup_def)

  have c: "count (cls_keys (raw_clauses S)) i = 1"
    by (meson cls_keys cls_keys_distinct distinct_mset_def i valid_cls_lookup_def)
  then have [simp]: "replicate_mset (count (cls_keys (raw_clauses S)) i) (clause_of_cls E) =
    {#clause_of_cls E#}"
    by simp
  show ?thesis
     using i unfolding conc_clauses_def clauses_of_clss_def valid_cls_lookup_def
     by (auto simp: update_clause[OF i] clss_update XX YY image_mset_if_eq_index
       distinct_mset_remove1_All)
qed

end

locale abs_conflict_driven_clause_learning\<^sub>W_clss =
  abs_state\<^sub>W_twl
     \<comment> \<open>functions for clauses: \<close>
    lit_lookup lit_keys twl_cls swap_lit
    it_of_other_watched cls_ot_twl_list

    cls_lookup cls_keys clss_update add_cls

    \<comment> \<open>functions for the conflicting clause:\<close>
    mset_ccls

    find_undef_in_unwatched

    conc_trail hd_raw_conc_trail prop_queue raw_clauses conc_backtrack_lvl raw_conc_conflicting

    conc_learned_clss

    cons_conc_trail tl_conc_trail reduce_conc_trail_to

    cons_prop_queue hd_prop_queue_to_trail prop_queue_to_trail

    add_conc_confl_to_learned_cls conc_remove_cls

    update_conc_backtrack_lvl mark_conflicting resolve_conflicting

    get_undecided_lit get_clause_watched_by update_clause

    conc_init_state restart_state

  for
    \<comment> \<open>Clause:\<close>
    lit_lookup :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'v literal option" and
    lit_keys :: "'cls \<Rightarrow> 'lit multiset" and

    twl_cls :: "'cls \<Rightarrow> 'lit multiset twl_clause" and
    swap_lit :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'lit \<Rightarrow> 'cls" and
    it_of_other_watched :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'lit option" and

    \<comment> \<open>Clauses\<close>
    cls_ot_twl_list :: "'v literal list twl_clause \<Rightarrow> 'cls" and
    cls_lookup :: "'clss \<Rightarrow> 'cls_it \<Rightarrow> 'cls option" and
    cls_keys :: "'clss \<Rightarrow> 'cls_it multiset" and
    clss_update :: "'clss \<Rightarrow> 'cls_it \<Rightarrow> 'cls \<Rightarrow> 'clss" and
    add_cls :: "'clss \<Rightarrow> 'cls \<Rightarrow> 'clss \<times> 'cls_it" and

    \<comment> \<open>Conflicting clause:\<close>
    mset_ccls :: "'ccls \<Rightarrow> 'v clause" and

    find_undef_in_unwatched :: "'st \<Rightarrow> 'cls \<Rightarrow> 'lit option" and

    conc_trail :: "'st \<Rightarrow> ('v, 'v clause) ann_lits" and
    hd_raw_conc_trail :: "'st \<Rightarrow> ('v, 'cls_it) ann_lit" and
    prop_queue :: "'st \<Rightarrow> ('v, 'v clause) ann_lits" and
    raw_clauses :: "'st \<Rightarrow> 'clss" and
    conc_backtrack_lvl :: "'st \<Rightarrow> nat" and
    raw_conc_conflicting :: "'st \<Rightarrow> 'ccls option" and

    conc_learned_clss :: "'st \<Rightarrow> 'v clauses" and

    cons_conc_trail :: "('v, 'cls_it) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    tl_conc_trail :: "'st \<Rightarrow> 'st" and
    reduce_conc_trail_to :: "('v, 'v clause) ann_lits \<Rightarrow> 'st \<Rightarrow> 'st" and

    cons_prop_queue :: "('v, 'cls_it) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    hd_prop_queue_to_trail :: "'st \<Rightarrow> 'st" and
    prop_queue_to_trail :: "'st \<Rightarrow> 'st" and

    add_conc_confl_to_learned_cls :: "'st \<Rightarrow> 'st" and
    conc_remove_cls :: "'cls \<Rightarrow> 'st \<Rightarrow> 'st" and

    update_conc_backtrack_lvl :: "nat \<Rightarrow> 'st \<Rightarrow> 'st" and

    mark_conflicting :: "'cls_it \<Rightarrow> 'st \<Rightarrow> 'st" and
    resolve_conflicting :: "'v literal \<Rightarrow> 'cls \<Rightarrow> 'st \<Rightarrow> 'st" and

    get_undecided_lit :: "'st \<Rightarrow> 'v literal option" and
    get_clause_watched_by :: "'st \<Rightarrow> 'v literal \<Rightarrow> 'cls_it list" and
    update_clause :: "'st \<Rightarrow> 'cls_it \<Rightarrow> 'cls \<Rightarrow> 'st" and

    conc_init_state :: "'clss \<Rightarrow> 'st" and
    restart_state :: "'st \<Rightarrow> 'st"
begin

fun update_clause2 where
"update_clause2 L S i =
  (case it_of_other_watched (raw_clauses S \<Down> i) L of
    None \<Rightarrow> S
  | Some L' \<Rightarrow>
    if ((raw_clauses S \<Down> i) \<down> L') \<in> lits_of_l (conc_trail S)
    then S
    else
      (case find_undef_in_unwatched S (raw_clauses S \<Down> i) of
        None \<Rightarrow> mark_conflicting i S
      | Some _ \<Rightarrow> S)
    )"

end


end