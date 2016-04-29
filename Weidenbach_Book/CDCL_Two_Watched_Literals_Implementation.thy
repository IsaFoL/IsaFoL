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

locale raw_clss_with_update =
  raw_clss get_lit mset_cls get_cls mset_clss
  for
    get_lit :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'v literal option" and
    mset_cls :: "'cls \<Rightarrow> 'v clause" and

    get_cls :: "'clss \<Rightarrow> 'cls_it \<Rightarrow> 'cls option" and
    mset_clss:: "'clss \<Rightarrow> 'cls multiset" +
  fixes
    twl_cls :: "'cls \<Rightarrow> 'v literal list twl_clause" and
    clss_update :: "'clss \<Rightarrow> 'cls_it \<Rightarrow> 'cls \<Rightarrow> 'clss" and
    swap_lit :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'lit \<Rightarrow> 'cls" and
    exists_in_unwatched :: "('lit \<Rightarrow> bool) \<Rightarrow> 'cls \<Rightarrow> 'lit option"
  assumes
    clause_twl_cls:
      "clause (twl_cls C) = mset_cls C" and
    clss_update:
      "i \<in>\<Down> Cs \<Longrightarrow> clss_cls (clss_update Cs i C) = (clss_cls Cs) (i := C)" and
    swap_lit:
      "j \<in>\<down> C \<Longrightarrow> k \<in>\<down> C \<Longrightarrow>
        twl_clause_to_mset (twl_cls (swap_lit C j k)) =
        TWL_Clause
          ({#C\<down>k#} + mset (remove1 (C\<down>j) (watched (twl_cls C))))
          ({#C\<down>j#} + mset (remove1 (C\<down>k) (watched (twl_cls C))))"
      and
    exists_Some:
      "exists_in_unwatched P C = Some j \<Longrightarrow> (P j \<and> j \<in>\<down> C \<and> (C \<down> j) \<in> set (unwatched (twl_cls C)))"
      and
    exists_None:
      "exists_in_unwatched P C = None \<longleftrightarrow>
        (\<forall>j. j \<in>\<down> C \<longrightarrow> (C \<down> j) \<in> set (unwatched (twl_cls C)) \<longrightarrow> \<not>P j)"
begin

end

locale abs_state\<^sub>W_clss_twl_ops =
  raw_clss_with_update
    get_lit mset_cls get_cls mset_clss
    twl_cls clss_update swap_lit exists_in_unwatched
    +
  raw_cls mset_ccls
  for
    \<comment> \<open>Clause:\<close>
    get_lit :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'v literal option" and
    mset_cls :: "'cls \<Rightarrow> 'v clause" and

    \<comment> \<open>Multiset of Clauses:\<close>
    get_cls :: "'clss \<Rightarrow> 'cls_it \<Rightarrow> 'cls option" and
    mset_clss:: "'clss \<Rightarrow> 'cls multiset" and

    twl_cls :: "'cls \<Rightarrow> 'v literal list twl_clause" and
    clss_update :: "'clss \<Rightarrow> 'cls_it \<Rightarrow> 'cls \<Rightarrow> 'clss" and
    swap_lit :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'lit \<Rightarrow> 'cls" and
    exists_in_unwatched :: "('lit \<Rightarrow> bool) \<Rightarrow> 'cls \<Rightarrow> 'lit option" and

    \<comment> \<open>Conflicting clause:\<close>
    mset_ccls :: "'ccls \<Rightarrow> 'v clause"
begin

fun mmset_of_mlit :: "'clss \<Rightarrow> ('v, 'cls_it) ann_lit \<Rightarrow> ('v, 'v clause) ann_lit"
  where
"mmset_of_mlit Cs (Propagated L C) = Propagated L (mset_cls (Cs \<Down> C))" |
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

definition clauses_of_clss where
"clauses_of_clss N \<equiv> image_mset mset_cls (mset_clss N)"

notation cls_lit (infix "\<down>" 49)
notation clss_cls (infix "\<Down>" 49)
notation in_cls (infix "\<in>\<down>" 49)
notation in_clss (infix "\<in>\<Down>" 49)

lemma clauses_of_clss_met_cls:
  "set_mset (clauses_of_clss Cs) = {mset_cls (Cs \<Down> i)|i. i \<in>\<Down> Cs}"
  unfolding clauses_of_clss_def clss_cls_def in_clss_def
  apply (auto dest!: in_mset_clss_exists_preimage)
  by (metis option.sel)

lemma finite_mset_cls: "finite {mset_cls (Cs \<Down> i)|i. i \<in>\<Down> Cs}"
  unfolding clauses_of_clss_met_cls[symmetric] by auto

lemma clauses_of_clss_mset_met_cls:
  assumes "distinct_mset (clauses_of_clss Cs)"
  shows "clauses_of_clss Cs = mset_set {mset_cls (Cs \<Down> i)|i. i \<in>\<Down> Cs}"
  using clauses_of_clss_met_cls distinct_mset_set_mset_ident[OF assms] by force

end


locale abs_state\<^sub>W_twl_ops =
  abs_state\<^sub>W_clss_twl_ops
    \<comment> \<open>functions for clauses: \<close>
    cls_lit mset_cls
    clss_cls mset_clss
    twl_cls clss_update swap_lit exists_in_unwatched

    \<comment> \<open>functions for the conflicting clause:\<close>
    mset_ccls
  for
    \<comment> \<open>Clause:\<close>
    cls_lit :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'v literal option" and
    mset_cls :: "'cls \<Rightarrow> 'v clause" and

    \<comment> \<open>Multiset of Clauses:\<close>
    clss_cls :: "'clss \<Rightarrow> 'cls_it \<Rightarrow> 'cls option" and
    mset_clss:: "'clss \<Rightarrow> 'cls multiset" and

    twl_cls :: "'cls \<Rightarrow> 'v literal list twl_clause" and
    clss_update :: "'clss \<Rightarrow> 'cls_it \<Rightarrow> 'cls \<Rightarrow> 'clss" and
    swap_lit :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'lit \<Rightarrow> 'cls" and
    exists_in_unwatched :: "('lit \<Rightarrow> bool) \<Rightarrow> 'cls \<Rightarrow> 'lit option" and

    \<comment> \<open>Conflicting clause:\<close>
    mset_ccls :: "'ccls \<Rightarrow> 'v clause" +
  fixes
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
"conc_clauses S \<equiv> image_mset mset_cls (mset_clss (raw_clauses S))"

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


locale abs_state\<^sub>W_twl =
  abs_state\<^sub>W_twl_ops
    cls_lit mset_cls
    clss_cls mset_clss
    twl_cls clss_update swap_lit exists_in_unwatched

    \<comment> \<open>functions for the conflicting clause:\<close>
    mset_ccls

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
    cls_lit :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'v literal option" and
    mset_cls :: "'cls \<Rightarrow> 'v clause" and

    \<comment> \<open>Multiset of Clauses:\<close>
    clss_cls :: "'clss \<Rightarrow> 'cls_it \<Rightarrow> 'cls option" and
    mset_clss:: "'clss \<Rightarrow> 'cls multiset" and

    twl_cls :: "'cls \<Rightarrow> 'v literal list twl_clause" and
    clss_update :: "'clss \<Rightarrow> 'cls_it \<Rightarrow> 'cls \<Rightarrow> 'clss" and
    swap_lit :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'lit \<Rightarrow> 'cls" and
    exists_in_unwatched :: "('lit \<Rightarrow> bool) \<Rightarrow> 'cls \<Rightarrow> 'lit option" and

    \<comment> \<open>Conflicting clause:\<close>
    mset_ccls :: "'ccls \<Rightarrow> 'v clause" and

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
      "i \<in> set (get_clause_watched_by T K) \<longleftrightarrow> K \<in> set (watched (twl_cls (raw_clauses T \<Down> i)))" and
    get_clause_watched_by_distinct:
      "distinct (get_clause_watched_by T K)" and
    update_clause:
      "i \<in>\<Down> raw_clauses S \<Longrightarrow>
        clss_cls (raw_clauses (update_clause S i E)) = (clss_cls (raw_clauses S)) (i := Some E)" and
    update_clause_state:
      "i \<in>\<Down> raw_clauses S \<Longrightarrow> state S = (M, N, U, k, C) \<Longrightarrow>
        state (update_clause S i E) = (M, conc_init_clss S, conc_learned_clss S, k, C)"
begin

lemma
  assumes
    "i \<in>\<Down> raw_clauses S"
  shows
    "conc_clauses (update S i E) =
       remove1_mset (mset_cls (raw_clauses S \<Down> i)) (conc_clauses S) + {#E#}"
    unfolding conc_clauses_def
    apply (subst update_clause)
    apply (simp add: update_clause assms)

end

locale abs_conflict_driven_clause_learning\<^sub>W_clss =
  twl_state\<^sub>W_clss
    \<comment> \<open>functions for clauses: \<close>
    cls_lit in_cls mset_cls
    clss_cls in_clss mset_clss

    \<comment> \<open>functions for the conflicting clause:\<close>
    mset_ccls

    twl_cls clss_update swap_lit  exists_in_unwatched
    \<comment> \<open>functions about the state:\<close>
      \<comment> \<open>getter:\<close>
    conc_trail hd_raw_conc_trail raw_clauses conc_backtrack_lvl
    raw_conc_conflicting conc_learned_clss
      \<comment> \<open>setter:\<close>
    cons_conc_trail tl_conc_trail add_conc_confl_to_learned_cls conc_remove_cls
    update_conc_backtrack_lvl
    mark_conflicting reduce_conc_trail_to resolve_conflicting

      \<comment> \<open>Some specific states:\<close>
    conc_init_state
    restart_state

      -- \<open>Additional functions:\<close>
        -- \<open>Propagate queue\<close>
    prop_queue
    cons_prop_queue
    hd_prop_queue_to_trail
    prop_queue_to_trail

        -- \<open>Not decided literals\<close>
    get_undecided_lit

        -- \<open>Watched clauses:\<close>
    get_clause_watched_by

    update_clause

  for
    \<comment> \<open>Clause:\<close>
    cls_lit :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'v literal" and
    in_cls :: "'lit \<Rightarrow> 'cls \<Rightarrow> bool" and
    mset_cls :: "'cls \<Rightarrow> 'v clause" and

    \<comment> \<open>Multiset of Clauses:\<close>
    clss_cls :: "'clss \<Rightarrow> 'cls_it \<Rightarrow> 'cls" and
    in_clss :: "'cls_it \<Rightarrow> 'clss \<Rightarrow> bool" and
    mset_clss:: "'clss \<Rightarrow> 'cls multiset" and

    \<comment> \<open>Conflicting clause:\<close>
    mset_ccls :: "'ccls \<Rightarrow> 'v clause" and

    \<comment> \<open>2 watched literals conversion:\<close>
    twl_cls :: "'cls \<Rightarrow> 'v literal list twl_clause" and
    clss_update :: "'clss \<Rightarrow> 'cls_it \<Rightarrow> 'cls \<Rightarrow> 'clss" and
    swap_lit :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'lit \<Rightarrow> 'cls" and
    exists_in_unwatched :: "('lit \<Rightarrow> bool) \<Rightarrow> 'cls \<Rightarrow> 'lit option" and
    conc_trail :: "'st \<Rightarrow> ('v, 'v clause) ann_lits" and
    hd_raw_conc_trail :: "'st \<Rightarrow> ('v, 'cls_it) ann_lit" and
    raw_clauses :: "'st \<Rightarrow> 'clss" and
    conc_backtrack_lvl :: "'st \<Rightarrow> nat" and
    raw_conc_conflicting :: "'st \<Rightarrow> 'ccls option" and

    conc_learned_clss :: "'st \<Rightarrow> 'v clauses" and

    cons_conc_trail :: "('v, 'cls_it) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    tl_conc_trail :: "'st \<Rightarrow> 'st" and
    add_conc_confl_to_learned_cls :: "'st \<Rightarrow> 'st" and
    conc_remove_cls :: "'cls \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_conc_backtrack_lvl :: "nat \<Rightarrow> 'st \<Rightarrow> 'st" and
    mark_conflicting :: "'cls_it \<Rightarrow> 'st \<Rightarrow> 'st" and
    reduce_conc_trail_to :: "('v, 'v clause) ann_lits \<Rightarrow> 'st \<Rightarrow> 'st" and
    resolve_conflicting :: "'v literal \<Rightarrow> 'cls \<Rightarrow> 'st \<Rightarrow> 'st" and

    conc_init_state :: "'clss \<Rightarrow> 'st" and
    restart_state :: "'st \<Rightarrow> 'st" and

    prop_queue :: "'st \<Rightarrow> ('v, 'v clause) ann_lits" and
    cons_prop_queue :: "('v, 'cls_it) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    hd_prop_queue_to_trail :: "'st \<Rightarrow> 'st" and
    prop_queue_to_trail :: "'st \<Rightarrow> 'st" and

    get_undecided_lit :: "'st \<Rightarrow> 'v literal option" and
    get_clause_watched_by :: "'st \<Rightarrow> 'v literal \<Rightarrow> 'cls_it list" and
    update_clause :: "'st \<Rightarrow> 'cls_it \<Rightarrow> 'cls \<Rightarrow> 'st"
begin

fun other_watched_lit  where
"other_watched_lit S i L =
  (case remove1 L (watched (twl_cls (raw_clauses S \<Down> i))) of
     [] \<Rightarrow> None
   | a # _ \<Rightarrow> Some a)"

fun update_clause where
"update_clause L S i =
  (case other_watched_lit S i L of
     None \<Rightarrow> S
   | Some L' \<Rightarrow>
     if L' \<in> lits_of_l (conc_trail S)
     then S
     else
       (case exists_in_unwatched
         (\<lambda>j. undefined_lit (conc_trail S) ((raw_clauses S \<Down> i) \<down> j)) (raw_clauses S \<Down> i) of
         None \<Rightarrow> mark_conflicting i S
       | Some _ \<Rightarrow> S)
     )"

end


end