(*  Title: Implementation of CDCL with Two Watched Literals
    Author: Mathias Fleury <mathias.fleury@mpi-inf.mpg.de>
*)

subsection \<open>Implementation for 2 Watched-Literals\<close>

theory CDCL_Two_Watched_Literals_Implementation
imports CDCL_W_Abstract_State CDCL_Two_Watched_Literals
begin

sledgehammer_params[spy]

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


subsubsection \<open>Clauses\<close>

locale abstract_clause_representation_ops =
  well_formed_two_watched_literal_clauses wf_watched_lits wf_unwatched_lits
  for
    wf_watched_lits :: "'cls \<Rightarrow> 'lit multiset" and
    wf_unwatched_lits :: "'cls \<Rightarrow> 'lit multiset"
  +
  fixes
    lit_lookup :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'v literal option" and
    lit_keys :: "'cls \<Rightarrow> 'lit multiset" and

    swap_lit :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'lit \<Rightarrow> 'cls" and
    it_of_watched_ordered :: "'cls \<Rightarrow> 'v literal \<Rightarrow> 'lit list" and
    cls_of_twl_list :: "'v literal list \<Rightarrow> 'cls"
begin

fun map_wf_twl_clause where
"map_wf_twl_clause f C = TWL_Clause (f (wf_watched_lits C)) (f (wf_unwatched_lits C))"

lemma clause_map_wf_twl_clause_wf_clause:
  assumes "\<And>x1 x2. f (x1 + x2) = f x1 + f x2 "
  shows "clause (map_wf_twl_clause f C) = f (wf_clause C)"
  by (auto simp: assms wf_clause_def)

abbreviation twl_clause :: "'cls \<Rightarrow> 'v literal multiset twl_clause" where
"twl_clause C \<equiv> map_wf_twl_clause (image_mset (\<lambda>L. the (lit_lookup C L))) C"

definition clause_of_cls :: "'cls \<Rightarrow> 'v clause" where
"clause_of_cls C \<equiv> clause (twl_clause C)"

lemma wf_watched_watched_empty_iff:
  "wf_watched_lits C = {#} \<longleftrightarrow> watched (twl_clause C) = {#}"
  by simp

lemma wf_watched_empty_then_wf_unwatched_empty:
  "wf_watched_lits C = {#} \<Longrightarrow> wf_unwatched_lits C = {#}"
  using twl_cls_wf[of C] by simp

definition wf_watched :: "'cls \<Rightarrow> 'v literal multiset" where
"wf_watched C = image_mset (the o lit_lookup C) (wf_watched_lits C)"

definition wf_unwatched :: "'cls \<Rightarrow> 'v literal multiset" where
"wf_unwatched C = image_mset (the o lit_lookup C) (wf_unwatched_lits C)"

sublocale twl_mset: well_formed_two_watched_literal_clauses_ops wf_watched wf_unwatched .

end


locale abstract_clause_representation =
  abstract_clause_representation_ops wf_watched_lits wf_unwatched_lits lit_lookup lit_keys swap_lit
    it_of_watched_ordered cls_of_twl_list
  for
    wf_watched_lits :: "'cls \<Rightarrow> 'lit multiset" and
    wf_unwatched_lits :: "'cls \<Rightarrow> 'lit multiset" and
    lit_lookup :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'v literal option" and
    lit_keys :: "'cls \<Rightarrow> 'lit multiset" and

    swap_lit :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'lit \<Rightarrow> 'cls" and
    it_of_watched_ordered :: "'cls \<Rightarrow> 'v literal \<Rightarrow> 'lit list" and
    cls_of_twl_list :: "'v literal list \<Rightarrow> 'cls" +
  assumes
    distinct_lit_keys[simp]: "distinct_mset (lit_keys C)" and
    valid_lit_keys: "i \<in># lit_keys C \<longleftrightarrow> lit_lookup C i \<noteq> None" and
    swap_lit:
      "j \<in># wf_watched_lits C \<Longrightarrow> k \<in># wf_unwatched_lits C \<Longrightarrow>
        twl_clause (swap_lit C j k) =
          TWL_Clause
            ({#the (lit_lookup C k)#} + remove1_mset (the (lit_lookup C j)) (wf_watched C))
            ({#the (lit_lookup C j)#} + remove1_mset (the (lit_lookup C k)) (wf_unwatched C))" and

    it_of_watched_ordered:
      "L \<in># watched (twl_clause C) \<Longrightarrow>
         mset (it_of_watched_ordered C L) = wf_watched_lits C \<and>
         lit_lookup C (hd (it_of_watched_ordered C L)) = Some L" and

    twl_cls_valid: -- \<open>this states that all the valid indexes are included in @{term "C"}.\<close>
      "lit_keys C = wf_clause C" and

    cls_of_twl_list:
      "distinct D \<Longrightarrow>
        clause_of_cls (cls_of_twl_list D) = mset D"
begin

lemma valid_lit_keys_SomeD: "lit_lookup C i = Some e \<Longrightarrow> i \<in># lit_keys C"
  unfolding valid_lit_keys by auto

lemma lit_lookup_Some_in_clause_of_cls:
  assumes L: "lit_lookup C i = Some L"
  shows "L \<in># clause_of_cls C"
proof -
  have "i \<in># wf_clause C"
     using L by (auto simp: valid_lit_keys twl_cls_valid[symmetric])
  then have "L \<in> (\<lambda>l. the (lit_lookup C l)) ` set_mset (wf_clause C)"
    by (metis (no_types) assms image_eqI option.sel)
  then show ?thesis
    by (auto simp: clause_map_wf_twl_clause_wf_clause wf_clause_def clause_of_cls_def)
qed

lemma clause_of_cls_valid_lit_lookup:
  assumes L: "L \<in># clause_of_cls C"
  shows "\<exists>i. lit_lookup C i = Some L"
proof -
  obtain i where
    "L = the (lit_lookup C i)" and
    "i \<in># wf_clause C"
    using L by (auto simp: clause_map_wf_twl_clause_wf_clause wf_clause_def clause_of_cls_def)
  then have "lit_lookup C i = Some L"
    by (auto simp: twl_cls_valid[symmetric] valid_lit_keys)
  then show ?thesis by blast
qed

sublocale abstract_with_index where
  get_lit = lit_lookup and
  convert_to_mset = clause_of_cls
  apply unfold_locales
  apply (frule valid_lit_keys_SomeD)
  by (force simp: lit_lookup_Some_in_clause_of_cls clause_of_cls_valid_lit_lookup
    twl_cls_valid valid_lit_keys[symmetric] wf_clause_def)+

lemma it_of_watched_ordered_not_None:
  assumes
    L: "L \<in># watched (twl_clause C)" and
    it: "it_of_watched_ordered C L = [j, k]"
  shows
    "lit_lookup C j = Some L" and
    "lit_lookup C k \<noteq> None"
proof -
  have jk: "{#j, k#} = wf_watched_lits C" and
    j: "lit_lookup C j = Some L"
    using it_of_watched_ordered[OF L] unfolding it by (auto simp: ac_simps)
  have k: "k \<in># wf_clause C"
    using jk[symmetric] by (auto simp: wf_clause_def)

  show "lit_lookup C j = Some L"
    using j by simp
  show "lit_lookup C k \<noteq> None"
    using k unfolding valid_lit_keys[symmetric] twl_cls_valid by auto
qed

lemma unwatched_twl_clause_twl_cls_wff_iff:
  "unwatched (twl_clause C) = {#} \<longleftrightarrow> unwatched (twl_cls_wf C) = {#}"
  by auto

lemma distinct_plus_subset_mset_empty:
  "distinct_mset (B + A) \<Longrightarrow> A \<subseteq># B \<Longrightarrow> A = {#}"
  using add.commute[of B A] by (metis distinct_mset_add subset_mset.inf.orderE)

lemma it_of_watched_ordered_cases:
  assumes L: "L \<in># watched (twl_clause C)"
  shows
    "(\<exists>j. it_of_watched_ordered C L = [j] \<and> lit_lookup C j = Some L \<and>
      wf_unwatched_lits C = {#} \<and> wf_watched_lits C = {#j#}) \<or>
     (\<exists>j k. it_of_watched_ordered C L = [j, k] \<and> lit_lookup C j = Some L \<and> lit_lookup C k \<noteq> None \<and>
        wf_watched_lits C = {#j, k#})"
proof -
  have "size (mset (it_of_watched_ordered C L)) \<le> 2"
    using it_of_watched_ordered[OF assms] twl_cls_wf[of "C"]
    by (cases "twl_cls_wf C") auto
  moreover have "it_of_watched_ordered C L \<noteq> []"
    using assms it_of_watched_ordered by fastforce
  ultimately consider
    (single_watched) j where "it_of_watched_ordered C L = [j]" |
    (two_watched) j k where "it_of_watched_ordered C L = [j, k]"
    by (metis add_cancel_left_left le_eq_less_or_eq length_0_conv length_list_2 less_2_cases
      list.exhaust list.size(4) size_mset)
  then show ?thesis
    proof cases
      case (single_watched j) note j = this(1)
      moreover
        have "unwatched (twl_clause C) = {#}"
          using twl_cls_wf[of "C"] it_of_watched_ordered[OF assms]
          by (cases "twl_cls_wf C") (auto simp: j dest: distinct_plus_subset_mset_empty)
      ultimately show ?thesis
        using it_of_watched_ordered[OF L] by auto
    next
      case (two_watched j k)
      moreover have "{#j, k#} = {#k, j#}"
        by (auto simp: multiset_eq_iff)
      ultimately show ?thesis
        using it_of_watched_ordered_not_None[OF L] it_of_watched_ordered[OF assms] by auto
    qed
qed

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
      "cls_lookup Cs i \<noteq> None \<Longrightarrow> add_cls Cs C = (Cs', i) \<Longrightarrow>
        cls_lookup Cs' = (cls_lookup Cs) (i := Some C)"  and
    add_cls_new_keys:
      "cls_lookup Cs i \<noteq> None \<Longrightarrow> add_cls Cs C = (Cs', i) \<Longrightarrow> i \<notin># cls_keys Cs"
begin

lemma add_cls_new_key:
  "cls_lookup Cs i \<noteq> None \<Longrightarrow> add_cls Cs C = (Cs', i) \<Longrightarrow> i \<in># cls_keys Cs'"
  unfolding cls_keys by (simp add: add_cls)

abbreviation raw_cls_of_clss :: "'clss \<Rightarrow> 'cls multiset" where
"raw_cls_of_clss Cs \<equiv> image_mset (\<lambda>L. the (cls_lookup Cs L)) (cls_keys Cs)"

lemma cls_keys_clss_update[simp]:
  "cls_lookup Cs i \<noteq> None \<Longrightarrow> cls_keys (clss_update Cs i E) = cls_keys Cs"
  by (rule distinct_set_mset_eq) (auto simp: cls_keys clss_update split: if_splits)

lemma cls_lookup_Some_in_raw_cls_of_clss:
  assumes L: "cls_lookup Cs i = Some C"
  shows "C \<in># raw_cls_of_clss Cs"
  by (metis (mono_tags, lifting) assms cls_keys image_iff option.distinct(1) option.sel
    set_image_mset)

lemma raw_cls_of_clss_valid_cls_lookup:
  assumes L: "C \<in># raw_cls_of_clss Cs"
  shows "\<exists>i. cls_lookup Cs i = Some C"
  using assms by (auto simp: cls_keys)

sublocale abstract_with_index2 where
  get_lit = cls_lookup and
  convert_to_mset = raw_cls_of_clss
  by unfold_locales (metis cls_lookup_Some_in_raw_cls_of_clss raw_cls_of_clss_valid_cls_lookup)+

end


subsubsection \<open>State\<close>

locale abstract_clause_clauses_representation =
  abstract_clause_representation wf_watched_lits wf_unwatched_lits lit_lookup lit_keys swap_lit
    it_of_watched_ordered cls_of_twl_list +
  abstract_clauses_representation cls_lookup cls_keys clss_update add_cls
  for
    wf_watched_lits :: "'cls \<Rightarrow> 'lit multiset" and
    wf_unwatched_lits :: "'cls \<Rightarrow> 'lit multiset" and
    lit_lookup :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'v literal option" and
    lit_keys :: "'cls \<Rightarrow> 'lit multiset" and

    swap_lit :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'lit \<Rightarrow> 'cls" and
    it_of_watched_ordered :: "'cls \<Rightarrow> 'v literal \<Rightarrow> 'lit list" and

    cls_of_twl_list :: "'v literal list \<Rightarrow> 'cls" and
    cls_lookup :: "'clss \<Rightarrow> 'cls_it \<Rightarrow> 'cls option" and
    cls_keys :: "'clss \<Rightarrow> 'cls_it multiset" and
    clss_update :: "'clss \<Rightarrow> 'cls_it \<Rightarrow> 'cls \<Rightarrow> 'clss" and
    add_cls :: "'clss \<Rightarrow> 'cls \<Rightarrow> 'clss \<times> 'cls_it"
begin


sublocale raw_clss where
  get_lit = lit_lookup and
  mset_cls = clause_of_cls and
  get_cls = cls_lookup and
  mset_clss = raw_cls_of_clss
  by unfold_locales

end

locale abs_state\<^sub>W_clss_twl_ops =
  abstract_clause_clauses_representation
    wf_watched_lits wf_unwatched_lits
    lit_lookup lit_keys swap_lit
    it_of_watched_ordered cls_of_twl_list

    cls_lookup cls_keys clss_update add_cls
    +
  raw_cls mset_ccls
  for
    \<comment> \<open>Clause:\<close>
    wf_watched_lits :: "'cls \<Rightarrow> 'lit multiset" and
    wf_unwatched_lits :: "'cls \<Rightarrow> 'lit multiset" and
    lit_lookup :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'v literal option" and
    lit_keys :: "'cls \<Rightarrow> 'lit multiset" and

    swap_lit :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'lit \<Rightarrow> 'cls" and
    it_of_watched_ordered :: "'cls \<Rightarrow> 'v literal \<Rightarrow> 'lit list" and

    \<comment> \<open>Clauses\<close>
    cls_of_twl_list :: "'v literal list \<Rightarrow> 'cls" and
    cls_lookup :: "'clss \<Rightarrow> 'cls_it \<Rightarrow> 'cls option" and
    cls_keys :: "'clss \<Rightarrow> 'cls_it multiset" and
    clss_update :: "'clss \<Rightarrow> 'cls_it \<Rightarrow> 'cls \<Rightarrow> 'clss" and
    add_cls :: "'clss \<Rightarrow> 'cls \<Rightarrow> 'clss \<times> 'cls_it" and

    \<comment> \<open>Conflicting clause:\<close>
    mset_ccls :: "'ccls \<Rightarrow> 'v clause"
begin

sublocale abs_state\<^sub>W_clss_ops where
  get_lit = lit_lookup and
  mset_cls = clause_of_cls and
  get_cls = cls_lookup and
  mset_clss = raw_cls_of_clss and
  mset_ccls = mset_ccls
  by unfold_locales

fun abs_mlit :: "'clss \<Rightarrow> ('v, 'cls_it) ann_lit \<Rightarrow> ('v, 'v clause) ann_lit"
  where
"abs_mlit Cs (Propagated L C) = Propagated L (clause_of_cls (Cs \<Down> C))" |
"abs_mlit _ (Decided L) = Decided L"

lemma lit_of_abs_mlit[simp]:
  "lit_of (abs_mlit Cs a) = lit_of a"
  by (cases a) auto

lemma lit_of_abs_mlit_set_lit_of_l[simp]:
  "lit_of ` abs_mlit Cs ` set M' = lits_of_l M'"
  by (induction M') auto

lemma map_abs_mlit_true_annots_true_cls[simp]:
  "map (abs_mlit Cs) M' \<Turnstile>as C \<longleftrightarrow> M' \<Turnstile>as C"
  by (simp add: true_annots_true_cls lits_of_def)

end


locale abs_state\<^sub>W_twl_ops =
  abs_state\<^sub>W_clss_twl_ops
    \<comment> \<open>functions for clauses: \<close>
    wf_watched_lits wf_unwatched_lits
    lit_lookup lit_keys swap_lit
    it_of_watched_ordered cls_of_twl_list

    cls_lookup cls_keys clss_update add_cls

    \<comment> \<open>functions for the conflicting clause:\<close>
    mset_ccls
  for
    \<comment> \<open>Clause:\<close>
    wf_watched_lits :: "'cls \<Rightarrow> 'lit multiset" and
    wf_unwatched_lits :: "'cls \<Rightarrow> 'lit multiset" and
    lit_lookup :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'v literal option" and
    lit_keys :: "'cls \<Rightarrow> 'lit multiset" and

    swap_lit :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'lit \<Rightarrow> 'cls" and
    it_of_watched_ordered :: "'cls \<Rightarrow> 'v literal \<Rightarrow> 'lit list" and

    \<comment> \<open>Clauses\<close>
    cls_of_twl_list :: "'v literal list \<Rightarrow> 'cls" and
    cls_lookup :: "'clss \<Rightarrow> 'cls_it \<Rightarrow> 'cls option" and
    cls_keys :: "'clss \<Rightarrow> 'cls_it multiset" and
    clss_update :: "'clss \<Rightarrow> 'cls_it \<Rightarrow> 'cls \<Rightarrow> 'clss" and
    add_cls :: "'clss \<Rightarrow> 'cls \<Rightarrow> 'clss \<times> 'cls_it" and

    \<comment> \<open>Conflicting clause:\<close>
    mset_ccls :: "'ccls \<Rightarrow> 'v clause" +
  fixes
    find_undef_in_unwatched :: "'st \<Rightarrow> 'cls \<Rightarrow> 'lit option" and
    raw_full_trail_abs :: "'st \<Rightarrow> ('v, 'cls_it) ann_lits" and
    trail_abs :: "'st \<Rightarrow> ('v, 'v clause) ann_lits" and
    hd_raw_trail_abs :: "'st \<Rightarrow> ('v, 'cls_it) ann_lit" and
    prop_queue_abs :: "'st \<Rightarrow> ('v, 'v clause) ann_lits" and
    raw_clauses_abs :: "'st \<Rightarrow> 'clss" and
    backtrack_lvl_abs :: "'st \<Rightarrow> nat" and
    raw_conflicting_abs :: "'st \<Rightarrow> 'ccls option" and

    learned_clss_abs :: "'st \<Rightarrow> 'v clauses" and

    tl_trail_abs :: "'st \<Rightarrow> 'st" and
    reduce_trail_to_abs :: "('v, 'v clause) ann_lits \<Rightarrow> 'st \<Rightarrow> 'st" and

    cons_prop_queue_abs :: "('v, 'cls_it) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    last_prop_queue_to_trail_abs :: "'st \<Rightarrow> 'st" and
    prop_queue_abs_null :: "'st \<Rightarrow> bool" and
    prop_queue_to_trail_abs :: "'st \<Rightarrow> 'st" and

    add_confl_to_learned_cls_abs :: "'st \<Rightarrow> 'st \<times> 'cls_it" and
    remove_cls_abs :: "'cls \<Rightarrow> 'st \<Rightarrow> 'st" and

    update_backtrack_lvl_abs :: "nat \<Rightarrow> 'st \<Rightarrow> 'st" and

    mark_conflicting_abs :: "'cls_it \<Rightarrow> 'st \<Rightarrow> 'st" and
    resolve_conflicting_abs :: "'v literal \<Rightarrow> 'cls \<Rightarrow> 'st \<Rightarrow> 'st" and

    get_undecided_lit :: "'st \<Rightarrow> 'v literal option" and
    get_clause_watched_by :: "'st \<Rightarrow> 'v literal \<Rightarrow> 'cls_it list" and
    update_clause :: "'st \<Rightarrow> 'cls_it \<Rightarrow> 'cls \<Rightarrow> 'st" and

    init_state_abs :: "'clss \<Rightarrow> 'st" and
    restart_state :: "'st \<Rightarrow> 'st"
begin

fun twl_cls_wf' :: "'cls \<Rightarrow> 'v literal multiset twl_clause" where
"twl_cls_wf' C = TWL_Clause (wf_watched C) (wf_unwatched C)"

definition twl_clauses :: "'st \<Rightarrow> 'v literal multiset twl_clause multiset" where
  \<open>twl_clauses S =
  image_mset (\<lambda>C. twl_mset.twl_cls_wf (raw_clauses_abs S \<Down> C)) (cls_keys (raw_clauses_abs S))\<close>

definition full_trail_abs :: "'st \<Rightarrow> ('v, 'v clause) ann_lits" where
"full_trail_abs S = prop_queue_abs S @ trail_abs S"

sublocale abs_state\<^sub>W_ops where
  cls_lit = lit_lookup and
  mset_cls = clause_of_cls and
  clss_cls = cls_lookup and
  mset_clss = raw_cls_of_clss and
  mset_ccls = mset_ccls and

  conc_trail = full_trail_abs and
  hd_raw_conc_trail = hd_raw_trail_abs  and
  raw_clauses = raw_clauses_abs and
  conc_backtrack_lvl = backtrack_lvl_abs and
  raw_conflicting = raw_conflicting_abs and
  conc_learned_clss = learned_clss_abs and
  cons_conc_trail = cons_prop_queue_abs and
  tl_conc_trail = "\<lambda>S. tl_trail_abs S" and
  add_conc_confl_to_learned_cls = "\<lambda>S. fst (add_confl_to_learned_cls_abs S)" and
  remove_cls = remove_cls_abs and
  update_conc_backtrack_lvl = update_backtrack_lvl_abs and
  mark_conflicting = mark_conflicting_abs and
  reduce_conc_trail_to = "\<lambda>M S. reduce_trail_to_abs M (prop_queue_to_trail_abs S)" and
  resolve_conflicting = "\<lambda>L D S. resolve_conflicting_abs L D S" and
  conc_init_state = init_state_abs and
  restart_state = restart_state
  by unfold_locales

abbreviation conc_learned_clss :: "'st \<Rightarrow> 'v literal multiset multiset" where
  \<open>conc_learned_clss \<equiv> learned_clss_abs\<close>

lemma mmset_of_mlit_abs_mlit[simp]: "mmset_of_mlit = abs_mlit"
  by (intro ext, rename_tac S L, case_tac L) auto

lemma image_mset_clause_twl_Clauses_conc_clauses:
  \<open>image_mset clause (twl_clauses S) = conc_clauses S\<close>
  unfolding conc_clauses_def twl_clauses_def
  by (auto intro!: image_mset_cong
      simp: clause_of_cls_def wf_watched_def wf_unwatched_def clss_cls_def)

definition prop_state ::
    "'st \<Rightarrow> ('v, 'v clause) ann_lit list \<times> ('v, 'v clause) ann_lit list \<times> 'v clauses \<times>
      'v clauses \<times> nat \<times> 'v clause option" where
"prop_state S = (prop_queue_abs S, trail_abs S, conc_init_clss S, learned_clss_abs S,
  backtrack_lvl_abs S, conc_conflicting S)"

lemma prop_state_state: "prop_state S = (P, M, N, U, k, C) \<Longrightarrow> state S = (P @ M, N, U, k, C)"
  unfolding prop_state_def state_def full_trail_abs_def by auto

definition wf_prop_queue_abs :: "'st \<Rightarrow> bool" where
"wf_prop_queue_abs S \<longleftrightarrow> (\<forall>M \<in> set (prop_queue_abs S). is_proped M)"

definition all_annotation_valid where
"all_annotation_valid S \<longleftrightarrow>
  (\<forall>L \<in> set (raw_full_trail_abs S). valid_annotation S L)"

definition wf_twl_state :: "'st \<Rightarrow> bool" where
  "wf_twl_state S \<longleftrightarrow>
  (\<forall>C \<in># (twl_clauses S). wf_twl_cls (full_trail_abs S) C) \<and> no_dup (full_trail_abs S)"

definition wf_state :: "'st \<Rightarrow> bool" where
"wf_state S \<longleftrightarrow>
  all_annotation_valid S \<and>
  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state S) \<and>
  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (state S) \<and>
  wf_prop_queue_abs S \<and>
  wf_twl_state S"

definition wf_confl_state :: "'st \<Rightarrow> bool" where
"wf_confl_state S \<longleftrightarrow> (wf_state S \<and> raw_conflicting_abs S \<noteq> None)"

end

(* TODO Move *)
text \<open>TODO Move and see if useful at other places\<close>
lemma Suc_count_decided_gt_get_level:
  \<open>get_level M L < Suc (count_decided M)\<close>
  by (induction M rule: ann_lit_list_induct) auto

lemma get_level_Succ_count_decided_neq[simp]:
  \<open>get_level M L \<noteq> Suc (count_decided M)\<close>
  using Suc_count_decided_gt_get_level[of L M] by auto
text \<open>End TODO Move\<close>

(* End Move *)

locale abs_state\<^sub>W_twl =
  abs_state\<^sub>W_twl_ops
    \<comment> \<open>functions for clauses: \<close>
    wf_watched_lits wf_unwatched_lits
    lit_lookup lit_keys swap_lit
    it_of_watched_ordered cls_of_twl_list

    cls_lookup cls_keys clss_update add_cls

    \<comment> \<open>functions for the conflicting clause:\<close>
    mset_ccls

    find_undef_in_unwatched

    raw_full_trail_abs trail_abs hd_raw_trail_abs prop_queue_abs raw_clauses_abs backtrack_lvl_abs
    raw_conflicting_abs

    learned_clss_abs

    tl_trail_abs reduce_trail_to_abs

    cons_prop_queue_abs last_prop_queue_to_trail_abs prop_queue_abs_null prop_queue_to_trail_abs

    add_confl_to_learned_cls_abs remove_cls_abs

    update_backtrack_lvl_abs mark_conflicting_abs resolve_conflicting_abs

    get_undecided_lit get_clause_watched_by update_clause

    init_state_abs restart_state

  for
    \<comment> \<open>Clause:\<close>
    wf_watched_lits :: "'cls \<Rightarrow> 'lit multiset" and
    wf_unwatched_lits :: "'cls \<Rightarrow> 'lit multiset" and
    lit_lookup :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'v literal option" and
    lit_keys :: "'cls \<Rightarrow> 'lit multiset" and

    swap_lit :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'lit \<Rightarrow> 'cls" and
    it_of_watched_ordered :: "'cls \<Rightarrow> 'v literal \<Rightarrow> 'lit list" and

    \<comment> \<open>Clauses\<close>
    cls_of_twl_list :: "'v literal list \<Rightarrow> 'cls" and
    cls_lookup :: "'clss \<Rightarrow> 'cls_it \<Rightarrow> 'cls option" and
    cls_keys :: "'clss \<Rightarrow> 'cls_it multiset" and
    clss_update :: "'clss \<Rightarrow> 'cls_it \<Rightarrow> 'cls \<Rightarrow> 'clss" and
    add_cls :: "'clss \<Rightarrow> 'cls \<Rightarrow> 'clss \<times> 'cls_it" and

    \<comment> \<open>Conflicting clause:\<close>
    mset_ccls :: "'ccls \<Rightarrow> 'v clause" and

    find_undef_in_unwatched :: "'st \<Rightarrow> 'cls \<Rightarrow> 'lit option" and

    raw_full_trail_abs :: "'st \<Rightarrow> ('v, 'cls_it) ann_lits" and
    trail_abs :: "'st \<Rightarrow> ('v, 'v clause) ann_lits" and
    hd_raw_trail_abs :: "'st \<Rightarrow> ('v, 'cls_it) ann_lit" and
    prop_queue_abs :: "'st \<Rightarrow> ('v, 'v clause) ann_lits" and
    raw_clauses_abs :: "'st \<Rightarrow> 'clss" and
    backtrack_lvl_abs :: "'st \<Rightarrow> nat" and
    raw_conflicting_abs :: "'st \<Rightarrow> 'ccls option" and

    learned_clss_abs :: "'st \<Rightarrow> 'v clauses" and

    tl_trail_abs :: "'st \<Rightarrow> 'st" and
    reduce_trail_to_abs :: "('v, 'v clause) ann_lits \<Rightarrow> 'st \<Rightarrow> 'st" and

    cons_prop_queue_abs :: "('v, 'cls_it) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    last_prop_queue_to_trail_abs :: "'st \<Rightarrow> 'st" and
    prop_queue_abs_null :: "'st \<Rightarrow> bool" and
    prop_queue_to_trail_abs :: "'st \<Rightarrow> 'st" and

    add_confl_to_learned_cls_abs :: "'st \<Rightarrow> 'st \<times> 'cls_it" and
    remove_cls_abs :: "'cls \<Rightarrow> 'st \<Rightarrow> 'st" and

    update_backtrack_lvl_abs :: "nat \<Rightarrow> 'st \<Rightarrow> 'st" and

    mark_conflicting_abs :: "'cls_it \<Rightarrow> 'st \<Rightarrow> 'st" and
    resolve_conflicting_abs :: "'v literal \<Rightarrow> 'cls \<Rightarrow> 'st \<Rightarrow> 'st" and

    get_undecided_lit :: "'st \<Rightarrow> 'v literal option" and
    get_clause_watched_by :: "'st \<Rightarrow> 'v literal \<Rightarrow> 'cls_it list" and
    update_clause :: "'st \<Rightarrow> 'cls_it \<Rightarrow> 'cls \<Rightarrow> 'st" and

    init_state_abs :: "'clss \<Rightarrow> 'st" and
    restart_state :: "'st \<Rightarrow> 'st" +
  assumes
    prop_state_cons_prop_queue_abs:
      "\<And>T'. undefined_lit (full_trail_abs T) (lit_of L) \<Longrightarrow>
        prop_state T = (P, T') \<Longrightarrow> valid_annotation T L \<Longrightarrow>
        prop_state (cons_prop_queue_abs L T) = (abs_mlit (raw_clauses_abs T) L # P,  T')" and

    last_prop_queue_to_trail_abs_prop_state:
      "\<And>T'. prop_queue_abs T \<noteq> [] \<Longrightarrow>
        prop_state T = (P, M, T') \<Longrightarrow>
        prop_state (last_prop_queue_to_trail_abs T) =
           (but_last P, last P # M, T')" and
    prop_queue_to_trail_abs_prop_state:
      "\<And>T'. prop_state T = (P, M, T') \<Longrightarrow>
        prop_state (prop_queue_to_trail_abs T) = ([], P @ M, T')" and
    raw_conflicting_abs_prop_queue_to_trail_abs[simp]:
      "raw_conflicting_abs (prop_queue_to_trail_abs st) = raw_conflicting_abs st" and
    raw_clauses_abs_prop_queue_to_trail_abs[simp]:
      "raw_clauses_abs (prop_queue_to_trail_abs st) = raw_clauses_abs st" and

    hd_raw_trail_abs_raw_full_trail_abs:
      "raw_full_trail_abs st \<noteq> [] \<Longrightarrow>
        hd_raw_trail_abs st = hd (raw_full_trail_abs st)" and

    tl_trail_abs_prop_state:
      "\<And>S'. prop_state st = (P, M, S') \<Longrightarrow>
        prop_state (tl_trail_abs st) = (tl P, if P = [] then tl M else M, S')" and

    remove_cls_abs:
      "\<And>S'. prop_state st = (P, M, N, U, S') \<Longrightarrow>
        prop_state (remove_cls_abs C' st) =
          (P, M, removeAll_mset (clause_of_cls C') N, removeAll_mset (clause_of_cls C') U, S')" and

    add_confl_to_learned_cls_abs:
      "no_dup (full_trail_abs st) \<Longrightarrow> prop_state st = (P, M, N, U, k, Some F) \<Longrightarrow>
        prop_state (fst (add_confl_to_learned_cls_abs st)) =
          (P, M, N, {#F#} + U, k, None)" and
    add_confl_to_learned_cls_abs_valid:
      "no_dup (full_trail_abs st) \<Longrightarrow> prop_state st = (P, M, N, U, k, Some F) \<Longrightarrow>
         clause_of_cls (raw_clauses_abs
           (fst (add_confl_to_learned_cls_abs st)) \<Down> snd (add_confl_to_learned_cls_abs st)) = F \<and>
         cls_lookup (raw_clauses_abs (fst (add_confl_to_learned_cls_abs st)))
           (snd (add_confl_to_learned_cls_abs st)) \<noteq> None" and

    update_backtrack_lvl_abs:
      "\<And>S'. prop_state st = (P, M, N, U, k, S') \<Longrightarrow>
        prop_state (update_backtrack_lvl_abs k' st) = (P, M, N, U, k', S')" and

    mark_conflicting_abs_prop_state:
      "prop_state st = (P, M, N, U, k, None) \<Longrightarrow> E \<in>\<Down> raw_clauses_abs st \<Longrightarrow>
        prop_state (mark_conflicting_abs E st) =
          (P, M, N, U, k, Some (clause_of_cls (raw_clauses_abs st \<Down> E)))"
      and

    resolve_conflicting_abs:
      "prop_state st = (P, M, N, U, k, Some F) \<Longrightarrow> -L' \<in># F \<Longrightarrow> L' \<in># clause_of_cls D \<Longrightarrow>
        prop_state (resolve_conflicting_abs L' D st) =
          (P, M, N, U, k, Some (cdcl\<^sub>W_restart_mset.resolve_cls L' F (clause_of_cls D)))" and

    prop_state_init_state_abs:
      "prop_state (init_state_abs Ns) = ([], [], clauses_of_clss Ns, {#}, 0, None)" and

    \<comment> \<open>Properties about restarting @{term restart_state}:\<close>
    prop_queue_abs_restart_state[simp]: "prop_queue_abs (restart_state S) = []" and
    trail_abs_restart_state[simp]: "trail_abs (restart_state S) = []" and
    conc_init_clss_restart_state[simp]: "conc_init_clss (restart_state S) = conc_init_clss S" and
    learned_clss_abs_restart_state[intro]:
      "learned_clss_abs (restart_state S) \<subseteq># learned_clss_abs S" and
    backtrack_lvl_abs_restart_state[simp]: "backtrack_lvl_abs (restart_state S) = 0" and
    conc_conflicting_restart_state[simp]: "conc_conflicting (restart_state S) = None" and

    \<comment> \<open>Properties about @{term reduce_trail_to_abs}:\<close>
    reduce_trail_to_abs:
      "\<And>S'. trail_abs st = M2 @ M1 \<Longrightarrow> prop_state st = ([], M, S') \<Longrightarrow>
        prop_state (reduce_trail_to_abs M1 st) = ([], M1, S')" and

    learned_clauses:
      "learned_clss_abs S \<subseteq># conc_clauses S" and

    get_undecided_lit_Some:
      "get_undecided_lit T = Some L' \<Longrightarrow> undefined_lit (trail_abs T) L' \<and>
        atm_of L' \<in> atms_of_mm (conc_clauses T)" and
    get_undecided_lit_None:
      "get_undecided_lit T = None \<longleftrightarrow>
         (\<forall>L'. atm_of L' \<in> atms_of_mm (conc_clauses T) \<longrightarrow> \<not>undefined_lit (trail_abs T) L')" and
    get_clause_watched_by:
      "i \<in> set (get_clause_watched_by T K) \<longleftrightarrow> (K \<in># watched (twl_clause (raw_clauses_abs T \<Down> i)) \<and>
        i \<in>\<Down> raw_clauses_abs S)" and
    get_clause_watched_by_distinct:
      "distinct (get_clause_watched_by T K)" and

    update_clause:
      "i \<in>\<Down> raw_clauses_abs S \<Longrightarrow>
        raw_clauses_abs (update_clause S i E') = clss_update (raw_clauses_abs S) i E'" and
    update_clause_state:
      "i \<in>\<Down> raw_clauses_abs S \<Longrightarrow> prop_state S = (P, M, N, U, k, C) \<Longrightarrow>
        prop_state (update_clause S i E') = (P, M, conc_init_clss S, learned_clss_abs S, k, C)" and

    find_undef_in_unwatched_Some:
      "find_undef_in_unwatched S E' = Some j \<Longrightarrow> j \<in>\<down> E' \<and> undefined_lit (full_trail_abs S) (E'\<down>j) \<and>
        (E'\<down>j) \<in># unwatched (twl_clause E')" and
    find_undef_in_unwatched_None:
      "find_undef_in_unwatched S E' = None \<longleftrightarrow>
        (\<forall>j. j \<in>\<down> E' \<longrightarrow> (E'\<down>j) \<in># unwatched (twl_clause E') \<longrightarrow>
           \<not>undefined_lit (full_trail_abs S) (E'\<down>j))" and

    prop_queue_abs_null[iff]:
      "prop_queue_abs_null S \<longleftrightarrow> List.null (prop_queue_abs S)" and

    raw_full_trail_abs:
      \<open>full_trail_abs S = map (mmset_of_mlit (raw_clauses_abs S)) (raw_full_trail_abs S)\<close>
begin

lemma hd_raw_trail_abs[simp]:
  "full_trail_abs st \<noteq> [] \<Longrightarrow>
    hd (full_trail_abs st) = mmset_of_mlit (raw_clauses_abs st) (hd_raw_trail_abs st)"
  using hd_raw_trail_abs_raw_full_trail_abs[of st] raw_full_trail_abs[of st]
  by (cases \<open>raw_full_trail_abs st\<close>) auto

lemma
  prop_queue_abs_prop_queue_to_trail_abs[simp]:
    "prop_queue_abs (prop_queue_to_trail_abs S) = []" and
  trail_abs_prop_queue_to_trail_abs[simp]:
    "trail_abs (prop_queue_to_trail_abs S) = prop_queue_abs S @ trail_abs S" and
  full_trail_abs_prop_queue_to_trail_abs[simp]:
    "full_trail_abs (prop_queue_to_trail_abs S) = prop_queue_abs S @ trail_abs S" and
  conc_init_clss_prop_queue_to_trail_abs[simp]:
    "conc_init_clss (prop_queue_to_trail_abs S) = conc_init_clss S" and
  learned_clss_abs_prop_queue_to_trail_abs[simp]:
    "learned_clss_abs (prop_queue_to_trail_abs S) = learned_clss_abs S" and
  backtrack_lvl_abs_prop_queue_to_trail_abs[simp]:
    "backtrack_lvl_abs (prop_queue_to_trail_abs S) = backtrack_lvl_abs S" and
  conc_conflicting_prop_queue_to_trail_abs[simp]:
    "conc_conflicting (prop_queue_to_trail_abs S) = conc_conflicting S"
  using prop_queue_to_trail_abs_prop_state[of S "prop_queue_abs S"]
  by (auto simp: prop_state_def full_trail_abs_def; fail)+

lemma
  shows
    trail_abs_tl_trail_abs[simp]:
      "prop_queue_abs (tl_trail_abs S) = tl (prop_queue_abs S)" and
    full_trail_abs_tl_trail_abs[simp]:
      "full_trail_abs (tl_trail_abs S) = tl (full_trail_abs S)" and
    conc_init_clss_tl_trail_abs[simp]:
      "conc_init_clss (tl_trail_abs S) = conc_init_clss S" and
    learned_clss_abs_tl_trail_abs[simp]:
      "learned_clss_abs (tl_trail_abs S) = learned_clss_abs S" and
    backtrack_lvl_abs_tl_trail_abs[simp]:
      "backtrack_lvl_abs (tl_trail_abs S) = backtrack_lvl_abs S" and
    conc_conflicting_tl_trail_abs[simp]:
      "conc_conflicting (tl_trail_abs S) = conc_conflicting S"
  using tl_trail_abs_prop_state[of S "prop_queue_abs S" "trail_abs S"]
  by (auto simp: prop_state_def full_trail_abs_def; fail)+

lemma
  assumes "raw_conflicting_abs S \<noteq> None" and "no_dup (full_trail_abs S)"
  shows
    prop_queue_abs_add_confl_to_learned_cls_abs[simp]:
      "prop_queue_abs (fst (add_confl_to_learned_cls_abs S)) = prop_queue_abs S" and
    trail_abs_add_confl_to_learned_cls_abs[simp]:
      "trail_abs (fst (add_confl_to_learned_cls_abs S)) = trail_abs S" and
    full_trail_abs_add_confl_to_learned_cls_abs[simp]:
      "full_trail_abs (fst (add_confl_to_learned_cls_abs S)) = full_trail_abs S" and
    conc_init_clss_add_confl_to_learned_cls_abs[simp]:
      "conc_init_clss (fst (add_confl_to_learned_cls_abs S)) = conc_init_clss S" and
    backtrack_lvl_abs_add_confl_to_learned_cls_abs[simp]:
      "backtrack_lvl_abs (fst (add_confl_to_learned_cls_abs S)) = backtrack_lvl_abs S" and
    conc_conflicting_add_confl_to_learned_cls_abs[simp]:
      "conc_conflicting (fst (add_confl_to_learned_cls_abs S)) = None"
  using add_confl_to_learned_cls_abs[of S _ "trail_abs S" _ _ _ _] assms
  by (auto simp: prop_state_def full_trail_abs_def; fail)+

lemma
  assumes "raw_conflicting_abs S = Some F" and "no_dup (full_trail_abs S)"
  shows
    learned_clss_abs_add_confl_to_learned_cls_abs[simp]:
      "learned_clss_abs (fst (add_confl_to_learned_cls_abs S)) = {#mset_ccls F#} + learned_clss_abs S"
  using add_confl_to_learned_cls_abs[of S _ "trail_abs S" _ _ _ "mset_ccls F"] assms
  by (auto simp: prop_state_def full_trail_abs_def; fail)+

lemma state_cons_prop_queue_abs:
  assumes
    undef: "undefined_lit (full_trail_abs st) (lit_of L)" and
    st: "state st = (M, S')" and
    "valid_annotation st L"
  shows "state (cons_prop_queue_abs L st) = (mmset_of_mlit (raw_clauses_abs st) L # M, S')"
  using assms prop_state_cons_prop_queue_abs[of st L "prop_queue_abs st" "(trail_abs st, S')"]
  unfolding prop_state_def state_def full_trail_abs_def by auto

lemma cons_conc_trail:
  assumes "state st = (M, S')"
  shows "state (tl_trail_abs st) = (tl M, S')"
  using assms tl_trail_abs_prop_state[of "prop_queue_to_trail_abs st"
      "trail_abs (prop_queue_to_trail_abs st)" _ S']
  unfolding prop_state_def state_def
  by auto

lemma remove_cls:
  assumes "state st = (M, N, U, S')"
  shows "state (remove_cls_abs C st) =
    (M, removeAll_mset (clause_of_cls C) N, removeAll_mset (clause_of_cls C) U, S')"
  using remove_cls_abs[of st "prop_queue_abs st" "trail_abs st" "conc_init_clss st"
    "learned_clss_abs st"] assms
  unfolding prop_state_def state_def by (auto simp: full_trail_abs_def)

lemma add_conc_confl_to_learned_cls:
  assumes "no_dup (full_trail_abs st)" and
    "state st = (M, N, U, k, Some F)"
  shows "state (fst (add_confl_to_learned_cls_abs st)) = (M, N, {#F#} + U, k, None)"
  using add_confl_to_learned_cls_abs[of st _ _ N U k F] assms
  unfolding prop_state_def state_def by (auto simp: full_trail_abs_def)

lemma mark_conflicting_abs:
  assumes
    "state st = (M, N, U, k, None)" and
    "E \<in>\<Down> raw_clauses_abs st"
  shows "state (mark_conflicting_abs E st) =
    (M, N, U, k, Some (clause_of_cls (raw_clauses_abs st \<Down> E)))"
  using mark_conflicting_abs_prop_state[of st _ _ N U k E] assms
  unfolding prop_state_def state_def by (auto simp: full_trail_abs_def)

lemma init_state_abs:
  "state (init_state_abs Ns) = ([], clauses_of_clss Ns, {#}, 0, None)"
  using prop_state_init_state_abs[of Ns] by (auto simp: state_def prop_state_def full_trail_abs_def)

lemma reduce_conc_trail_to:
  assumes
    "full_trail_abs st = M2 @ M1" and
    "state st = (M, S')"
  shows "state (reduce_trail_to_abs M1 (prop_queue_to_trail_abs st)) = (M1, S')"
  using reduce_trail_to_abs[of "prop_queue_to_trail_abs st" M2 M1 M S'] assms
  unfolding full_trail_abs_def state_def prop_state_def by auto

lemma resolve_conflicting:
  assumes
    "state st = (M, N, U, k, Some F)" and
    "- L' \<in># F" and
    "L' \<in># clause_of_cls D"
  shows "state (resolve_conflicting_abs L' D st) =
    (M, N, U, k, Some (remove1_mset (- L') F \<union># remove1_mset L' (clause_of_cls D)))"
  using resolve_conflicting_abs[of st _ _ N U k F L' D] assms
  unfolding full_trail_abs_def state_def prop_state_def by auto

sublocale abs_state\<^sub>W where
  cls_lit = lit_lookup and
  mset_cls = clause_of_cls and
  clss_cls = cls_lookup and
  mset_clss = raw_cls_of_clss and
  mset_ccls = mset_ccls and

  conc_trail = full_trail_abs and
  hd_raw_conc_trail = hd_raw_trail_abs  and
  raw_clauses = raw_clauses_abs and
  conc_backtrack_lvl = backtrack_lvl_abs and
  raw_conflicting = raw_conflicting_abs and
  conc_learned_clss = learned_clss_abs and
  cons_conc_trail = cons_prop_queue_abs and
  tl_conc_trail = "\<lambda>S. tl_trail_abs S" and
  add_conc_confl_to_learned_cls = "\<lambda>S. fst (add_confl_to_learned_cls_abs S)" and
  remove_cls = remove_cls_abs and
  update_conc_backtrack_lvl = update_backtrack_lvl_abs and
  mark_conflicting = "\<lambda>i S. mark_conflicting_abs i S" and
  reduce_conc_trail_to = "\<lambda>M S. reduce_trail_to_abs M (prop_queue_to_trail_abs S)" and
  resolve_conflicting = "\<lambda>L D S. resolve_conflicting_abs L D S" and
  conc_init_state = init_state_abs and
  restart_state = restart_state
  apply unfold_locales
                  using hd_raw_trail_abs apply (simp; fail)
                 using state_cons_prop_queue_abs apply (simp; fail)
                using cons_conc_trail apply (simp; fail)
               using remove_cls apply (simp; fail)
              using add_conc_confl_to_learned_cls apply (simp; fail)
             using prop_state_def prop_state_state update_backtrack_lvl_abs apply (auto; fail)[1]
            using mark_conflicting_abs apply (simp; fail)
           using resolve_conflicting apply (blast; fail)
          using init_state_abs apply (simp; fail)
         apply (simp add: full_trail_abs_def; fail)
        apply (simp add: full_trail_abs_def; fail)
       apply (simp add: learned_clss_abs_restart_state; fail)
     using backtrack_lvl_abs_restart_state apply blast
    apply simp
   using reduce_conc_trail_to apply (blast; fail)
  apply (simp add: learned_clauses; fail)
  done

lemma conc_clauses_update_clause:
  assumes
    i: "i \<in>\<Down> raw_clauses_abs S"
  shows
    "conc_clauses (update_clause S i E) =
       remove1_mset (clause_of_cls (raw_clauses_abs S \<Down> i)) (conc_clauses S) + {#clause_of_cls E#}"
     (is "?abs = ?r")
proof-
  have XX: "\<And>x. clause_of_cls (the (if x = i then Some E else cls_lookup (raw_clauses_abs S) x)) =
    (if x = i then clause_of_cls E else clause_of_cls (the (cls_lookup (raw_clauses_abs S) x)))"
     by (auto simp: update_clause[OF i] clss_update split: if_splits)
  have YY: "remove1_mset (clause_of_cls (raw_clauses_abs S \<Down> i))
    {#clause_of_cls (the (cls_lookup (raw_clauses_abs S) x)). x \<in># cls_keys (raw_clauses_abs S)#} =
    {#clause_of_cls (the (cls_lookup (raw_clauses_abs S) x)).
       x \<in># remove1_mset i (cls_keys (raw_clauses_abs S))#}"
     apply (subst image_mset_Diff)
     using i by (auto simp add: cls_keys in_clss_def clss_cls_def)

  have c: "count (cls_keys (raw_clauses_abs S)) i = 1"
    by (meson cls_keys cls_keys_distinct distinct_mset_def i in_clss_def)
  then have [simp]: "replicate_mset (count (cls_keys (raw_clauses_abs S)) i) (clause_of_cls E) =
    {#clause_of_cls E#}"
    by simp
  show ?thesis
     using i unfolding conc_clauses_def clauses_of_clss_def in_clss_def
     by (auto simp: update_clause[OF i] clss_update XX YY image_mset_If ac_simps
         filter_eq_replicate_mset filter_mset_neq
         distinct_mset_remove1_All)
qed

end

subsubsection \<open>The new Calculus\<close>

fun reduce_trail_to_lvl :: "nat \<Rightarrow> ('a, 'b) ann_lit list \<Rightarrow> ('a, 'b) ann_lit list" where
"reduce_trail_to_lvl _ [] = []" |
"reduce_trail_to_lvl target_lvl (Decided L # M) =
  (if count_decided M = target_lvl then M
  else reduce_trail_to_lvl target_lvl M)" |
"reduce_trail_to_lvl lvl (Propagated L C # M) = reduce_trail_to_lvl lvl M"

fun reduce_trail_to_lvl_no_count :: "nat \<Rightarrow> nat \<Rightarrow> ('a, 'b) ann_lit list \<Rightarrow> ('a, 'b) ann_lit list" where
"reduce_trail_to_lvl_no_count _ _ [] = []" |
"reduce_trail_to_lvl_no_count target_lvl current_lvl (Decided L # M) =
  (if Suc target_lvl = current_lvl then M
  else reduce_trail_to_lvl_no_count target_lvl (current_lvl - 1) M)" |
  -- \<open>@{term "Suc lvl"} is the level we are seeking plus one, @{term "Suc current_lvl"} is the
    current level.\<close>
"reduce_trail_to_lvl_no_count lvl current_lvl (Propagated L C # M) =
  reduce_trail_to_lvl_no_count lvl current_lvl M"

lemma reduce_trail_to_lvl_reduce_trail_to_lvl_no_count:
  "reduce_trail_to_lvl i M = reduce_trail_to_lvl_no_count i (count_decided M) M"
  by (induction M rule: ann_lit_list_induct) auto

lemma reduce_trail_to_lvl_lvl_eq[simp]:
  "reduce_trail_to_lvl (count_decided M - 1) M = tl (dropWhile (\<lambda>L. \<not>is_decided L) M)"
  by (induction M rule: ann_lit_list_induct) auto

lemma reduce_trail_to_lvl_lvl_ge:
  "i \<ge> count_decided M \<Longrightarrow> reduce_trail_to_lvl i M = []"
  by (induction M rule: ann_lit_list_induct) auto

lemma reduce_trail_to_lvl_lvl_ge_lvl:
  "reduce_trail_to_lvl i M = [] \<Longrightarrow> i \<ge> count_decided M \<or> i = 0"
  by (induction M rule: ann_lit_list_induct) (auto split: if_split_asm)

lemma reduce_trail_to_lvl_decomp_lvl:
  assumes "i < count_decided M"
  shows "(\<exists>M' L. M = M' @ Decided L # reduce_trail_to_lvl i M) \<and>
    count_decided (reduce_trail_to_lvl i M) = i"
  using assms
proof (induction M rule: ann_lit_list_induct)
  case Nil
  then show ?case by simp
next
  case (Decided L M) note IH = this(1) and i = this(2)
  show ?case
    proof (cases "i < count_decided M")
      case False
      then have i: "i = count_decided M"
        using i by auto
      show ?thesis
        by (auto simp: i reduce_trail_to_lvl_lvl_ge)
    next
      case True
      then obtain L' M' where
        M: "M = M' @ Decided L' # reduce_trail_to_lvl i M" and
        i: "count_decided (reduce_trail_to_lvl i M) = i"
        using IH by auto
      then have "Decided L # M = (Decided L # M') @ Decided L' # reduce_trail_to_lvl i M"
        by auto
      then have "\<exists>M' La. Decided L # M = M' @ Decided La # reduce_trail_to_lvl i M"
        by blast
      then show ?thesis using i by auto
    qed
next
  case (Propagated L C M) note IH = this(1) and i = this(2)
  show ?case
    proof (cases "i < count_decided M")
      case False
      then have i: "i = count_decided M"
        using i by auto
      show ?thesis
        using False Propagated.prems by (auto simp: i reduce_trail_to_lvl_lvl_ge)
    next
      case True
      then obtain L' M' where
        M: "M = M' @ Decided L' # reduce_trail_to_lvl i M" and
        i: "count_decided (reduce_trail_to_lvl i M) = i"
        using IH by auto

      have "Propagated L C # M = (Propagated L C # M') @ Decided L' # reduce_trail_to_lvl i M"
        using M by auto
      then have "\<exists>M' La. Propagated L C # M = M' @ Decided La # reduce_trail_to_lvl i M"
        by blast
      then show ?thesis using M i by auto
    qed
qed

lemma reduce_trail_to_lvl_skip_not_marked_at_beginning:
  assumes "\<forall>m \<in> set M'. \<not>is_decided m"
  shows "reduce_trail_to_lvl i (M' @ Decided L # M'') = reduce_trail_to_lvl i (Decided L # M'')"
  using assms by (induction M' rule: ann_lit_list_induct) auto

lemma count_decided_tl_dropWhile_not_decided:
  "count_decided (tl (dropWhile (\<lambda>L. \<not> is_decided L) M)) = count_decided M - 1"
  by (induction M rule: ann_lit_list_induct) auto


locale abs_conflict_driven_clause_learning\<^sub>W_clss =
  abs_state\<^sub>W_twl
    \<comment> \<open>functions for clauses: \<close>
    wf_watched_lits wf_unwatched_lits
    lit_lookup lit_keys swap_lit
    it_of_watched_ordered cls_of_twl_list

    cls_lookup cls_keys clss_update add_cls

    \<comment> \<open>functions for the conflicting clause:\<close>
    mset_ccls

    find_undef_in_unwatched

    raw_full_trail_abs trail_abs hd_raw_trail_abs prop_queue_abs raw_clauses_abs backtrack_lvl_abs
    raw_conflicting_abs

    learned_clss_abs

    tl_trail_abs reduce_trail_to_abs

    cons_prop_queue_abs last_prop_queue_to_trail_abs prop_queue_abs_null prop_queue_to_trail_abs

    add_confl_to_learned_cls_abs remove_cls_abs

    update_backtrack_lvl_abs mark_conflicting_abs resolve_conflicting_abs

    get_undecided_lit get_clause_watched_by update_clause

    init_state_abs restart_state +
  type_definition
    rough_state_of abs_state_of "(Collect wf_twl_state)"
  for
    \<comment> \<open>Clause:\<close>
    wf_watched_lits :: "'cls \<Rightarrow> 'lit multiset" and
    wf_unwatched_lits :: "'cls \<Rightarrow> 'lit multiset" and
    lit_lookup :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'v literal option" and
    lit_keys :: "'cls \<Rightarrow> 'lit multiset" and

    swap_lit :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'lit \<Rightarrow> 'cls" and
    it_of_watched_ordered :: "'cls \<Rightarrow> 'v literal \<Rightarrow> 'lit list" and

    \<comment> \<open>Clauses\<close>
    cls_of_twl_list :: "'v literal list \<Rightarrow> 'cls" and
    cls_lookup :: "'clss \<Rightarrow> 'cls_it \<Rightarrow> 'cls option" and
    cls_keys :: "'clss \<Rightarrow> 'cls_it multiset" and
    clss_update :: "'clss \<Rightarrow> 'cls_it \<Rightarrow> 'cls \<Rightarrow> 'clss" and
    add_cls :: "'clss \<Rightarrow> 'cls \<Rightarrow> 'clss \<times> 'cls_it" and

    \<comment> \<open>Conflicting clause:\<close>
    mset_ccls :: "'ccls \<Rightarrow> 'v clause" and

    find_undef_in_unwatched :: "'st \<Rightarrow> 'cls \<Rightarrow> 'lit option" and

    raw_full_trail_abs :: "'st \<Rightarrow> ('v, 'cls_it) ann_lits" and
    trail_abs :: "'st \<Rightarrow> ('v, 'v clause) ann_lits" and
    hd_raw_trail_abs :: "'st \<Rightarrow> ('v, 'cls_it) ann_lit" and
    prop_queue_abs :: "'st \<Rightarrow> ('v, 'v clause) ann_lits" and
    raw_clauses_abs :: "'st \<Rightarrow> 'clss" and
    backtrack_lvl_abs :: "'st \<Rightarrow> nat" and
    raw_conflicting_abs :: "'st \<Rightarrow> 'ccls option" and

    learned_clss_abs :: "'st \<Rightarrow> 'v clauses" and

    tl_trail_abs :: "'st \<Rightarrow> 'st" and
    reduce_trail_to_abs :: "('v, 'v clause) ann_lits \<Rightarrow> 'st \<Rightarrow> 'st" and

    cons_prop_queue_abs :: "('v, 'cls_it) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    last_prop_queue_to_trail_abs :: "'st \<Rightarrow> 'st" and
    prop_queue_abs_null :: "'st \<Rightarrow> bool" and
    prop_queue_to_trail_abs :: "'st \<Rightarrow> 'st" and

    add_confl_to_learned_cls_abs :: "'st \<Rightarrow> 'st \<times> 'cls_it" and
    remove_cls_abs :: "'cls \<Rightarrow> 'st \<Rightarrow> 'st" and

    update_backtrack_lvl_abs :: "nat \<Rightarrow> 'st \<Rightarrow> 'st" and

    mark_conflicting_abs :: "'cls_it \<Rightarrow> 'st \<Rightarrow> 'st" and
    resolve_conflicting_abs :: "'v literal \<Rightarrow> 'cls \<Rightarrow> 'st \<Rightarrow> 'st" and

    get_undecided_lit :: "'st \<Rightarrow> 'v literal option" and
    get_clause_watched_by :: "'st \<Rightarrow> 'v literal \<Rightarrow> 'cls_it list" and
    update_clause :: "'st \<Rightarrow> 'cls_it \<Rightarrow> 'cls \<Rightarrow> 'st" and

    init_state_abs :: "'clss \<Rightarrow> 'st" and
    restart_state :: "'st \<Rightarrow> 'st" and

    abs_state_of :: "'st \<Rightarrow> 'inv" and
    rough_state_of :: "'inv \<Rightarrow> 'st" and

    abs_confl_state_of :: "'st \<Rightarrow> 'inv" and
    rough_confl_state_of :: "'inv \<Rightarrow> 'st"
begin

sublocale abs_conflict_driven_clause_learning\<^sub>W where
  get_lit = lit_lookup and
  mset_cls = clause_of_cls and
  get_cls = cls_lookup and
  mset_clss = raw_cls_of_clss and
  mset_ccls = mset_ccls and

  conc_trail = full_trail_abs and
  hd_raw_conc_trail = hd_raw_trail_abs  and
  raw_clauses = raw_clauses_abs and
  conc_backtrack_lvl = backtrack_lvl_abs and
  raw_conflicting = raw_conflicting_abs and
  conc_learned_clss = learned_clss_abs and
  cons_conc_trail = cons_prop_queue_abs and
  tl_conc_trail = "\<lambda>S. tl_trail_abs S" and
  add_conc_confl_to_learned_cls = "\<lambda>S. fst (add_confl_to_learned_cls_abs S)" and
  remove_cls = remove_cls_abs and
  update_conc_backtrack_lvl = update_backtrack_lvl_abs and
  mark_conflicting = "\<lambda>i S. mark_conflicting_abs i S" and
  reduce_conc_trail_to = "\<lambda>M S. reduce_trail_to_abs M (prop_queue_to_trail_abs S)" and
  resolve_conflicting = "\<lambda>L D S. resolve_conflicting_abs L D S" and
  conc_init_state = init_state_abs and
  restart_state = restart_state
  by unfold_locales

text \<open>Lifting the operators to type @{typ 'inv}\<close>
definition wf_state_abs :: "'st \<Rightarrow> 'inv" where
"wf_state_abs S = abs_state_of (if wf_twl_state S then S else S)"

lemma [code abstype]:
  "wf_state_abs (rough_state_of S) = S"
  by (simp add: Rep_inverse wf_state_abs_def)

definition full_trail_abs_inv ::  "'inv \<Rightarrow> ('v, 'v literal multiset) ann_lit list" where
"full_trail_abs_inv S = full_trail_abs (rough_state_of S)"

definition prop_queue_abs_inv ::  "'inv \<Rightarrow> ('v, 'v literal multiset) ann_lit list" where
"prop_queue_abs_inv S = prop_queue_abs (rough_state_of S)"

definition trail_abs_inv ::  "'inv \<Rightarrow> ('v, 'v literal multiset) ann_lit list" where
"trail_abs_inv S = trail_abs (rough_state_of S)"

lemma full_trail_abs_inv:
  "full_trail_abs_inv S = prop_queue_abs_inv S @ trail_abs_inv S"
  unfolding full_trail_abs_def full_trail_abs_inv_def prop_queue_abs_inv_def trail_abs_inv_def
  by auto

definition hd_raw_trail_abs_inv :: "'inv \<Rightarrow> ('v, 'cls_it) ann_lit" where
"hd_raw_trail_abs_inv S = hd_raw_trail_abs (rough_state_of S)"

definition raw_clauses_abs_inv :: "'inv \<Rightarrow> 'clss" where
"raw_clauses_abs_inv S = raw_clauses_abs (rough_state_of S)"

definition backtrack_lvl_abs_inv :: "'inv \<Rightarrow> nat" where
"backtrack_lvl_abs_inv S = backtrack_lvl_abs (rough_state_of S)"

definition raw_conflicting_abs_inv :: "'inv \<Rightarrow> 'ccls option" where
"raw_conflicting_abs_inv S = raw_conflicting_abs (rough_state_of S)"

definition learned_clss_abs_inv :: "'inv \<Rightarrow> 'v clauses" where
"learned_clss_abs_inv S = learned_clss_abs (rough_state_of S)"

definition tl_trail_abs_inv :: "'inv \<Rightarrow> 'inv" where
"tl_trail_abs_inv S = abs_state_of (tl_trail_abs (rough_state_of S))"

definition wf_resolve :: "'inv \<Rightarrow> 'inv \<Rightarrow> bool" where
"wf_resolve S T \<equiv> resolve_abs (rough_state_of S) (rough_state_of T)"

abbreviation mark_conflicting_abs_and_flush where
"mark_conflicting_abs_and_flush  i S \<equiv> mark_conflicting_abs i (prop_queue_to_trail_abs S)"

lemma true_annots_CNot_uminus_incl_iff:
  "M \<Turnstile>as CNot C \<longleftrightarrow> uminus ` set_mset C \<subseteq> lits_of_l M"
  by (auto simp: true_annots_true_cls_def_iff_negation_in_model)

lemma get_maximum_level_skip_Decide_first:
  assumes "atm_of L \<notin> atms_of D" and "atms_of D \<subseteq> atm_of ` lits_of_l M"
  shows "get_maximum_level (Decided L # M) D = get_maximum_level M D"
  using assms unfolding get_maximum_level_def atms_of_def
    atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set
  by (smt ann_lit.sel(1) assms(1) atms_of_def get_level_skip_beginning image_iff multiset.map_cong0)

definition backtrack_implementation_lvl :: "nat \<Rightarrow> 'v literal \<Rightarrow> 'st \<Rightarrow> 'st"  where
"backtrack_implementation_lvl k L S =
  (let S =
    add_confl_to_learned_cls_abs
      (update_backtrack_lvl_abs k (reduce_trail_to_abs (reduce_trail_to_lvl k (full_trail_abs S)) S))
   in cons_prop_queue_abs (Propagated L (snd S)) (fst S))"

definition backtrack_implementation :: "'v literal \<Rightarrow> 'st \<Rightarrow> 'st" where
"backtrack_implementation L S =
  backtrack_implementation_lvl
    (get_maximum_level (tl (full_trail_abs S)) (the (conc_conflicting S)))
    L S"

definition resolve_implementation :: "'v literal \<Rightarrow> 'cls_it \<Rightarrow> 'st \<Rightarrow> 'st" where
"resolve_implementation L C S = tl_trail_abs (resolve_conflicting_abs L (raw_clauses_abs S \<Down> C) S)"

definition skip_implementation :: "'st \<Rightarrow> 'st" where
"skip_implementation S = tl_trail_abs S"

lemma skip_implementation:
  assumes
    "-L \<notin># mset_ccls (the (raw_conflicting_abs S))" and
    "full_trail_abs S \<noteq> []" and
    "raw_conflicting_abs S \<noteq> None" and
    "conc_conflicting S \<noteq> Some {#}"
    "hd_raw_trail_abs S = Propagated L C" and
    wf: "wf_twl_state S"
  shows "cdcl\<^sub>W_restart_mset.skip (state S) (state (skip_implementation S))"
proof -
  obtain M where
    M: "full_trail_abs S = Propagated L (clause_of_cls (raw_clauses_abs S \<Down> C)) # M"
    apply (cases "full_trail_abs S")
    using assms hd_raw_trail_abs[of S] by auto
  obtain D where D: "raw_conflicting_abs S = Some D"
    apply (cases "raw_conflicting_abs S")
    using assms by auto
  show ?thesis
    apply (rule cdcl\<^sub>W_restart_mset.skip.intros)
    using assms M D by (auto simp: skip_implementation_def)
qed

lemma always_exists_state_eqI:
  \<open>(\<forall>a aa ab ac b. \<not> (a, aa, ab, ac, b) \<sim>m S) \<longleftrightarrow> False\<close>
  unfolding state_eq_def
  by (cases S) (auto simp: backtrack_lvl.simps learned_clss.simps init_clss.simps trail.simps
      conflicting.simps CDCL_W_Abstract_State.state_def)

lemma get_maximum_level_skip_un_decided_not_present:
  assumes
    "\<forall>L\<in>#D. atm_of L \<notin> atm_of ` lits_of_l M"
  shows "get_maximum_level (M @ aa) D = get_maximum_level aa D"
  using assms unfolding get_maximum_level_def by simp

lemma backtrack_rule_reduce_trail_to_lvl:
  fixes S :: 'st
  defines
    \<open>i \<equiv> get_maximum_level (tl (full_trail_abs S)) (the (conc_conflicting S))\<close> and
    \<open>D \<equiv> the (conc_conflicting S)\<close>
  assumes
    inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state S)\<close> and
    inv': \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (state S)\<close> and
    confl: \<open>raw_conflicting_abs S \<noteq> None\<close> and
    n_empty[simp]: \<open>D \<noteq> {#}\<close> and
    n_s: \<open>no_step cdcl\<^sub>W_restart_mset.skip (state S)\<close> and
    i: \<open>i < backtrack_lvl_abs S\<close> and
    T: \<open>T \<sim>m cons_trail (Propagated (-lit_of (hd (full_trail_abs S))) D)
          (cdcl\<^sub>W_restart_mset.reduce_trail_to (reduce_trail_to_lvl i (full_trail_abs S))
            (add_learned_cls D
              (update_backtrack_lvl i
                (update_conflicting None (state S)))))\<close>
  shows
    \<open>cdcl\<^sub>W_restart_mset.backtrack (state S) T\<close>
proof -
  have confl'[simp]: \<open>conc_conflicting S = Some D\<close>
    using confl D_def by auto
  have n_d: \<open>no_dup (full_trail_abs S)\<close>
    using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by auto

  have \<open>full_trail_abs S \<noteq> []\<close>
    using n_empty inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
    by auto
  then obtain L M where LM: \<open>full_trail_abs S = L # M\<close>
    by (cases \<open>full_trail_abs S\<close>)auto

  let ?L' = "-lit_of L"
  have \<open>full_trail_abs S \<Turnstile>as CNot D\<close>
    using n_empty inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
    by auto
  have \<open>-lit_of L \<notin> lits_of_l M\<close>
    using n_d by (auto simp: LM lits_of_def uminus_lit_swap)
  then have \<open>lit_of L \<notin># D\<close>
    using \<open>full_trail_abs S \<Turnstile>as CNot D\<close>
    by (auto simp: LM true_annots_true_cls_def_iff_negation_in_model uminus_lit_swap)

  have \<open>?L' \<in># D\<close> if \<open>\<not>is_decided L\<close>
    using n_s that
    by (cases L) (auto simp: cdcl\<^sub>W_restart_mset.skip.simps LM simp: always_exists_state_eqI)
  moreover {
    have \<open>cdcl\<^sub>W_restart_mset.conflict_is_false_with_level (state S)\<close>
      using inv' unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by auto
    moreover have \<open>backtrack_lvl (state S) = count_decided (trail (state S))\<close>
      using n_empty inv' inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
      by auto
    moreover have \<open>full_trail_abs S \<Turnstile>as CNot D\<close>
      using n_empty inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
      by auto
    ultimately have \<open>get_level (trail (state S)) L' = backtrack_lvl (state S) \<longleftrightarrow> atm_of (lit_of L) = atm_of L'\<close>
      if \<open>L' \<in># D\<close> and \<open>is_decided L\<close> for L'
      using that by (cases L) (auto simp: LM split: if_splits)
    then have \<open>?L' \<in># D\<close> if \<open>is_decided L\<close>
      using that inv' \<open>lit_of L \<notin># D\<close> unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant_def
      by (cases L) (auto simp: LM atm_of_eq_atm_of split:  if_splits) }
  ultimately have \<open>?L' \<in># D\<close> by blast

  obtain K M2 where
    M1: \<open>trail (state S) = M2 @ Decided K # reduce_trail_to_lvl i (trail (state S))\<close> and
    lvl_reduce_i: \<open>count_decided (reduce_trail_to_lvl i (trail (state S))) = i\<close>
    using reduce_trail_to_lvl_decomp_lvl[of i \<open>trail (state S)\<close>]
      i inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by auto
  define M1 where \<open>M1 \<equiv> reduce_trail_to_lvl i (trail (state S))\<close>
  obtain M2' where M2': \<open>(Decided K # M1, M2') \<in> set (get_all_ann_decomposition (trail (state S)))\<close>
    using Decided_cons_in_get_all_ann_decomposition_append_Decided_cons[of K M1 M2] M1 M1_def by auto

  have lev_L_S: \<open>get_level (trail (state S)) (- lit_of L) = backtrack_lvl (state S)\<close>
    using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (auto simp: LM)

  have \<open>get_maximum_level (trail (state S)) D \<le> get_level (trail (state S)) (- lit_of L)\<close>
    using count_decided_ge_get_maximum_level[of "L#M"] inv
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by (auto simp: LM)
  moreover have \<open>get_maximum_level (trail (state S)) D \<ge> get_level (trail (state S)) ?L'\<close>
    using get_maximum_level_ge_get_level[of ?L' D] \<open>?L' \<in># D\<close> by blast
  ultimately have lev_L: \<open>get_level (trail (state S)) ?L' = get_maximum_level (trail (state S)) D\<close>
    by linarith

  have [simp]: \<open>get_level M (lit_of L) = 0\<close>
    apply (rule atm_of_notin_get_rev_level_eq_0)
    using n_d by (auto simp: LM lits_of_def)
  have remove1_All: \<open>remove1_mset (- lit_of L) D = removeAll_mset (- lit_of L) D\<close>
    using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
    by (auto simp: distinct_mset_remove1_All)
  have \<open>get_maximum_level M D =
      get_maximum_level M (remove1_mset ?L' D)\<close>
    using get_maximum_level_add_mset[of M ?L' \<open>remove1_mset ?L' D\<close>] \<open>?L' \<in># D\<close>
    by auto
  also {
    have H: \<open>\<forall>x\<in>atms_of (removeAll_mset (- lit_of L) D). x \<noteq> atm_of (lit_of L)\<close>
      using \<open>lit_of L \<notin># D\<close> by (auto simp: atms_of_def atm_of_eq_atm_of)
    have \<open>get_maximum_level M (remove1_mset ?L' D) = get_maximum_level (L # M) (remove1_mset ?L' D)\<close>
      using get_maximum_level_skip_beginning[of \<open>removeAll_mset ?L' D\<close> \<open>[L]\<close> M]
      by (auto simp: H remove1_All)
    }
  finally have lvl_D_I: \<open>get_maximum_level (trail (state S)) (remove1_mset ?L' D) = i\<close>
    unfolding i_def by (auto simp: LM)
  have \<open>get_level (trail (state S)) K = Suc (count_decided M1)\<close>
    unfolding M1[unfolded M1_def[symmetric]]
    apply (subst get_rev_level_skip)
    using n_d M1[unfolded M1_def[symmetric]]
    by (auto simp: lits_of_def)
  then have lvl_K_i: \<open>get_level (trail (state S)) K = i + 1\<close>
    using lvl_reduce_i by (auto simp: M1_def)

  show ?thesis
    apply (rule cdcl\<^sub>W_restart_mset.backtrack_rule)
           using confl' apply (simp; fail)
          using \<open>?L' \<in># D\<close> apply (simp; fail)
         using M2' apply (simp; fail)
        using lev_L_S apply (simp; fail)
       using lev_L apply (simp; fail)
      using lvl_D_I apply (simp; fail)
     using lvl_K_i apply (simp; fail)
    using T M2' by (auto simp: state_eq_def LM M1_def
        simp del: CDCL_W_Abstract_State.cdcl\<^sub>W_restart_mset.state_simp)[]
qed

lemma full_trail_abs_Cons_Decide_hd_raw_trail_abs:
  \<open>full_trail_abs S = Decided L # list \<Longrightarrow> hd_raw_trail_abs S = Decided L\<close>
  using hd_raw_trail_abs[of S] by (cases \<open>hd_raw_trail_abs S\<close>) (auto simp del: hd_raw_trail_abs)

lemma reduce_trail_to_lvl_exists_prepend:
  \<open>\<exists>M'. M = M' @ reduce_trail_to_lvl k M\<close>
  apply (induction M rule: ann_lit_list_induct)
    apply simp
   apply (metis (no_types, hide_lams) append_Cons reduce_trail_to_lvl.simps(2) self_append_conv2)
  by (metis append_Cons reduce_trail_to_lvl.simps(3))

lemma
  fixes S :: 'st and k :: nat
  defines [simp]: "M \<equiv> reduce_trail_to_lvl k (full_trail_abs S)"
  assumes pq: \<open>prop_queue_abs S = []\<close>
  shows
    conc_init_clss_reduce_trail_to_abs[simp]:
    \<open>conc_init_clss (reduce_trail_to_abs M S) = conc_init_clss S\<close> and
    conc_learned_clss_reduce_trail_to_abs[simp]:
    \<open>conc_learned_clss (reduce_trail_to_abs M S) = conc_learned_clss S\<close> and
    backtrack_lvl_abs_reduce_trail_to_abs[simp]:
    \<open>backtrack_lvl_abs (reduce_trail_to_abs M S) = backtrack_lvl_abs S\<close>
  using reduce_trail_to_abs[of S _ M] pq reduce_trail_to_lvl_exists_prepend[of \<open>trail_abs S\<close> k]
  by (auto simp: prop_state_def full_trail_abs_def)

lemma raw_conflicting_abs_reduce_trail_to_abs:
  \<open>trail_abs S = M2 @ M1 \<Longrightarrow> prop_queue_abs S = [] \<Longrightarrow>
  raw_conflicting_abs (reduce_trail_to_abs M1 S) = None \<longleftrightarrow> raw_conflicting_abs S = None\<close>
  using reduce_trail_to_abs[of S M2 M1]
  by (cases \<open>raw_conflicting_abs S\<close>) (fastforce simp: prop_state_def)+

schematic_goal
  fixes k :: nat and M :: "('a, 'b) ann_lit list"
  defines M1[symmetric, simp]: "M1 \<equiv> reduce_trail_to_lvl k M"
  shows H: \<open>M = ?M' @ reduce_trail_to_lvl k M\<close>
  using reduce_trail_to_lvl_exists_prepend[of M k]
  apply auto
  apply (rule sym)
  apply auto
  done

thm prop_state_cons_prop_queue_abs

lemma
  fixes S :: 'st
  defines M_def[simp]: "M \<equiv> tl (trail_abs S)"
  defines M1[simp]: "M1 \<equiv> reduce_trail_to_lvl (get_maximum_level M (the (conc_conflicting S))) (trail_abs S)"
  assumes
    inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state S)\<close> and
    inv': \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (state S)\<close> and
    ne: \<open>full_trail_abs S \<noteq> []\<close> and
    confl: \<open>conc_conflicting S \<noteq> None\<close> \<open>conc_conflicting S \<noteq> Some {#}\<close> and
    hd: \<open>hd_raw_trail_abs S = Decided L\<close> and
    pq[simp]: \<open>prop_queue_abs S = []\<close>
  shows \<open>cdcl\<^sub>W_restart_mset.backtrack (state S) (state (backtrack_implementation L S))\<close>
proof -
  obtain D' where D': "raw_conflicting_abs S = Some D'"
    using confl by auto
  obtain K where
    K: \<open>trail (state S) = K @ M1\<close>
    using H[of \<open>full_trail_abs S\<close> \<open>get_maximum_level (tl (full_trail_abs S)) (mset_ccls D')\<close>] D'
    unfolding M1 by (auto simp: full_trail_abs_def)
  have M1': \<open> M1 =
    full_trail_abs (reduce_trail_to_abs (reduce_trail_to_lvl (get_maximum_level (tl (full_trail_abs S)) (mset_ccls D')) (full_trail_abs S)) S)\<close>
    using D' K reduce_trail_to_abs[of S _ M1] by (auto simp: full_trail_abs_def prop_state_def)
  let ?T_confl = \<open>(update_backtrack_lvl_abs (get_maximum_level (tl (full_trail_abs S)) (mset_ccls D'))
      (reduce_trail_to_abs
         (reduce_trail_to_lvl (get_maximum_level (tl (full_trail_abs S)) (mset_ccls D'))
           (full_trail_abs S)) S))\<close>
  let ?T = \<open>add_confl_to_learned_cls_abs ?T_confl\<close>
  obtain T' it where T': \<open>?T = (T', it)\<close>
    by (cases \<open>?T\<close> )auto
  have \<open>no_dup (full_trail_abs ?T_confl)\<close>
    using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
     cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def K
    unfolding M1[unfolded M_def, symmetric, simp] M1'[symmetric]
    by (auto intro!: H simp: K M1[symmetric, simp] M1'[symmetric] simp del: M1)
  moreover have \<open>conc_conflicting ?T_confl = None \<Longrightarrow> False\<close>
    using confl
    apply simp
    apply (subst (asm) raw_conflicting_abs_reduce_trail_to_abs)
    apply (auto intro: H simp: full_trail_abs_def
        raw_conflicting_abs_reduce_trail_to_abs)
    done
  ultimately have \<open>valid_annotation (fst ?T) (Propagated L (snd ?T))\<close>
    using add_confl_to_learned_cls_abs_valid[of "?T_confl"] unfolding T'
    by (fastforce simp: in_clss_def M1' M1[symmetric] prop_state_def simp del: M1)

  have \<open>backtrack_lvl_abs S = count_decided (full_trail_abs S)\<close>
    using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
     cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by auto
  moreover {
    have H: \<open>full_trail_abs S = Decided L # tl (full_trail_abs S)\<close>
      using hd hd_raw_trail_abs[OF ne] ne by (cases \<open>full_trail_abs S\<close>) auto
    have \<open>count_decided (tl (full_trail_abs S)) < count_decided (full_trail_abs S)\<close>
      by (subst (2) H) auto }
  ultimately have
    M: \<open>get_maximum_level (tl (full_trail_abs S)) (the (conc_conflicting S)) < backtrack_lvl_abs S\<close>
    using count_decided_ge_get_maximum_level[of \<open>tl (full_trail_abs S)\<close> \<open>the (conc_conflicting S)\<close>]
    by auto
  let ?U = \<open>cons_trail (Propagated (- lit_of (hd (full_trail_abs S))) (the (conc_conflicting S)))
     (cdcl\<^sub>W_restart_mset.reduce_trail_to (reduce_trail_to_lvl (get_maximum_level (tl (full_trail_abs S)) (the (conc_conflicting S))) (full_trail_abs S))
       (add_learned_cls (the (conc_conflicting S)) (update_backtrack_lvl (get_maximum_level (tl (full_trail_abs S)) (the (conc_conflicting S))) (update_conflicting None (state S)))))\<close>
  have bt: \<open>cdcl\<^sub>W_restart_mset.backtrack (state S) ?U\<close>
    apply (rule backtrack_rule_reduce_trail_to_lvl)
          using inv apply (simp; fail)
         using inv' apply (simp; fail)
        using confl apply (auto; fail)[]
       using confl apply (auto; fail)[]
      using hd ne hd_raw_trail_abs[of S] apply (auto simp: cdcl\<^sub>W_restart_mset.skip.simps
          simp del: hd_raw_trail_abs)[]
     using M apply (simp; fail)
    apply (auto; fail)
    done
  then have inv_U: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv ?U\<close>
    using inv by (auto dest!: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o.intros
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_bj.intros cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_restart.intros
        intro: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_inv)
  have eq: \<open>?U \<sim>m state (backtrack_implementation L S)\<close>
    using D'
    using ne confl
    apply (auto simp: state_eq_def
        backtrack_implementation_def backtrack_implementation_lvl_def Let_def
        M1[symmetric] M1'[symmetric] T'
        simp del: CDCL_W_Abstract_State.cdcl\<^sub>W_restart_mset.state_simp M1)[]
    using inv_U unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def

      sorry

  show ?thesis
    using cdcl\<^sub>W_restart_mset.backtrack_state_eq_compatible[OF bt _ eq]
    inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def by auto

oops

definition cdcl_bj_implementation :: "'st \<Rightarrow> 'st" where
"cdcl_bj_implementation S =
  (if conc_conflicting S = None \<or> conc_conflicting S = Some {#} then S
  else
    case hd_raw_trail_abs S of
      Decided L \<Rightarrow> backtrack_implementation L S
    | Propagated L C \<Rightarrow>
      if -L \<in># mset_ccls (the (raw_conflicting_abs S))
      then
        if get_maximum_level (full_trail_abs S) (mset_ccls (the (raw_conflicting_abs S)) - {#-L#})
        < backtrack_lvl_abs S
        then backtrack_implementation L S
        else resolve_implementation L C S
      else skip_implementation S)"

lemma full_trail_abs_hd_rase_trail_abs:
  assumes \<open>full_trail_abs S = Propagated La C' # M\<close>
    \<open>hd_raw_trail_abs S = Propagated L C\<close>
  shows \<open>L = La\<close> and \<open>C' = clause_of_cls (raw_clauses_abs S \<Down> C)\<close>
  using assms hd_raw_trail_abs[of S] by auto

lemma get_maximum_level_cong:
  assumes M_M': \<open>M = M'\<close> and D_D': \<open>atms_of D = atms_of D'\<close>
  shows \<open>get_maximum_level M D = get_maximum_level M' D'\<close>
proof -
  have in_D_D': \<open>L \<in># D' \<or>  -L \<in># D'\<close> if \<open>L \<in># D\<close> for L
    using D_D' that
    by (auto simp: atms_of_def atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set[symmetric])
  have in_D'_D: \<open>L \<in># D \<or>  -L \<in># D\<close> if \<open>L \<in># D'\<close> for L
    using D_D' that
    by (auto simp: atms_of_def atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set[symmetric])
  have H: \<open> - L \<in># D \<Longrightarrow> get_level M' L = get_level M' (-L)\<close> for L D
    by auto
  have \<open>get_level M' ` set_mset D = get_level M' ` set_mset D'\<close>
    apply (standard; standard)
     apply (auto simp: H dest!: in_D_D' simp del: atm_of_uminus; fail)[]
    by (auto simp: H  dest!: in_D'_D simp del: atm_of_uminus)[]
  then show ?thesis
    using M_M' unfolding get_maximum_level_def by auto
qed

lemma hd_full_trail_abs:
  \<open>full_trail_abs S \<noteq> [] \<Longrightarrow>
       hd_raw_trail_abs S = Propagated L C \<Longrightarrow>
      hd (full_trail_abs S) = Propagated L (clause_of_cls (raw_clauses_abs S \<Down> C))\<close>
  using hd_raw_trail_abs[of S] by auto

lemma cdcl_bj_implementation_cases[consumes 1, case_names confl_None confl_False Decide_backtrack
    Propagate_backtrack Propagate_Resolve Propagate_skip]:
  assumes
    inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state S)\<close> and
    \<open>conc_conflicting S = None \<Longrightarrow> P S S\<close> and
    \<open>conc_conflicting S = Some {#} \<Longrightarrow> P S S\<close> and
    \<open>\<And>L. full_trail_abs S \<noteq> [] \<Longrightarrow> hd_raw_trail_abs S = Decided L \<Longrightarrow>
      P S (backtrack_implementation L S)\<close> and
    \<open>\<And>L C. full_trail_abs S \<noteq> [] \<Longrightarrow> hd_raw_trail_abs S = Propagated L C \<Longrightarrow>
      -L \<in># mset_ccls (the (raw_conflicting_abs S)) \<Longrightarrow>
      get_maximum_level (full_trail_abs S) (mset_ccls (the (raw_conflicting_abs S)) - {#-L#})
        < backtrack_lvl_abs S \<Longrightarrow> no_step cdcl\<^sub>W_restart_mset.skip (state S) \<Longrightarrow>
        no_step cdcl\<^sub>W_restart_mset.resolve (state S) \<Longrightarrow>
       P S (backtrack_implementation L S)\<close> and
    \<open>\<And>L C. full_trail_abs S \<noteq> [] \<Longrightarrow> hd_raw_trail_abs S = Propagated L C \<Longrightarrow>
      -L \<in># mset_ccls (the (raw_conflicting_abs S)) \<Longrightarrow>
       \<not>get_maximum_level (full_trail_abs S) (mset_ccls (the (raw_conflicting_abs S)) - {#-L#})
        < backtrack_lvl_abs S \<Longrightarrow>
       P S (resolve_implementation L C S)\<close> and
    \<open>\<And>L C. full_trail_abs S \<noteq> [] \<Longrightarrow> hd_raw_trail_abs S = Propagated L C \<Longrightarrow>
      -L \<notin># mset_ccls (the (raw_conflicting_abs S)) \<Longrightarrow> P S (skip_implementation S)\<close>
  shows \<open>P S (cdcl_bj_implementation S)\<close>
proof -
  have \<open>conc_conflicting S \<noteq> Some {#} \<Longrightarrow> conc_conflicting S \<noteq> None \<Longrightarrow> full_trail_abs S \<noteq> []\<close>
    using inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
    by auto
  moreover have \<open>full_trail_abs S \<noteq> [] \<Longrightarrow>conc_conflicting S \<noteq> None \<Longrightarrow> - L \<in># (the (conc_conflicting S)) \<Longrightarrow>
       hd_raw_trail_abs S = Propagated L C \<Longrightarrow> no_step cdcl\<^sub>W_restart_mset.skip (state S)\<close>
       for L C
    by (auto simp: cdcl\<^sub>W_restart_mset.skip.simps
        dest: full_trail_abs_hd_rase_trail_abs)
  ultimately show ?thesis
    by (auto simp: cdcl_bj_implementation_def split: ann_lit.splits
        elim!: cdcl\<^sub>W_restart_mset.resolveE intro: assms)
qed



text \<open>When we update a clause with respect to the literal L, there are several cases:
  \<^enum> the only literal is L: this is a conflict.
  \<^enum> if the other watched literal is true, there is noting to do.
  \<^enum> if it is false, then we have found a conflict (since every unwatched literal has to be false).
  \<^enum> otherwise, we have to check if we can find a literal to swap or propagate the variable.
\<close>

fun update_watched_clause :: "'st \<Rightarrow> 'v literal \<Rightarrow> 'cls_it \<Rightarrow> 'st"  where
"update_watched_clause S L i =
  (case it_of_watched_ordered (raw_clauses_abs S \<Down> i) L of
    [_] \<Rightarrow> mark_conflicting_abs i S
  | [j, k] \<Rightarrow>
    if ((raw_clauses_abs S \<Down> i) \<down> k) \<in> lits_of_l (trail_abs S)
    then S
    else if -((raw_clauses_abs S \<Down> i) \<down> k) \<in> lits_of_l (trail_abs S)
    then mark_conflicting_abs i S
    else
      (case find_undef_in_unwatched S (raw_clauses_abs S \<Down> i) of
        None \<Rightarrow> cons_prop_queue_abs (Propagated L i) S
      | Some _ \<Rightarrow> update_clause S i (swap_lit (raw_clauses_abs S \<Down> i) j k))
  )"

lemma
  fixes i :: 'cls_it and S :: 'st and L :: "'v literal"
  defines S': "S' \<equiv> update_watched_clause S L i"
  assumes
    "cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state S)" and
    L: "L \<in># watched (twl_clause (raw_clauses_abs S \<Down> i))" and
    confl: "raw_conflicting_abs S = None" and
    i: "i \<in>\<Down> raw_clauses_abs S" and
    L_trail: "- L \<in> lits_of_l (full_trail_abs S)"
  shows "propagate_abs S S' \<or> conflict_abs S S'"
proof -
  let ?C = "raw_clauses_abs S \<Down> i"
  consider
    (single_watched) j :: 'lit where "it_of_watched_ordered ?C L = [j]" and
      "lit_lookup ?C j = Some L" and "wf_unwatched_lits ?C = {#}" and
      "wf_watched_lits (raw_clauses_abs S \<Down> i) = {#j#}" |
    (two_watched) j k :: 'lit where "it_of_watched_ordered ?C L = [j, k]" and
      "lit_lookup ?C j = Some L" and "lit_lookup ?C k \<noteq> None" and
      "wf_watched_lits (raw_clauses_abs S \<Down> i) = {#j, k#}"
    using it_of_watched_ordered_cases[OF L] by blast
  then show ?thesis
    proof cases
      case (single_watched j) note it = this(1) and lit = this(2) and C = this(3) and W = this(4)
      moreover
        have iL: "clause_of_cls (raw_clauses_abs S \<Down> i) = {#L#}"
          by (auto simp: clause_map_wf_twl_clause_wf_clause wf_clause_def C
             W lit unwatched_twl_clause_twl_cls_wff_iff[symmetric] clause_of_cls_def)
        have "conflict_abs S (mark_conflicting_abs i S)"
          apply (rule conflict_abs_rule[of _ i])
             using confl apply auto[]
            using i apply simp
           using L_trail iL apply simp
          by auto
      ultimately show ?thesis
        unfolding S' by auto
    next
      case (two_watched j k) note jk = this(1) and it_L = this(2) and k = this(3)
      moreover {
        have \<open>no_dup (trail_abs S)\<close>
          sorry
        then have \<open>- L \<in> lits_of_l (trail_abs S) \<Longrightarrow>  L \<notin> lits_of_l (trail_abs S)\<close> for L
          using consistent_interp_def distinct_consistent_interp by blast
        then have [simp]: \<open>- ((raw_clauses_abs S \<Down> i) \<down> k) \<in> lits_of_l (trail_abs S) \<Longrightarrow>
          ((raw_clauses_abs S \<Down> i) \<down> k) \<notin> lits_of_l (trail_abs S)\<close>
          by blast }
      ultimately show ?thesis
         unfolding S' apply auto
oops

text \<open>Possible optimisation: @{term "Option.is_none (raw_conflicting_abs S')"} is the same as
  checking whether conflict has been marked by @{term update_watched_clause}.\<close>
fun update_watched_clauses  :: "'st \<Rightarrow> 'v literal \<Rightarrow> 'cls_it list \<Rightarrow> 'st" where
"update_watched_clauses S L (i # Cs) =
  (let S' = update_watched_clause S L i in
    if Option.is_none (raw_conflicting_abs S')
    then update_watched_clauses S' L Cs
    else S')" |
"update_watched_clauses S L [] = S"

definition propagate_and_conflict_one_lit where
"propagate_and_conflict_one_lit S L =
  update_watched_clauses S L (get_clause_watched_by S L)"

lemma raw_conflicting_abs_mark_conflicting_abs:
  assumes "i \<in>\<Down> raw_clauses_abs S" and "raw_conflicting_abs S = None"
  shows "raw_conflicting_abs (mark_conflicting_abs i S) \<noteq> None"
  by (metis (no_types) \<open>i \<in>\<Down> raw_clauses_abs S\<close> \<open>raw_conflicting_abs S = None\<close>
    conc_conflicting_mark_conflicting conflicting_None_iff_raw_conflicting
    conflicting_conc_conflicting option.distinct(1))

lemma
  assumes "Option.is_none (raw_conflicting_abs S)" and "-L \<in> lits_of_l (full_trail_abs S)"
  shows
    "state S = state (propagate_and_conflict_one_lit S L) \<or>
    conflict_abs S (propagate_and_conflict_one_lit S L)"
  using assms unfolding propagate_and_conflict_one_lit_def
proof (induction "get_clause_watched_by S L" arbitrary: S L)
  case Nil
  then show ?case by auto
next
  case (Cons i Cs) note IH = this(1) and watched = this(2)[symmetric] and confl = this(3) and
    L = this(4)
  let ?C = "raw_clauses_abs S \<Down> i"
  have "L \<in># watched (twl_clause ?C)"
    using get_clause_watched_by[of i S L] unfolding watched by simp
  then have [simp]: "it_of_watched_ordered ?C L \<noteq> []" and
    "lit_lookup (raw_clauses_abs S \<Down> i) (hd (it_of_watched_ordered (raw_clauses_abs S \<Down> i) L)) = Some L"
    using it_of_watched_ordered[of L ?C] by auto

  have "L \<in># watched (twl_clause ?C)" and "i \<in>\<Down> raw_clauses_abs S"
    using get_clause_watched_by[of i S L] unfolding watched by auto
  then have [simp]: "\<not>Option.is_none (raw_conflicting_abs (mark_conflicting_abs i S))"
    using confl raw_conflicting_abs_mark_conflicting_abs[of i S] by (auto simp: Option.is_none_def)
  show ?case
    unfolding watched
    apply (auto simp: )
oops


function (domintros) propagate_and_conflict where
"propagate_and_conflict S =
  (if prop_queue_abs_null S
  then S
  else
    let S' = prop_queue_to_trail_abs S in
    propagate_and_conflict (propagate_and_conflict_one_lit S' (lit_of (hd_raw_trail_abs S'))))"
by auto

end

end