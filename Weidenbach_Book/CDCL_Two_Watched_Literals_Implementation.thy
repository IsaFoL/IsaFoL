(*  Title: Implementation of CDCL with Two Watched Literals
    Author: Mathias Fleury <mathias.fleury@mpi-inf.mpg.de>
*)

subsection \<open>Implementation for 2 Watched-Literals\<close>

theory CDCL_Two_Watched_Literals_Implementation
imports CDCL_W_Abstract_State CDCL_Two_Watched_Literals
begin

sledgehammer_params[spy]

text \<open>The following locale axiomatizes a type introduced by the @{text typedef} command, by
  assuming that all generated theorems are true. This is necessary because one cannot create a new
  type in a locale.\<close>
locale type_definition_locale =
  fixes Abs :: "'a \<Rightarrow> 'inv" and Rep :: "'inv \<Rightarrow> 'a" and inv :: "'a \<Rightarrow> bool"
  assumes
    Rep_inv: "Abs (Rep x) = x" and
    Rep: "Rep x \<in> {a. inv a}" and
    Rep_inject: "Rep x = Rep y \<longleftrightarrow> x = y" and
    Abs_inverse: "z \<in> {a. inv a} \<Longrightarrow> Rep (Abs z) = z" and
    Abs_induct: "(\<And>y. y \<in> {a. inv a} \<Longrightarrow> P (Abs y)) \<Longrightarrow> P y" and
    Rep_induct: "z \<in> {a. inv a} \<Longrightarrow> (\<And>z. P' (Rep z)) \<Longrightarrow> P' z" and
    Abs_cases: "(\<And>y. x = Abs y \<Longrightarrow> y \<in> {a. inv a} \<Longrightarrow> Q) \<Longrightarrow> Q" and
    Rep_cases: "z \<in> {a. inv a} \<Longrightarrow> (\<And>y. z = Rep y \<Longrightarrow> Q) \<Longrightarrow> Q" and
    Abs_inject: "z \<in> {a. inv a} \<Longrightarrow> z' \<in> {a. inv a} \<Longrightarrow> Abs z = Abs z' \<longleftrightarrow> z = z'"

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
  fixes
    lit_lookup :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'v literal option" and
    lit_keys :: "'cls \<Rightarrow> 'lit multiset" and

    twl_cls :: "'cls \<Rightarrow> 'lit wf_twl_clause" and
    swap_lit :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'lit \<Rightarrow> 'cls" and
    it_of_watched_ordered :: "'cls \<Rightarrow> 'v literal \<Rightarrow> 'lit list" and
    cls_of_twl_list :: "'v literal list twl_clause \<Rightarrow> 'cls"
begin
term map_twl_clause
abbreviation twl_clause :: "'cls \<Rightarrow> 'v literal multiset twl_clause" where
"twl_clause C \<equiv> map_wf_twl_clause (image_mset (\<lambda>L. the (lit_lookup C L))) (twl_cls C)"

abbreviation clause_of_cls :: "'cls \<Rightarrow> 'v clause" where
"clause_of_cls C \<equiv> clause (twl_clause C)"

lemma wf_watched_watched_empty_iff:
  "wf_watched (twl_cls C) = {#} \<longleftrightarrow> watched (twl_clause C) = {#}"
proof -
  obtain twl_C where
    C: "twl_cls C = wf_of_twl_clause twl_C" and wf: "twl_C \<in> {C. struct_wf_twl_cls C}"
    by (cases "twl_cls C")
  obtain W UW where
    twl_C: "twl_C = TWL_Clause W UW"
    by (cases twl_C)
  have "wf_watched (twl_cls C) = {#} \<longleftrightarrow> wf_clause (twl_cls C) = {#}"
    using wf unfolding C twl_C
    by (auto simp: wf_clause_watched_unwatched wf_of_twl_clause_inverse wf_watched.rep_eq
      wf_unwatched.rep_eq)
  also have "wf_clause (twl_cls C) = {#} \<longleftrightarrow> clause_of_cls C = {#}"
    by (auto simp: clause_map_wf_twl_clause_wf_clause)
  also have "clause_of_cls C = {#} \<longleftrightarrow> watched (twl_clause C) = {#}"
    using wf unfolding C twl_C
    by (auto simp: clause_map_wf_twl_clause_wf_clause watched_map_wf_twl_clause
      wf_of_twl_clause_inverse wf_watched.rep_eq wf_unwatched.rep_eq
      wf_clause_watched_unwatched)
  finally show ?thesis .
qed

end


locale abstract_clause_representation =
  abstract_clause_representation_ops lit_lookup lit_keys twl_cls swap_lit
    it_of_watched_ordered cls_of_twl_list
  for
    lit_lookup :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'v literal option" and
    lit_keys :: "'cls \<Rightarrow> 'lit multiset" and

    twl_cls :: "'cls \<Rightarrow> 'lit wf_twl_clause" and
    swap_lit :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'lit \<Rightarrow> 'cls" and
    it_of_watched_ordered :: "'cls \<Rightarrow> 'v literal \<Rightarrow> 'lit list" and
    cls_of_twl_list :: "'v literal list twl_clause \<Rightarrow> 'cls" +
  assumes
    distinct_lit_keys[simp]: "distinct_mset (lit_keys C)" and
    valid_lit_keys: "i \<in># lit_keys C \<longleftrightarrow> lit_lookup C i \<noteq> None" and
    swap_lit:
      "j \<in># wf_watched (twl_cls C) \<Longrightarrow> k \<in># wf_unwatched (twl_cls C) \<Longrightarrow>
        twl_clause_of_wf (twl_cls (swap_lit C j k)) =
          TWL_Clause
            ({#k#} + remove1_mset j (wf_watched (twl_cls C)))
            ({#j#} + remove1_mset k (wf_unwatched (twl_cls C)))" and

    it_of_watched_ordered:
      "L \<in># watched (twl_clause C) \<Longrightarrow>
         mset (it_of_watched_ordered C L) = wf_watched (twl_cls C) \<and>
         lit_lookup C (hd (it_of_watched_ordered C L)) = Some L" and

    twl_cls_valid: -- \<open>this states that all the valid indexes are included in @{term "twl_cls C"}.\<close>
      "lit_keys C = wf_clause (twl_cls C)" and

    cls_of_twl_list:
      "distinct (watched D @ unwatched D) \<Longrightarrow>
        twl_clause (cls_of_twl_list D) = map_twl_clause mset D"
begin

lemma lit_lookup_Some_in_clause_of_cls:
  assumes L: "lit_lookup C i = Some L"
  shows "L \<in># clause_of_cls C"
proof -
  have "i \<in># wf_clause (twl_cls C)"
     using L by (auto simp: valid_lit_keys twl_cls_valid[symmetric])
  then have "L \<in> (\<lambda>l. the (lit_lookup C l)) ` set_mset (wf_clause (twl_cls C))"
    by (metis (no_types) assms image_eqI option.sel)
  then show ?thesis
    by (auto simp:clause_map_wf_twl_clause_wf_clause)
qed

lemma clause_of_cls_valid_lit_lookup:
  assumes L: "L \<in># clause_of_cls C"
  shows "\<exists>i. lit_lookup C i = Some L"
proof -
  obtain i where
    "L = the (lit_lookup C i)" and
    "i \<in># wf_clause (twl_cls C)"
    using L by (cases "twl_cls C") (auto simp: clause_map_wf_twl_clause_wf_clause)
  then have "lit_lookup C i = Some L"
    by (auto simp: twl_cls_valid[symmetric] valid_lit_keys)
  then show ?thesis by blast
qed

sublocale abstract_with_index where
  get_lit = lit_lookup and
  convert_to_mset = clause_of_cls
  by unfold_locales (auto simp: lit_lookup_Some_in_clause_of_cls clause_of_cls_valid_lit_lookup)


lemma it_of_watched_ordered_not_None:
  assumes
    L: "L \<in># watched (twl_clause C)" and
    it: "it_of_watched_ordered C L = [j, k]"
  shows
    "lit_lookup C j = Some L" and
    "lit_lookup C k \<noteq> None"
proof -
  have jk: "{#j, k#} = wf_watched (twl_cls C)" and
    j: "lit_lookup C j = Some L"
    using it_of_watched_ordered[OF L] unfolding it by (auto simp: ac_simps)
  have k: "k \<in># wf_clause (twl_cls C)"
    using jk[symmetric] by (auto simp: wf_clause_watched_unwatched)

  show "lit_lookup C j = Some L"
    using j by simp
  show "lit_lookup C k \<noteq> None"
    using k unfolding valid_lit_keys[symmetric] twl_cls_valid by auto
qed

lemma unwatched_twl_clause_twl_clause_of_wff_iff:
  "unwatched (twl_clause C) = {#} \<longleftrightarrow> unwatched (twl_clause_of_wf (twl_cls C)) = {#}"
  apply (cases "twl_cls C")
  apply (rename_tac y, case_tac y)
  by (auto simp: unwatched_map_wf_twl_clause wf_unwatched.rep_eq)

lemma it_of_watched_ordered_cases:
  assumes L: "L \<in># watched (twl_clause C)"
  shows
    "(\<exists>j. it_of_watched_ordered C L = [j] \<and> lit_lookup C j = Some L \<and>
      unwatched (twl_clause C) = {#} \<and>  wf_watched (twl_cls C) = {#j#}) \<or>
     (\<exists>j k. it_of_watched_ordered C L = [j, k] \<and> lit_lookup C j = Some L \<and> lit_lookup C k \<noteq> None \<and>
        wf_watched (twl_cls C) = {#j, k#})"
proof -
  have "size (mset (it_of_watched_ordered C L)) \<le> 2"
    using it_of_watched_ordered[OF assms] twl_clause_of_wf[of "twl_cls C"]
    by (cases "twl_clause_of_wf (twl_cls C)") (auto simp add: wf_watched.rep_eq)
  moreover have "it_of_watched_ordered C L \<noteq> []"
    using assms by (metis image_mset_is_empty_iff insert_DiffM it_of_watched_ordered mset.simps(1)
      single_not_empty union_eq_empty watched_map_wf_twl_clause)
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
          using twl_clause_of_wf[of "twl_cls C"] it_of_watched_ordered[OF assms]
          apply (auto simp add:)
          apply (cases "twl_clause_of_wf (twl_cls C)")
          by (auto simp: j wf_watched.rep_eq subset_eq_mset_single_iff
            distinct_mset_size_2 unwatched_twl_clause_twl_clause_of_wff_iff)
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
      "add_cls Cs C = (Cs', i) \<Longrightarrow> cls_lookup Cs' = (cls_lookup Cs) (i := Some C)"  and
    add_cls_new_keys:
      "add_cls Cs C = (Cs', i) \<Longrightarrow> i \<notin># cls_keys Cs"
begin

lemma add_cls_new_key:
  "add_cls Cs C = (Cs', i) \<Longrightarrow> i \<in># cls_keys Cs'"
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
  abstract_clause_representation lit_lookup lit_keys twl_cls swap_lit
    it_of_watched_ordered cls_of_twl_list +
  abstract_clauses_representation cls_lookup cls_keys clss_update add_cls
  for
    lit_lookup :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'v literal option" and
    lit_keys :: "'cls \<Rightarrow> 'lit multiset" and

    twl_cls :: "'cls \<Rightarrow> 'lit wf_twl_clause" and
    swap_lit :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'lit \<Rightarrow> 'cls" and
    it_of_watched_ordered :: "'cls \<Rightarrow> 'v literal \<Rightarrow> 'lit list" and

    cls_of_twl_list :: "'v literal list twl_clause \<Rightarrow> 'cls" and
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
    lit_lookup lit_keys twl_cls swap_lit
    it_of_watched_ordered cls_of_twl_list

    cls_lookup cls_keys clss_update add_cls
    +
  raw_cls mset_ccls
  for
    \<comment> \<open>Clause:\<close>
    lit_lookup :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'v literal option" and
    lit_keys :: "'cls \<Rightarrow> 'lit multiset" and

    twl_cls :: "'cls \<Rightarrow> 'lit wf_twl_clause" and
    swap_lit :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'lit \<Rightarrow> 'cls" and
    it_of_watched_ordered :: "'cls \<Rightarrow> 'v literal \<Rightarrow> 'lit list" and

    \<comment> \<open>Clauses\<close>
    cls_of_twl_list :: "'v literal list twl_clause \<Rightarrow> 'cls" and
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
    lit_lookup lit_keys twl_cls swap_lit
    it_of_watched_ordered cls_of_twl_list

    cls_lookup cls_keys clss_update add_cls

    \<comment> \<open>functions for the conflicting clause:\<close>
    mset_ccls
  for
    \<comment> \<open>Clause:\<close>
    lit_lookup :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'v literal option" and
    lit_keys :: "'cls \<Rightarrow> 'lit multiset" and

    twl_cls :: "'cls \<Rightarrow> 'lit wf_twl_clause" and
    swap_lit :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'lit \<Rightarrow> 'cls" and
    it_of_watched_ordered :: "'cls \<Rightarrow> 'v literal \<Rightarrow> 'lit list" and

    \<comment> \<open>Clauses\<close>
    cls_of_twl_list :: "'v literal list twl_clause \<Rightarrow> 'cls" and
    cls_lookup :: "'clss \<Rightarrow> 'cls_it \<Rightarrow> 'cls option" and
    cls_keys :: "'clss \<Rightarrow> 'cls_it multiset" and
    clss_update :: "'clss \<Rightarrow> 'cls_it \<Rightarrow> 'cls \<Rightarrow> 'clss" and
    add_cls :: "'clss \<Rightarrow> 'cls \<Rightarrow> 'clss \<times> 'cls_it" and

    \<comment> \<open>Conflicting clause:\<close>
    mset_ccls :: "'ccls \<Rightarrow> 'v clause" +
  fixes
    find_undef_in_unwatched :: "'st \<Rightarrow> 'cls \<Rightarrow> 'lit option" and
    abs_trail :: "'st \<Rightarrow> ('v, 'v clause) ann_lits" and
    hd_raw_abs_trail :: "'st \<Rightarrow> ('v, 'cls_it) ann_lit" and
    prop_queue :: "'st \<Rightarrow> ('v, 'v clause) ann_lits" and
    raw_clauses :: "'st \<Rightarrow> 'clss" and
    abs_backtrack_lvl :: "'st \<Rightarrow> nat" and
    raw_conc_conflicting :: "'st \<Rightarrow> 'ccls option" and

    abs_learned_clss :: "'st \<Rightarrow> 'v clauses" and

    tl_abs_trail :: "'st \<Rightarrow> 'st" and
    reduce_abs_trail_to :: "('v, 'v clause) ann_lits \<Rightarrow> 'st \<Rightarrow> 'st" and

    cons_prop_queue :: "('v, 'cls_it) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    last_prop_queue_to_trail :: "'st \<Rightarrow> 'st" and
    prop_queue_null :: "'st \<Rightarrow> bool" and
    prop_queue_to_trail :: "'st \<Rightarrow> 'st" and

    add_abs_confl_to_learned_cls :: "'st \<Rightarrow> 'st" and
    abs_remove_cls :: "'cls \<Rightarrow> 'st \<Rightarrow> 'st" and

    update_abs_backtrack_lvl :: "nat \<Rightarrow> 'st \<Rightarrow> 'st" and

    mark_conflicting :: "'cls_it \<Rightarrow> 'st \<Rightarrow> 'st" and
    resolve_abs_conflicting :: "'v literal \<Rightarrow> 'cls \<Rightarrow> 'st \<Rightarrow> 'st" and

    get_undecided_lit :: "'st \<Rightarrow> 'v literal option" and
    get_clause_watched_by :: "'st \<Rightarrow> 'v literal \<Rightarrow> 'cls_it list" and
    update_clause :: "'st \<Rightarrow> 'cls_it \<Rightarrow> 'cls \<Rightarrow> 'st" and

    abs_init_state :: "'clss \<Rightarrow> 'st" and
    restart_state :: "'st \<Rightarrow> 'st"
begin

definition full_trail :: "'st \<Rightarrow> ('v, 'v clause) ann_lits" where
"full_trail S = prop_queue S @ abs_trail S"

sublocale abs_state\<^sub>W_ops where
  cls_lit = lit_lookup and
  mset_cls = clause_of_cls and
  clss_cls = cls_lookup and
  mset_clss = raw_cls_of_clss and
  mset_ccls = mset_ccls and

  conc_trail = full_trail and
  hd_raw_conc_trail = hd_raw_abs_trail  and
  raw_clauses = raw_clauses and
  conc_backtrack_lvl = abs_backtrack_lvl and
  raw_conc_conflicting = raw_conc_conflicting and
  conc_learned_clss = abs_learned_clss and
  cons_conc_trail = cons_prop_queue and
  tl_conc_trail = "\<lambda>S. tl_abs_trail S" and
  add_conc_confl_to_learned_cls = "\<lambda>S. add_abs_confl_to_learned_cls S" and
  remove_cls = abs_remove_cls and
  update_conc_backtrack_lvl = update_abs_backtrack_lvl and
  mark_conflicting = "\<lambda>i S. mark_conflicting i S" and
  reduce_conc_trail_to = "\<lambda>M S. reduce_abs_trail_to M (prop_queue_to_trail S)" and
  resolve_conflicting = "\<lambda>L D S. resolve_abs_conflicting L D S" and
  conc_init_state = abs_init_state and
  restart_state = restart_state
  by unfold_locales

lemma mmset_of_mlit_abs_mlit[simp]: "mmset_of_mlit = abs_mlit"
  by (intro ext, rename_tac S L, case_tac L) auto

definition prop_state ::
    "'st \<Rightarrow> ('v, 'v clause) ann_lit list \<times> ('v, 'v clause) ann_lit list \<times> 'v clauses \<times>
      'v clauses \<times> nat \<times> 'v clause option" where
"prop_state S = (prop_queue S, abs_trail S, conc_init_clss S, abs_learned_clss S,
  abs_backtrack_lvl S, conc_conflicting S)"

lemma prop_state_state: "prop_state S = (P, M, N, U, k, C) \<Longrightarrow> state S = (P @ M, N, U, k, C)"
  unfolding prop_state_def state_def full_trail_def by auto

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
    it_of_watched_ordered cls_of_twl_list

    cls_lookup cls_keys clss_update add_cls

    \<comment> \<open>functions for the conflicting clause:\<close>
    mset_ccls

    find_undef_in_unwatched

    abs_trail hd_raw_abs_trail prop_queue raw_clauses abs_backtrack_lvl raw_conc_conflicting

    abs_learned_clss

    tl_abs_trail reduce_abs_trail_to

    cons_prop_queue last_prop_queue_to_trail prop_queue_null prop_queue_to_trail

    add_abs_confl_to_learned_cls abs_remove_cls

    update_abs_backtrack_lvl mark_conflicting resolve_abs_conflicting

    get_undecided_lit get_clause_watched_by update_clause

    abs_init_state restart_state

  for
    \<comment> \<open>Clause:\<close>
    lit_lookup :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'v literal option" and
    lit_keys :: "'cls \<Rightarrow> 'lit multiset" and

    twl_cls :: "'cls \<Rightarrow> 'lit wf_twl_clause" and
    swap_lit :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'lit \<Rightarrow> 'cls" and
    it_of_watched_ordered :: "'cls \<Rightarrow> 'v literal \<Rightarrow> 'lit list" and

    \<comment> \<open>Clauses\<close>
    cls_of_twl_list :: "'v literal list twl_clause \<Rightarrow> 'cls" and
    cls_lookup :: "'clss \<Rightarrow> 'cls_it \<Rightarrow> 'cls option" and
    cls_keys :: "'clss \<Rightarrow> 'cls_it multiset" and
    clss_update :: "'clss \<Rightarrow> 'cls_it \<Rightarrow> 'cls \<Rightarrow> 'clss" and
    add_cls :: "'clss \<Rightarrow> 'cls \<Rightarrow> 'clss \<times> 'cls_it" and

    \<comment> \<open>Conflicting clause:\<close>
    mset_ccls :: "'ccls \<Rightarrow> 'v clause" and

    find_undef_in_unwatched :: "'st \<Rightarrow> 'cls \<Rightarrow> 'lit option" and

    abs_trail :: "'st \<Rightarrow> ('v, 'v clause) ann_lits" and
    hd_raw_abs_trail :: "'st \<Rightarrow> ('v, 'cls_it) ann_lit" and
    prop_queue :: "'st \<Rightarrow> ('v, 'v clause) ann_lits" and
    raw_clauses :: "'st \<Rightarrow> 'clss" and
    abs_backtrack_lvl :: "'st \<Rightarrow> nat" and
    raw_conc_conflicting :: "'st \<Rightarrow> 'ccls option" and

    abs_learned_clss :: "'st \<Rightarrow> 'v clauses" and

    tl_abs_trail :: "'st \<Rightarrow> 'st" and
    reduce_abs_trail_to :: "('v, 'v clause) ann_lits \<Rightarrow> 'st \<Rightarrow> 'st" and

    cons_prop_queue :: "('v, 'cls_it) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    last_prop_queue_to_trail :: "'st \<Rightarrow> 'st" and
    prop_queue_null :: "'st \<Rightarrow> bool" and
    prop_queue_to_trail :: "'st \<Rightarrow> 'st" and

    add_abs_confl_to_learned_cls :: "'st \<Rightarrow> 'st" and
    abs_remove_cls :: "'cls \<Rightarrow> 'st \<Rightarrow> 'st" and

    update_abs_backtrack_lvl :: "nat \<Rightarrow> 'st \<Rightarrow> 'st" and

    mark_conflicting :: "'cls_it \<Rightarrow> 'st \<Rightarrow> 'st" and
    resolve_abs_conflicting :: "'v literal \<Rightarrow> 'cls \<Rightarrow> 'st \<Rightarrow> 'st" and

    get_undecided_lit :: "'st \<Rightarrow> 'v literal option" and
    get_clause_watched_by :: "'st \<Rightarrow> 'v literal \<Rightarrow> 'cls_it list" and
    update_clause :: "'st \<Rightarrow> 'cls_it \<Rightarrow> 'cls \<Rightarrow> 'st" and

    abs_init_state :: "'clss \<Rightarrow> 'st" and
    restart_state :: "'st \<Rightarrow> 'st" +
  assumes
    prop_state_cons_prop_queue:
      "\<And>T'. undefined_lit (full_trail T) (lit_of L) \<Longrightarrow>
        prop_state T = (P, T') \<Longrightarrow> valid_annotation T L \<Longrightarrow>
        prop_state (cons_prop_queue L T) = (abs_mlit (raw_clauses T) L # P,  T')" and

    last_prop_queue_to_trail_prop_state:
      "\<And>T'. prop_queue T \<noteq> [] \<Longrightarrow>
        prop_state T = (P, M, T') \<Longrightarrow>
        prop_state (last_prop_queue_to_trail T) =
           (but_last P, last P # M, T')" and
    prop_queue_to_trail_prop_state:
      "\<And>T'. prop_state T = (P, M, T') \<Longrightarrow>
        prop_state (prop_queue_to_trail T) = ([], P @ M, T')" and
    raw_conc_conflicting_prop_queue_to_trail[simp]:
      "raw_conc_conflicting (prop_queue_to_trail st) = raw_conc_conflicting st" and
    raw_clauses_prop_queue_to_trail[simp]:
      "raw_clauses (prop_queue_to_trail st) = raw_clauses st" and

    hd_raw_abs_trail:
      "full_trail st \<noteq> [] \<Longrightarrow>
        mmset_of_mlit (raw_clauses st) (hd_raw_abs_trail st) = hd (full_trail st)" and

    tl_abs_trail_prop_state:
      "\<And>S'. prop_state st = (P, M, S') \<Longrightarrow>
        prop_state (tl_abs_trail st) = (tl P, if P = [] then tl M else M, S')" and

    abs_remove_cls:
      "\<And>S'. prop_state st = (P, M, N, U, S') \<Longrightarrow>
        prop_state (abs_remove_cls C' st) =
          (P, M, removeAll_mset (clause_of_cls C') N, removeAll_mset (clause_of_cls C') U, S')" and

    add_abs_confl_to_learned_cls:
      "no_dup (full_trail st) \<Longrightarrow> prop_state st = (P, M, N, U, k, Some F) \<Longrightarrow>
        prop_state (add_abs_confl_to_learned_cls st) =
          (P, M, N, {#F#} + U, k, None)" and

    update_abs_backtrack_lvl:
      "\<And>S'. prop_state st = (P, M, N, U, k, S') \<Longrightarrow>
        prop_state (update_abs_backtrack_lvl k' st) = (P, M, N, U, k', S')" and

    mark_conflicting_prop_state:
      "prop_state st = (P, M, N, U, k, None) \<Longrightarrow> E \<in>\<Down> raw_clauses st \<Longrightarrow>
        prop_state (mark_conflicting E st) =
          (P, M, N, U, k, Some (clause_of_cls (raw_clauses st \<Down> E)))"
      and

    resolve_abs_conflicting:
      "prop_state st = (P, M, N, U, k, Some F) \<Longrightarrow> -L' \<in># F \<Longrightarrow> L' \<in># clause_of_cls D \<Longrightarrow>
        prop_state (resolve_abs_conflicting L' D st) =
          (P, M, N, U, k, Some (cdcl\<^sub>W_mset.resolve_cls L' F (clause_of_cls D)))" and

    prop_state_abs_init_state:
      "prop_state (abs_init_state Ns) = ([], [], clauses_of_clss Ns, {#}, 0, None)" and

    \<comment> \<open>Properties about restarting @{term restart_state}:\<close>
    prop_queue_restart_state[simp]: "prop_queue (restart_state S) = []" and
    abs_trail_restart_state[simp]: "abs_trail (restart_state S) = []" and
    conc_init_clss_restart_state[simp]: "conc_init_clss (restart_state S) = conc_init_clss S" and
    abs_learned_clss_restart_state[intro]:
      "abs_learned_clss (restart_state S) \<subseteq># abs_learned_clss S" and
    abs_backtrack_lvl_restart_state[simp]: "abs_backtrack_lvl (restart_state S) = 0" and
    conc_conflicting_restart_state[simp]: "conc_conflicting (restart_state S) = None" and

    \<comment> \<open>Properties about @{term reduce_abs_trail_to}:\<close>
    reduce_abs_trail_to:
      "\<And>S'. abs_trail st = M2 @ M1 \<Longrightarrow> prop_state st = ([], M, S') \<Longrightarrow>
        prop_state (reduce_abs_trail_to M1 st) = ([], M1, S')" and

    learned_clauses:
      "abs_learned_clss S \<subseteq># conc_clauses S" and

    get_undecided_lit_Some:
      "get_undecided_lit T = Some L' \<Longrightarrow> undefined_lit (abs_trail T) L' \<and>
        atm_of L' \<in> atms_of_mm (conc_clauses T)" and
    get_undecided_lit_None:
      "get_undecided_lit T = None \<longleftrightarrow>
         (\<forall>L'. atm_of L' \<in> atms_of_mm (conc_clauses T) \<longrightarrow> \<not>undefined_lit (abs_trail T) L')" and
    get_clause_watched_by:
      "i \<in> set (get_clause_watched_by T K) \<longleftrightarrow> (K \<in># watched (twl_clause (raw_clauses T \<Down> i)) \<and>
        i \<in>\<Down> raw_clauses S)" and
    get_clause_watched_by_distinct:
      "distinct (get_clause_watched_by T K)" and

    update_clause:
      "i \<in>\<Down> raw_clauses S \<Longrightarrow>
        raw_clauses (update_clause S i E') = clss_update (raw_clauses S) i E'" and
    update_clause_state:
      "i \<in>\<Down> raw_clauses S \<Longrightarrow> prop_state S = (P, M, N, U, k, C) \<Longrightarrow>
        prop_state (update_clause S i E') = (P, M, conc_init_clss S, abs_learned_clss S, k, C)" and

    find_undef_in_unwatched_Some:
      "find_undef_in_unwatched S E' = Some j \<Longrightarrow> j \<in>\<down> E' \<and> undefined_lit (full_trail S) (E'\<down>j) \<and>
        (E'\<down>j) \<in># unwatched (twl_clause E')" and
    find_undef_in_unwatched_None:
      "find_undef_in_unwatched S E' = None \<longleftrightarrow>
        (\<forall>j. j \<in>\<down> E' \<longrightarrow> (E'\<down>j) \<in># unwatched (twl_clause E') \<longrightarrow>
           \<not>undefined_lit (full_trail S) (E'\<down>j))" and

    prop_queue_null[iff]:
      "prop_queue_null S \<longleftrightarrow> List.null (prop_queue S)"
begin

lemma
  prop_queue_prop_queue_to_trail[simp]:
    "prop_queue (prop_queue_to_trail S) = []" and
  abs_trail_prop_queue_to_trail[simp]:
    "abs_trail (prop_queue_to_trail S) = prop_queue S @ abs_trail S" and
  full_trail_prop_queue_to_trail[simp]:
    "full_trail (prop_queue_to_trail S) = prop_queue S @ abs_trail S" and
  conc_init_clss_prop_queue_to_trail[simp]:
    "conc_init_clss (prop_queue_to_trail S) = conc_init_clss S" and
  abs_learned_clss_prop_queue_to_trail[simp]:
    "abs_learned_clss (prop_queue_to_trail S) = abs_learned_clss S" and
  abs_backtrack_lvl_prop_queue_to_trail[simp]:
    "abs_backtrack_lvl (prop_queue_to_trail S) = abs_backtrack_lvl S" and
  conc_conflicting_prop_queue_to_trail[simp]:
    "conc_conflicting (prop_queue_to_trail S) = conc_conflicting S"
  using prop_queue_to_trail_prop_state[of S "prop_queue S"]
  by (cases "prop_state (prop_queue_to_trail S)"; auto simp: prop_state_def full_trail_def; fail)+

lemma
  shows
    abs_trail_tl_abs_trail[simp]:
      "prop_queue (tl_abs_trail S) = tl (prop_queue S)" and
    full_trail_tl_abs_trail[simp]:
      "full_trail (tl_abs_trail S) = tl (full_trail S)" and
    conc_init_clss_tl_abs_trail[simp]:
      "conc_init_clss (tl_abs_trail S) = conc_init_clss S" and
    abs_learned_clss_tl_abs_trail[simp]:
      "abs_learned_clss (tl_abs_trail S) = abs_learned_clss S" and
    abs_backtrack_lvl_tl_abs_trail[simp]:
      "abs_backtrack_lvl (tl_abs_trail S) = abs_backtrack_lvl S" and
    conc_conflicting_tl_abs_trail[simp]:
      "conc_conflicting (tl_abs_trail S) = conc_conflicting S"
  using tl_abs_trail_prop_state[of S "prop_queue S" "abs_trail S"]
  by (cases "prop_state (tl_abs_trail S)"; auto simp: prop_state_def full_trail_def; fail)+

lemma
  assumes "raw_conc_conflicting S = Some F" and "no_dup (full_trail S)"
  shows
    prop_queue_add_abs_confl_to_learned_cls[simp]:
      "prop_queue (add_abs_confl_to_learned_cls S) = prop_queue S" and
    abs_trail_add_abs_confl_to_learned_cls[simp]:
      "abs_trail (add_abs_confl_to_learned_cls S) = abs_trail S" and
    full_trail_add_abs_confl_to_learned_cls[simp]:
      "full_trail (add_abs_confl_to_learned_cls S) = full_trail S" and
    conc_init_clss_add_abs_confl_to_learned_cls[simp]:
      "conc_init_clss (add_abs_confl_to_learned_cls S) = conc_init_clss S" and
    abs_learned_clss_add_abs_confl_to_learned_cls[simp]:
      "abs_learned_clss (add_abs_confl_to_learned_cls S) = {#mset_ccls F#} + abs_learned_clss S" and
    abs_backtrack_lvl_add_abs_confl_to_learned_cls[simp]:
      "abs_backtrack_lvl (add_abs_confl_to_learned_cls S) = abs_backtrack_lvl S" and
    conc_conflicting_add_abs_confl_to_learned_cls[simp]:
      "conc_conflicting (add_abs_confl_to_learned_cls S) = None"
  using add_abs_confl_to_learned_cls[of S _ "abs_trail S" _ _ _ "mset_ccls F"] assms
  by (cases "prop_state (add_abs_confl_to_learned_cls S)";
    auto simp: prop_state_def full_trail_def; fail)+

lemma state_cons_prop_queue:
  assumes
    undef: "undefined_lit (full_trail st) (lit_of L)" and
    st: "state st = (M, S')" and
    "valid_annotation st L"
  shows "state (cons_prop_queue L st) = (mmset_of_mlit (raw_clauses st) L # M, S')"
  using assms prop_state_cons_prop_queue[of st L "prop_queue st" "(abs_trail st, S')"]
  unfolding prop_state_def state_def full_trail_def by auto

lemma cons_conc_trail:
  assumes "state st = (M, S')"
  shows "state (tl_abs_trail st) = (tl M, S')"
  using assms tl_abs_trail_prop_state[of "prop_queue_to_trail st"
      "abs_trail (prop_queue_to_trail st)" _ S']
  unfolding prop_state_def state_def
  by auto

lemma remove_cls:
  assumes "state st = (M, N, U, S')"
  shows "state (abs_remove_cls C st) =
    (M, removeAll_mset (clause_of_cls C) N, removeAll_mset (clause_of_cls C) U, S')"
  using abs_remove_cls[of st "prop_queue st" "abs_trail st" "conc_init_clss st"
    "abs_learned_clss st"] assms
  unfolding prop_state_def state_def by (auto simp: full_trail_def)

lemma add_conc_confl_to_learned_cls:
  assumes "no_dup (full_trail st)" and
    "state st = (M, N, U, k, Some F)"
  shows "state (add_abs_confl_to_learned_cls st) = (M, N, {#F#} + U, k, None)"
  using add_abs_confl_to_learned_cls[of st _ _ N U k F] assms
  unfolding prop_state_def state_def by (auto simp: full_trail_def)

lemma mark_conflicting:
  assumes
    "state st = (M, N, U, k, None)" and
    "E \<in>\<Down> raw_clauses st"
  shows "state (mark_conflicting E st) =
    (M, N, U, k, Some (clause_of_cls (raw_clauses st \<Down> E)))"
  using mark_conflicting_prop_state[of st _ _ N U k E] assms
  unfolding prop_state_def state_def by (auto simp: full_trail_def)

lemma abs_init_state:
  "state (abs_init_state Ns) = ([], clauses_of_clss Ns, {#}, 0, None)"
  using prop_state_abs_init_state[of Ns] by (auto simp: state_def prop_state_def full_trail_def)

lemma reduce_conc_trail_to:
  assumes
    "full_trail st = M2 @ M1" and
    "state st = (M, S')"
  shows "state (reduce_abs_trail_to M1 (prop_queue_to_trail st)) = (M1, S')"
  using reduce_abs_trail_to[of "prop_queue_to_trail st" M2 M1 M S'] assms
  unfolding full_trail_def state_def prop_state_def by auto

lemma resolve_conflicting:
  assumes
    "state st = (M, N, U, k, Some F)" and
    "- L' \<in># F" and
    "L' \<in># clause_of_cls D"
  shows "state (resolve_abs_conflicting L' D st) =
    (M, N, U, k, Some (remove1_mset (- L') F #\<union> remove1_mset L' (clause_of_cls D)))"
  using resolve_abs_conflicting[of st _ _ N U k F L' D] assms
  unfolding full_trail_def state_def prop_state_def by auto

sublocale abs_state\<^sub>W where
  cls_lit = lit_lookup and
  mset_cls = clause_of_cls and
  clss_cls = cls_lookup and
  mset_clss = raw_cls_of_clss and
  mset_ccls = mset_ccls and

  conc_trail = full_trail and
  hd_raw_conc_trail = hd_raw_abs_trail  and
  raw_clauses = raw_clauses and
  conc_backtrack_lvl = abs_backtrack_lvl and
  raw_conc_conflicting = raw_conc_conflicting and
  conc_learned_clss = abs_learned_clss and
  cons_conc_trail = cons_prop_queue and
  tl_conc_trail = "\<lambda>S. tl_abs_trail S" and
  add_conc_confl_to_learned_cls = "\<lambda>S. add_abs_confl_to_learned_cls S" and
  remove_cls = abs_remove_cls and
  update_conc_backtrack_lvl = update_abs_backtrack_lvl and
  mark_conflicting = "\<lambda>i S. mark_conflicting i S" and
  reduce_conc_trail_to = "\<lambda>M S. reduce_abs_trail_to M (prop_queue_to_trail S)" and
  resolve_conflicting = "\<lambda>L D S. resolve_abs_conflicting L D S" and
  conc_init_state = abs_init_state and
  restart_state = restart_state
  apply unfold_locales
                  using hd_raw_abs_trail apply (simp; fail)
                 using state_cons_prop_queue apply (simp; fail)
                using cons_conc_trail apply (simp; fail)
               using remove_cls apply (simp; fail)
              using add_conc_confl_to_learned_cls apply (simp; fail)
             using prop_state_def prop_state_state update_abs_backtrack_lvl apply (auto; fail)[1]
            using mark_conflicting apply (simp; fail)
           using resolve_conflicting apply (blast; fail)
          using abs_init_state apply (simp; fail)
         apply (simp add: full_trail_def; fail)
        apply (simp add: full_trail_def; fail)
       apply (simp add: abs_learned_clss_restart_state; fail)
     using abs_backtrack_lvl_restart_state apply blast
    apply simp
   using reduce_conc_trail_to apply (blast; fail)
  apply (simp add: learned_clauses; fail)
  done

lemma conc_clauses_update_clause:
  assumes
    i: "i \<in>\<Down> raw_clauses S"
  shows
    "conc_clauses (update_clause S i E) =
       remove1_mset (clause_of_cls (raw_clauses S \<Down> i)) (conc_clauses S) + {#clause_of_cls E#}"
     (is "?abs = ?r")
proof-
  have XX: "\<And>x. clause_of_cls (the (if x = i then Some E else cls_lookup (raw_clauses S) x)) =
    (if x = i then clause_of_cls E else clause_of_cls (the (cls_lookup (raw_clauses S) x)))"
     by (auto simp: update_clause[OF i] clss_update split: if_splits)
  have YY: "remove1_mset (clause_of_cls (raw_clauses S \<Down> i))
    {#clause_of_cls (the (cls_lookup (raw_clauses S) x)). x \<in># cls_keys (raw_clauses S)#} =
    {#clause_of_cls (the (cls_lookup (raw_clauses S) x)).
       x \<in># remove1_mset i (cls_keys (raw_clauses S))#}"
     apply (subst subseteq_image_mset_minus)
     using i by (auto simp add: cls_keys in_clss_def clss_cls_def)

  have c: "count (cls_keys (raw_clauses S)) i = 1"

    by (meson cls_keys cls_keys_distinct distinct_mset_def i in_clss_def)
  then have [simp]: "replicate_mset (count (cls_keys (raw_clauses S)) i) (clause_of_cls E) =
    {#clause_of_cls E#}"
    by simp
  show ?thesis
     using i unfolding conc_clauses_def clauses_of_clss_def in_clss_def
     by (auto simp: update_clause[OF i] clss_update XX YY image_mset_if_eq_index
       distinct_mset_remove1_All)
qed

definition wf_prop_queue :: "'st \<Rightarrow> bool" where
"wf_prop_queue S \<longleftrightarrow> (\<forall>M \<in> set (prop_queue S). is_proped M)"

function all_annotation_valid where
"all_annotation_valid S \<longleftrightarrow>
  (if full_trail S = []
  then True
  else valid_annotation S (hd_raw_abs_trail S) \<and> all_annotation_valid (tl_abs_trail S))"
by auto
termination
  apply (relation "measure (\<lambda>S. length (full_trail S))")
  apply auto
  done

declare all_annotation_valid.simps[simp del]

lemma all_annotation_valid_simps[simp]:
  shows
    "full_trail S = [] \<Longrightarrow> all_annotation_valid S" and
    "full_trail S \<noteq> [] \<Longrightarrow> all_annotation_valid S = (valid_annotation S (hd_raw_abs_trail S)
      \<and> all_annotation_valid (tl_abs_trail S))"
    using all_annotation_valid.simps by metis+

definition wf_twl_state :: "'st \<Rightarrow> bool" where
"wf_twl_state S \<longleftrightarrow>
  (full_trail S \<noteq> [] \<longrightarrow> all_annotation_valid S) \<and>
  cdcl\<^sub>W_mset.cdcl\<^sub>W_all_struct_inv (state S) \<and>
  wf_prop_queue S"

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
    lit_lookup lit_keys twl_cls swap_lit
    it_of_watched_ordered cls_of_twl_list

    cls_lookup cls_keys clss_update add_cls

    \<comment> \<open>functions for the conflicting clause:\<close>
    mset_ccls

    find_undef_in_unwatched

    abs_trail hd_raw_abs_trail prop_queue raw_clauses abs_backtrack_lvl raw_conc_conflicting

    abs_learned_clss

    tl_abs_trail reduce_abs_trail_to

    cons_prop_queue last_prop_queue_to_trail prop_queue_null prop_queue_to_trail

    add_abs_confl_to_learned_cls abs_remove_cls

    update_abs_backtrack_lvl mark_conflicting resolve_abs_conflicting

    get_undecided_lit get_clause_watched_by update_clause

    abs_init_state restart_state +
  type_definition_locale
    abs_state_of rough_state_of wf_twl_state
  for
    \<comment> \<open>Clause:\<close>
    lit_lookup :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'v literal option" and
    lit_keys :: "'cls \<Rightarrow> 'lit multiset" and

    twl_cls :: "'cls \<Rightarrow> 'lit wf_twl_clause" and
    swap_lit :: "'cls \<Rightarrow> 'lit \<Rightarrow> 'lit \<Rightarrow> 'cls" and
    it_of_watched_ordered :: "'cls \<Rightarrow> 'v literal \<Rightarrow> 'lit list" and

    \<comment> \<open>Clauses\<close>
    cls_of_twl_list :: "'v literal list twl_clause \<Rightarrow> 'cls" and
    cls_lookup :: "'clss \<Rightarrow> 'cls_it \<Rightarrow> 'cls option" and
    cls_keys :: "'clss \<Rightarrow> 'cls_it multiset" and
    clss_update :: "'clss \<Rightarrow> 'cls_it \<Rightarrow> 'cls \<Rightarrow> 'clss" and
    add_cls :: "'clss \<Rightarrow> 'cls \<Rightarrow> 'clss \<times> 'cls_it" and

    \<comment> \<open>Conflicting clause:\<close>
    mset_ccls :: "'ccls \<Rightarrow> 'v clause" and

    find_undef_in_unwatched :: "'st \<Rightarrow> 'cls \<Rightarrow> 'lit option" and

    abs_trail :: "'st \<Rightarrow> ('v, 'v clause) ann_lits" and
    hd_raw_abs_trail :: "'st \<Rightarrow> ('v, 'cls_it) ann_lit" and
    prop_queue :: "'st \<Rightarrow> ('v, 'v clause) ann_lits" and
    raw_clauses :: "'st \<Rightarrow> 'clss" and
    abs_backtrack_lvl :: "'st \<Rightarrow> nat" and
    raw_conc_conflicting :: "'st \<Rightarrow> 'ccls option" and

    abs_learned_clss :: "'st \<Rightarrow> 'v clauses" and

    tl_abs_trail :: "'st \<Rightarrow> 'st" and
    reduce_abs_trail_to :: "('v, 'v clause) ann_lits \<Rightarrow> 'st \<Rightarrow> 'st" and

    cons_prop_queue :: "('v, 'cls_it) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    last_prop_queue_to_trail :: "'st \<Rightarrow> 'st" and
    prop_queue_null :: "'st \<Rightarrow> bool" and
    prop_queue_to_trail :: "'st \<Rightarrow> 'st" and

    add_abs_confl_to_learned_cls :: "'st \<Rightarrow> 'st" and
    abs_remove_cls :: "'cls \<Rightarrow> 'st \<Rightarrow> 'st" and

    update_abs_backtrack_lvl :: "nat \<Rightarrow> 'st \<Rightarrow> 'st" and

    mark_conflicting :: "'cls_it \<Rightarrow> 'st \<Rightarrow> 'st" and
    resolve_abs_conflicting :: "'v literal \<Rightarrow> 'cls \<Rightarrow> 'st \<Rightarrow> 'st" and

    get_undecided_lit :: "'st \<Rightarrow> 'v literal option" and
    get_clause_watched_by :: "'st \<Rightarrow> 'v literal \<Rightarrow> 'cls_it list" and
    update_clause :: "'st \<Rightarrow> 'cls_it \<Rightarrow> 'cls \<Rightarrow> 'st" and

    abs_init_state :: "'clss \<Rightarrow> 'st" and
    restart_state :: "'st \<Rightarrow> 'st" and

    abs_state_of :: "'st \<Rightarrow> 'inv" and
    rough_state_of :: "'inv \<Rightarrow> 'st"
begin

sublocale abs_conflict_driven_clause_learning\<^sub>W where
  get_lit = lit_lookup and
  mset_cls = clause_of_cls and
  get_cls = cls_lookup and
  mset_clss = raw_cls_of_clss and
  mset_ccls = mset_ccls and

  conc_trail = full_trail and
  hd_raw_conc_trail = hd_raw_abs_trail  and
  raw_clauses = raw_clauses and
  conc_backtrack_lvl = abs_backtrack_lvl and
  raw_conc_conflicting = raw_conc_conflicting and
  conc_learned_clss = abs_learned_clss and
  cons_conc_trail = cons_prop_queue and
  tl_conc_trail = "\<lambda>S. tl_abs_trail S" and
  add_conc_confl_to_learned_cls = "\<lambda>S. add_abs_confl_to_learned_cls S" and
  remove_cls = abs_remove_cls and
  update_conc_backtrack_lvl = update_abs_backtrack_lvl and
  mark_conflicting = "\<lambda>i S. mark_conflicting i S" and
  reduce_conc_trail_to = "\<lambda>M S. reduce_abs_trail_to M (prop_queue_to_trail S)" and
  resolve_conflicting = "\<lambda>L D S. resolve_abs_conflicting L D S" and
  conc_init_state = abs_init_state and
  restart_state = restart_state
  by unfold_locales

lemma XXX: "type_definition rough_state_of abs_state_of {S. wf_twl_state S}"
  unfolding type_definition_def
  using Rep by (auto intro: Abs_inverse simp: Rep_inv)

definition wf_resolve :: "'inv \<Rightarrow> 'inv \<Rightarrow> bool" where
"wf_resolve S T \<equiv> resolve_abs (rough_state_of S) (rough_state_of T)"

abbreviation mark_conflicting_and_flush where
"mark_conflicting_and_flush  i S \<equiv> mark_conflicting i (prop_queue_to_trail S)"

fun is_of_maximum_level :: "'v clause \<Rightarrow> ('v, 'b) ann_lit list \<Rightarrow> bool" where
"is_of_maximum_level C [] \<longleftrightarrow> True" |
"is_of_maximum_level C (Decided L' # M) \<longleftrightarrow> -L' \<notin># C" |
"is_of_maximum_level C (Propagated L' _ # M) \<longleftrightarrow> -L' \<notin># C \<and> is_of_maximum_level C M"

lemma is_of_maximum_level_decomposition:
  assumes "is_of_maximum_level C M"
  shows
    "\<exists> M' L' M''. ((M = M' @ Decided L' # M'' \<and> -L' \<notin># C) \<or> (M = M' \<and> M'' = [])) \<and>
     (\<forall>m \<in> set M'. \<not>is_decided m) \<and>
     uminus ` set_mset C \<inter> lits_of_l M' = {}"
  using assms
proof (induction M rule: ann_lit_list_induct)
  case Nil
  then show ?case by fastforce
next
  case (Decided L M)
  then have "Decided L # M = [] @ Decided L # M" and
    "\<forall>m \<in> set []. \<not>is_decided m" and
    "uminus ` set_mset C \<inter> lits_of_l [] = {}" and
    "-L \<notin># C"
    by auto
  then show ?case
    by metis
next
  case (Propagated L D M) note IH = this(1) and max = this(2)
  let ?L = "Propagated L D"
  let ?M = "?L # M"
  have LC: "-L \<notin># C" and "is_of_maximum_level C M"
    using max by auto
  then obtain M' L' M'' where
    M: "(M = M' @ Decided L' # M'' \<and> -L' \<notin># C) \<or> M = M' \<and> M'' = []" and
    nm: "\<forall>m\<in>set M'. \<not> is_decided m" and
    inter: "uminus ` set_mset C \<inter> lits_of_l M' = {}"
    using IH by auto
  then have  M: "(?M = (?L # M') @ Decided L' # M'' \<and> -L' \<notin># C) \<or> ?M = ?L # M' \<and> M'' = []" and
    nm: "\<forall>m\<in>set (?L # M'). \<not> is_decided m" and
    inter: "uminus ` set_mset C \<inter> lits_of_l (?L # M') = {}"
    using LC by auto
  then show ?case
    by blast
qed

lemma true_annots_CNot_uminus_incl_iff:
  "M \<Turnstile>as CNot C \<longleftrightarrow> uminus ` set_mset C \<subseteq> lits_of_l M"
  by (auto simp: true_annots_true_cls_def_iff_negation_in_model)

lemma get_maximum_level_skip_Decide_first:
  assumes "atm_of L \<notin> atms_of D" and "atms_of D \<subseteq> atm_of ` lits_of_l M"
  shows "get_maximum_level (Decided L # M) D = get_maximum_level M D"
  using assms unfolding get_maximum_level_def atms_of_def
    atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set
  by (smt ann_lit.sel(1) assms(1) atms_of_def get_level_skip_beginning image_iff multiset.map_cong0)

text \<open>The following lemma gives the relation between @{term is_of_maximum_level} and the inequality
  on the level. The clause @{term C} is expected to be instantiated by a clause like
  @{term "remove1_mset L (mset_ccls E)"}, where @{term E} is the conflicting clause. \<close>
lemma
  fixes M :: "('v, 'b) ann_lits" and L :: "'v literal" and D :: 'b
  defines LM[simp]: "LM \<equiv> Propagated L D # M"
  assumes
    n_d: "no_dup LM" and
    max: "is_of_maximum_level C M" and
    M_C: "LM \<Turnstile>as CNot C" and
    L_C: "-L \<notin># C"
  shows
    "get_maximum_level (Propagated L D # M) C < count_decided (Propagated L D # M) \<or> C = {#}"
proof -
  consider
    (no_decide) "\<forall>m\<in>set M. \<not> is_decided m" and
      "uminus ` set_mset C \<inter> lits_of_l M = {}" |
    (decide) M' L' M'' where "M = M' @ Decided L' # M''" and "\<forall>m\<in>set M'. \<not> is_decided m" and
      "-L' \<notin># C" and "uminus ` set_mset C \<inter> lits_of_l M' = {}"
    using is_of_maximum_level_decomposition[OF max] by auto
  then show ?thesis
    proof cases
      case no_decide note nm = this(1) and inter = this(2)
      have "C = {#}"
        using inter M_C L_C by (cases C) (auto simp: true_annots_true_cls true_clss_def)
      then show ?thesis by blast
    next
      case (decide M' L' M'') note M = this(1) and nm = this(2) and L' = this(3) and inter = this(4)
      have uL_M: "-L \<notin> lits_of_l (Propagated L D # M)"
        using n_d by (auto simp: lits_of_def uminus_lit_swap)
      then have atm_L_C: "atm_of L \<notin> atms_of C"
        using M_C unfolding LM by (metis L_C atm_of_in_atm_of_set_in_uminus atms_of_def
          true_annots_true_cls_def_iff_negation_in_model)
      have "atm_of xa \<in> atms_of C \<Longrightarrow> atm_of xa \<noteq> atm_of L" for xa :: "'v literal"
        using M_C uL_M L_C
        unfolding true_annots_true_cls_def_iff_negation_in_model lits_of_def atms_of_def
        by (fastforce simp: atm_of_eq_atm_of uminus_lit_swap)
      have "atms_of C \<inter> atm_of ` lits_of_l M' = {}"
        proof (rule ccontr)
          assume "\<not> ?thesis"
          then obtain a where
            a_C: "a \<in> atms_of C" and
            a_M': "a \<in> atm_of ` lits_of_l M'"
            by auto
          then obtain K where K_C: "K \<in># C" and a: "a = atm_of K"
            by (auto simp: atms_of_def)
          have "K \<noteq> -L"
            using L_C \<open>K \<in># C\<close> by blast
          then have "-K \<in> lits_of_l M"
            using a_C M_C \<open>K \<in># C\<close> unfolding a
            by (auto simp: uminus_lit_swap atm_of_eq_atm_of atms_of_def lits_of_def
              true_annots_true_cls_def_iff_negation_in_model)
          then have "-K \<in> lits_of_l M'"
            using n_d a_M' unfolding a by (fastforce simp: M atms_of_def lits_of_def
              uminus_lit_swap)
          moreover have "-K \<in> uminus ` set_mset C"
            using K_C by auto
          ultimately show False using inter by fast
        qed
      then have atms_C_M': "\<forall>x\<in>atms_of C. x \<notin> atm_of ` lits_of_l M'"
        by blast
      have False if "L' \<in># C"
        proof -
          have "-L' \<in> lits_of_l M"
            using that M_C L_C unfolding true_annots_true_cls_def_iff_negation_in_model by auto
          then show False
            using n_d unfolding LM by (metis M ann_lit.sel(1) consistent_interp_def image_iff
              distinct.simps(2)  distinct_consistent_interp in_set_conv_decomp list.simps(9)
              lits_of_def)
        qed
      then have atm_L'_C: "atm_of L' \<notin> atms_of C"
        using L' by (auto simp: atms_of_def atm_of_eq_atm_of)

      have atms_C_M'': "atms_of C \<subseteq> atm_of ` lits_of_l M''"
        proof
          fix a
          assume a_C: "a \<in> atms_of C"
          then obtain K where K_C: "K \<in># C" and a: "a = atm_of K"
            by (auto simp: atms_of_def)
          have "K \<noteq> -L"
            using L_C \<open>K \<in># C\<close> by blast
          then have "-K \<in> lits_of_l M"
            using a_C M_C \<open>K \<in># C\<close> unfolding a
            by (auto simp: uminus_lit_swap atm_of_eq_atm_of atms_of_def lits_of_def
              true_annots_true_cls_def_iff_negation_in_model)
          then have "atm_of (-K) \<in> atm_of ` lits_of_l M"
            by fast
          then have "atm_of K \<in> atm_of ` lits_of_l M"
            by simp
          then show "a \<in> atm_of ` lits_of_l M''"
            using atms_C_M'  a_C atm_L'_C  unfolding a M by auto
        qed
      have max_C: "get_maximum_level (Propagated L D # M' @ Decided L' # M'') C =
        get_maximum_level M'' C"
        apply (subst get_maximum_level_skip_first)
          using atm_L_C apply simp
        apply (subst get_maximum_level_skip_beginning)
          using atms_C_M' apply simp
        apply (subst get_maximum_level_skip_Decide_first)
          using atm_L'_C apply simp
         using atms_C_M'' apply simp
        by (rule refl)
      show ?thesis
        using count_decided_ge_get_maximum_level[of M'' "C"] by (auto simp: M nm max_C)
    qed
qed

definition wf_state :: "'st \<Rightarrow> 'inv" where
"wf_state S = abs_state_of (if cdcl\<^sub>W_mset.cdcl\<^sub>W_all_struct_inv (state S) then S else S)"

lemma [code abstype]:
  "wf_state (rough_state_of S) = S"
  by (simp add: Rep_inv wf_state_def)

fun backtrack_implementation where
"backtrack_implementation S =
  reduce_abs_trail_to (reduce_trail_to_lvl (abs_backtrack_lvl S) (full_trail S))"

function (domintros) skip_or_resolve where
"skip_or_resolve S =
  (if full_trail S = [] then S
  else
    case hd_raw_abs_trail S of
      Decided L \<Rightarrow> S
    | Propagated L C \<Rightarrow>
      if -L \<in># mset_ccls (the (raw_conc_conflicting S))
      then
        if is_of_maximum_level (mset_ccls (the (raw_conc_conflicting S))) (tl (full_trail S))
        then S
        else skip_or_resolve (tl_abs_trail (resolve_abs_conflicting L (raw_clauses S \<Down> C) S))
      else skip_or_resolve (tl_abs_trail S))"
  by auto

lemma
  assumes
    "cdcl\<^sub>W_mset.cdcl\<^sub>W_all_struct_inv (state S)" and
    "raw_conc_conflicting S \<noteq> None"
  shows "skip_or_resolve_dom S"
  using assms
proof (induction "full_trail S" arbitrary: S)
  case Nil
  then show ?case
    by (metis skip_or_resolve.domintros)
next
  case (Cons L M) note IH = this(1) and ft[symmetric] = this(2) and wf = this(3) and confl = this(4)
  let ?L = "hd_raw_abs_trail S"
  let ?l = "lit_of ?L"


  show ?case
    proof (cases ?L)
      case (Decided l)
      then show ?thesis
        by (metis ann_lit.distinct(1) skip_or_resolve.domintros)
    next
      case (Propagated l E) note hd [simp] = this(1)
      have ft: "full_trail S = mmset_of_mlit (raw_clauses S) (Propagated l E) # tl (full_trail S)"
        by (metis (no_types, lifting) ft hd hd_raw_conc_trail list.distinct(1) list.sel(1,3))
      show ?thesis
        proof (cases "-l \<in># mset_ccls (the (raw_conc_conflicting S))")
          case True
          let ?T = "tl_abs_trail (resolve_abs_conflicting l (raw_clauses S \<Down> E) S)"
          obtain C where
            C: "raw_conc_conflicting S = Some C"
            using confl by auto
          have l: "l \<in># clause_of_cls (raw_clauses S \<Down> E)"
            sorry
          have "resolve_abs S ?T"
            apply (rule resolve_abs_rule)
                 apply (subst ft, simp)
                apply simp
               using l apply simp
              using C apply force
             using True C apply simp
            sorry

  oops

text \<open>When we update a clause with respect to the literal L, there are several cases:
  \<^enum> the only literal is L: this is a conflict.
  \<^enum> if the other watched literal is true, there is noting to do.
  \<^enum> if it is false, then we have found a conflict (since every unwatched literal has to be false).
  \<^enum> otherwise, we have to check if we can find a literal to swap or propagate the variable.
\<close>
fun update_watched_clause :: "'st \<Rightarrow> 'v literal \<Rightarrow> 'cls_it \<Rightarrow> 'st"  where
"update_watched_clause S L i =
  (case it_of_watched_ordered (raw_clauses S \<Down> i) L of
    [_] \<Rightarrow> mark_conflicting i S
  | [j, k] \<Rightarrow>
    if ((raw_clauses S \<Down> i) \<down> k) \<in> lits_of_l (abs_trail S)
    then S
    else if -((raw_clauses S \<Down> i) \<down> k) \<in> lits_of_l (abs_trail S)
    then mark_conflicting i S
    else
      (case find_undef_in_unwatched S (raw_clauses S \<Down> i) of
        None \<Rightarrow> cons_prop_queue (Propagated L i) S
      | Some _ \<Rightarrow> update_clause S i (swap_lit (raw_clauses S \<Down> i) j k))
  )"

lemma
  fixes i :: 'cls_it and S :: 'st and L :: "'v literal"
  defines S': "S' \<equiv> update_watched_clause S L i"
  assumes
    "cdcl\<^sub>W_mset.cdcl\<^sub>W_all_struct_inv (state S)" and
    L: "L \<in># watched (twl_clause (raw_clauses S \<Down> i))" and
    confl: "raw_conc_conflicting S = None" and
    i: "i \<in>\<Down> raw_clauses S" and
    L_trail: "- L \<in> lits_of_l (full_trail S)"
  shows "propagate_abs S S' \<or> conflict_abs S S'"
proof -
  let ?C = "raw_clauses S \<Down> i"
  consider
    (single_watched) j :: 'lit where "it_of_watched_ordered (raw_clauses S \<Down> i) L = [j]" and
      "lit_lookup ?C j = Some L" and "unwatched (twl_clause (raw_clauses S \<Down> i)) = {#}" and
      "wf_watched (twl_cls (raw_clauses S \<Down> i)) = {#j#}" |
    (two_watched) j k :: 'lit where "it_of_watched_ordered (raw_clauses S \<Down> i) L = [j, k]" and
      "lit_lookup ?C j = Some L" and "lit_lookup ?C k \<noteq> None"
    using it_of_watched_ordered_cases[OF L] by blast
  then show ?thesis
    proof cases
      case (single_watched j) note it = this(1) and lit = this(2) and C = this(3) and W = this(4)
      moreover
        have iL: "clause_of_cls (raw_clauses S \<Down> i) = {#L#}"
          by (auto simp: clause_map_wf_twl_clause_wf_clause wf_clause_watched_unwatched C
            wf_unwatched.rep_eq W lit unwatched_twl_clause_twl_clause_of_wff_iff[symmetric])
        have "conflict_abs S (mark_conflicting i S)"
          apply (rule conflict_abs_rule[of _ i])
             using confl apply auto[]
            using i apply simp
           using L_trail iL apply simp
          by auto
      ultimately show ?thesis
        unfolding S' by auto
    next
      case (two_watched j k) note jk = this(1) and it_L = this(2) and k = this(3)
      then show ?thesis
         unfolding S' apply auto
oops

text \<open>Possible optimisation: @{term "Option.is_none (raw_conc_conflicting S')"} is the same as
  checking whether conflict has been marked by @{term update_watched_clause}.\<close>
fun update_watched_clauses  :: "'st \<Rightarrow> 'v literal \<Rightarrow> 'cls_it list \<Rightarrow> 'st" where
"update_watched_clauses S L (i # Cs) =
  (let S' = update_watched_clause S L i in
    if Option.is_none (raw_conc_conflicting S')
    then update_watched_clauses S' L Cs
    else S')" |
"update_watched_clauses S L [] = S"

definition propagate_and_conflict_one_lit where
"propagate_and_conflict_one_lit S L =
  update_watched_clauses S L (get_clause_watched_by S L)"


lemma raw_conc_conflicting_mark_conflicting:
  assumes "i \<in>\<Down> raw_clauses S" and "raw_conc_conflicting S = None"
  shows "raw_conc_conflicting (mark_conflicting i S) \<noteq> None"
  by (metis (no_types) \<open>i \<in>\<Down> raw_clauses S\<close> \<open>raw_conc_conflicting S = None\<close>
    conc_conflicting_mark_conflicting conflicting_None_iff_raw_conc_conflicting
    conflicting_conc_conflicting option.distinct(1))

lemma
  assumes "Option.is_none (raw_conc_conflicting S)" and "-L \<in> lits_of_l (full_trail S)"
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
  let ?C = "raw_clauses S \<Down> i"
  have "L \<in># watched (twl_clause ?C)"
    using get_clause_watched_by[of i S L] unfolding watched by simp
  then have [simp]: "it_of_watched_ordered ?C L \<noteq> []" and
    "lit_lookup (raw_clauses S \<Down> i) (hd (it_of_watched_ordered (raw_clauses S \<Down> i) L)) = Some L"
    using it_of_watched_ordered[of L ?C] by (auto simp: wf_watched_watched_empty_iff)

  have "L \<in># watched (twl_clause ?C)" and "i \<in>\<Down> raw_clauses S"
    using get_clause_watched_by[of i S L] unfolding watched by auto
  then have [simp]: "\<not>Option.is_none (raw_conc_conflicting (mark_conflicting i S))"
    using confl raw_conc_conflicting_mark_conflicting[of i S] by (auto simp: Option.is_none_def)
  show ?case
    unfolding watched
    apply (auto simp: )
oops


function propagate_and_conflict where
"propagate_and_conflict S =
  (if prop_queue_null S
  then S
  else
    let S' = prop_queue_to_trail S in
    propagate_and_conflict (propagate_and_conflict_one_lit S' (lit_of (hd_raw_abs_trail S'))))"
by auto
termination sorry
end


interpretation 2: type_definition_locale where Rep = twl_clause_of_wf and Abs = wf_of_twl_clause and
inv = struct_wf_twl_cls
apply unfold_locales
using twl_clause_of_wf_inverse apply metis
using twl_clause_of_wf apply metis
using twl_clause_of_wf_inject apply metis
using wf_of_twl_clause_inverse apply metis
using wf_of_twl_clause_induct apply metis
using twl_clause_of_wf_induct apply metis
using wf_of_twl_clause_cases  apply metis
using twl_clause_of_wf_cases  apply metis
using wf_of_twl_clause_inject apply metis
done


end