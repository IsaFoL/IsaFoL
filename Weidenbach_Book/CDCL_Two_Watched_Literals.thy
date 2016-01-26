(*  Title: CDCL with Two Watched Literals
    Author: Jasmin Blanchette <jasmin.blanchette@inria.fr>
    Author: Mathias Fleury <mathias.fleury@mpi-inf.mpg.de>
*)

theory CDCL_Two_Watched_Literals
imports CDCL_WNOT (* Have to decide which imports are the best *)
begin

text \<open>Only the 2-watched literals have to be verified here: the backtrack level and the trail can
  remain separate.\<close>

datatype 'v twl_clause =
  TWL_Clause (watched: "'v clause") (unwatched: "'v clause")

abbreviation raw_clause :: "'v twl_clause \<Rightarrow> 'v clause" where
  "raw_clause C \<equiv> watched C + unwatched C"

datatype ('v, 'lvl, 'mark) twl_state =
  TWL_State (trail: "('v, 'lvl, 'mark) marked_lits") (init_clss: "'v twl_clause multiset")
    (learned_clss: "'v twl_clause multiset") (backtrack_lvl: 'lvl)
    (conflicting: "'v clause conflicting_clause")

abbreviation raw_init_clss where
  "raw_init_clss S \<equiv> image_mset raw_clause (init_clss S)"

abbreviation raw_learned_clsss where
  "raw_learned_clsss S \<equiv> image_mset raw_clause (learned_clss S)"

abbreviation clauses where
  "clauses S \<equiv> init_clss S + learned_clss S"

definition
  candidates_propagate :: "('v, 'lvl, 'mark) twl_state \<Rightarrow> ('v literal \<times> 'v clause) set"
where
  "candidates_propagate S =
   {(L, raw_clause C) | L C.
    C \<in># clauses S \<and> watched C - mset_set (uminus ` lits_of (trail S)) = {#L#} \<and>
    undefined_lit L (trail S)}"

definition candidates_conflict :: "('v, 'lvl, 'mark) twl_state \<Rightarrow> 'v clause set" where
  "candidates_conflict S =
   {raw_clause C | C. C \<in># clauses S \<and> watched C \<subseteq># mset_set (uminus ` lits_of (trail S))}"

(* FIXME *)
(* interpretation dpll_state trail "image_mset raw_clause o clauses"
  "\<lambda>M S. TWL_State M (init_clss S) (learned_clss S) (backtrack_lvl S) (conflicting S)"
oops *)
primrec wf_twl_cls :: "('v, 'lvl, 'mark) marked_lit list \<Rightarrow> 'v twl_clause \<Rightarrow> bool" where
  "wf_twl_cls M (TWL_Clause W UW) \<longleftrightarrow>
   distinct_mset W \<and> size W \<le> 2 \<and> (size W < 2 \<longrightarrow> set_mset UW \<subseteq> set_mset W) \<and>
   (\<forall>L \<in># W. -L \<in> lits_of M \<longrightarrow> (\<forall>L' \<in># UW. L' \<notin># W \<longrightarrow> -L' \<in> lits_of M))"

primrec watched_decided_recently where
"watched_decided_recently S (TWL_Clause W UW) \<longleftrightarrow>
  (\<forall>L\<in>#W. \<forall>L'\<in>#UW.
    -L \<in> lits_of (trail S) \<longrightarrow> -L' \<in> lits_of (trail S) \<longrightarrow>
      Min {i. map lit_of (trail S)!i = -L} \<le> Min {i. map lit_of (trail S)!i = -L'})"

lemma size_mset_2: "size x1 = 2 \<longleftrightarrow> (\<exists>a b. x1 = {#a, b#})"
by (metis (no_types, hide_lams) Suc_eq_plus1 one_add_one size_1_singleton_mset
  size_Diff_singleton size_Suc_Diff1 size_eq_Suc_imp_eq_union size_single union_single_eq_diff
  union_single_eq_member)

lemma distinct_mset_size_2: "distinct_mset {#a, b#} \<longleftrightarrow> a \<noteq> b"
  unfolding distinct_mset_def by auto

text \<open>does not hold when all there are multiple conflicts in a clause.\<close>
lemma "wf_twl_cls M S \<Longrightarrow> wf_twl_cls (tl M) S"
apply (cases M; cases S)
apply (auto simp: size_mset_2 Ball_mset_def distinct_mset_size_2 split: split_if_asm)
apply (rename_tac LM M' W q LW LW')
oops

definition wf_twl_state :: "('v, 'lvl, 'mark) twl_state \<Rightarrow> bool" where
  "wf_twl_state S \<longleftrightarrow> (\<forall>C \<in># clauses S. wf_twl_cls (trail S) C)"

lemma wf_candidates_propagate_sound:
  assumes wf: "wf_twl_state S" and
    cand: "(L, C) \<in> candidates_propagate S"
  shows "trail S \<Turnstile>as CNot (mset_set (set_mset C - {L})) \<and> undefined_lit L (trail S)"
proof
  def M \<equiv> "trail S"
  def N \<equiv> "init_clss S"
  def U \<equiv> "learned_clss S"

  note MNU_defs [simp] = M_def N_def U_def

  obtain Cw where cw:
    "C = raw_clause Cw"
    "Cw \<in># N + U"
    "watched Cw - mset_set (uminus ` lits_of M) = {#L#}"
    "undefined_lit L M"
    using cand unfolding candidates_propagate_def MNU_defs by blast

  obtain W UW where cw_eq: "Cw = TWL_Clause W UW"
    by (case_tac Cw, blast)

  have l_w: "L \<in># W"
    by (metis Multiset.diff_le_self cw(3) cw_eq mset_leD multi_member_last twl_clause.sel(1))

  have wf_c: "wf_twl_cls M Cw"
    using wf \<open>Cw \<in># N + U\<close> unfolding wf_twl_state_def by simp

  have w_nw:
    "distinct_mset W"
    "size W < 2 \<Longrightarrow> set_mset UW \<subseteq> set_mset W"
    "\<And>L L'. L \<in># W \<Longrightarrow> -L \<in> lits_of M \<Longrightarrow> L' \<in># UW \<Longrightarrow> L' \<notin># W \<Longrightarrow> -L' \<in> lits_of M"
   using wf_c unfolding cw_eq by auto

  have "\<forall>L' \<in> set_mset C - {L}. -L' \<in> lits_of M"
  proof (cases "size W < 2")
    case True
    moreover have "size W \<noteq> 0"
      using cw(3) cw_eq by auto
    ultimately have "size W = 1"
      by linarith
    then have w: "W = {#L#}"
      by (metis (no_types, lifting) Multiset.diff_le_self cw(3) cw_eq single_not_empty
        size_1_singleton_mset subset_mset.add_diff_inverse union_is_single twl_clause.sel(1))
    from True have "set_mset UW \<subseteq> set_mset W"
      using w_nw(2) by blast
    then show ?thesis
      using w cw(1) cw_eq by auto
  next
    case sz2: False
    show ?thesis
    proof
      fix L'
      assume l': "L' \<in> set_mset C - {L}"
      have ex_la: "\<exists>La. La \<noteq> L \<and> La \<in># W"
      proof (cases W)
        case empty
        thus ?thesis
          using l_w by auto
      next
        case lb: (add W' Lb)
        show ?thesis
        proof (cases W')
          case empty
          thus ?thesis
            using lb sz2 by simp
        next
          case lc: (add W'' Lc)
          thus ?thesis
            by (metis add_gr_0 count_union distinct_mset_single_add lb union_single_eq_member
              w_nw(1))
        qed
      qed
      then obtain La where la: "La \<noteq> L" "La \<in># W"
        by blast
      then have "La \<in># mset_set (uminus ` lits_of M)"
        using cw(3)[unfolded cw_eq, simplified, folded M_def]
        by (metis count_diff count_single diff_zero not_gr0)
      then have nla: "-La \<in> lits_of M"
        by auto
      then show "-L' \<in> lits_of M"
      (* generated by Sledgehammer in two iterations *)
      proof -
        have f1: "L' \<in> set_mset C"
          using l' by blast
        have f2: "L' \<notin> {L}"
          using l' by fastforce
        have "\<And>l L. - (l::'a literal) \<in> L \<or> l \<notin> uminus ` L"
          by force
        then have "\<And>l. - l \<in> lits_of M \<or> count {#L#} l = count (C - UW) l"
          by (metis (no_types) add_diff_cancel_right' count_diff count_mset_set(3) cw(1) cw(3)
                cw_eq diff_zero twl_clause.sel(2))
        then show ?thesis
          by (smt comm_monoid_add_class.add_0 cw(1) cw_eq diff_union_cancelR ex_la f1 f2 insertCI
            less_numeral_extra(3) mem_set_mset_iff plus_multiset.rep_eq single.rep_eq
            twl_clause.sel(1) twl_clause.sel(2) w_nw(3))
      qed
    qed
  qed
  then show "trail S \<Turnstile>as CNot (mset_set (set_mset C - {L}))"
    unfolding true_annots_def by auto

  show "undefined_lit L (trail S)"
    using cw(4) M_def by blast
qed

lemma wf_candidates_propagate_complete:
  assumes wf: "wf_twl_state S" and
    c_mem: "C \<in># image_mset raw_clause (clauses S)" and
    l_mem: "L \<in># C" and
    unsat: "trail S \<Turnstile>as CNot (mset_set (set_mset C - {L}))" and
    undef: "undefined_lit L (trail S)"
  shows "(L, C) \<in> candidates_propagate S"
proof -
  def M \<equiv> "trail S"
  def N \<equiv> "init_clss S"
  def U \<equiv> "learned_clss S"

  note MNU_defs [simp] = M_def N_def U_def

  obtain Cw where cw: "C = raw_clause Cw" "Cw \<in># N + U"
    using c_mem by force

  obtain W UW where cw_eq: "Cw = TWL_Clause W UW"
    by (case_tac Cw, blast)

  have wf_c: "wf_twl_cls M Cw"
    using wf cw(2) unfolding wf_twl_state_def by simp

  have w_nw:
    "distinct_mset W"
    "size W < 2 \<Longrightarrow> set_mset UW \<subseteq> set_mset W"
    "\<And>L L'. L \<in># W \<Longrightarrow> -L \<in> lits_of M \<Longrightarrow> L' \<in># UW \<Longrightarrow> L' \<notin># W \<Longrightarrow> -L' \<in> lits_of M"
   using wf_c unfolding cw_eq by auto

  have unit_set: "set_mset (W - mset_set (uminus ` lits_of M)) = {L}"
  proof
    show "set_mset (W - mset_set (uminus ` lits_of M)) \<subseteq> {L}"
    proof
      fix L'
      assume l': "L' \<in> set_mset (W - mset_set (uminus ` lits_of M))"
      hence l'_mem_w: "L' \<in> set_mset W"
        by auto
      have "L' \<notin> uminus ` lits_of M"
        using distinct_mem_diff_mset[OF w_nw(1) l'] by simp
      then have "\<not> M \<Turnstile>a {#-L'#}"
        using image_iff by fastforce
      moreover have "L' \<in># C"
        using cw(1) cw_eq l'_mem_w by auto
      ultimately have "L' = L"
        unfolding M_def by (metis unsat[unfolded CNot_def true_annots_def, simplified])
      then show "L' \<in> {L}"
        by simp
    qed
  next
    show "{L} \<subseteq> set_mset (W - mset_set (uminus ` lits_of M))"
    proof clarify
      have "L \<in># W"
      proof (cases W)
        case empty
        thus ?thesis
          using w_nw(2) cw(1) cw_eq l_mem by auto
      next
        case (add W' La)
        thus ?thesis
        proof (cases "La = L")
          case True
          thus ?thesis
            using add by simp
        next
          case False
          have "-La \<in> lits_of M"
            using False add cw(1) cw_eq unsat[unfolded CNot_def true_annots_def, simplified]
            by fastforce
          then show ?thesis
            by (metis M_def Marked_Propagated_in_iff_in_lits_of add add.left_neutral count_union
              cw(1) cw_eq gr0I l_mem twl_clause.sel(1) twl_clause.sel(2) undef union_single_eq_member
              w_nw(3))
        qed
      qed
      moreover have "L \<notin># mset_set (uminus ` lits_of M)"
        using Marked_Propagated_in_iff_in_lits_of undef by auto
      ultimately show "L \<in> set_mset (W - mset_set (uminus ` lits_of M))"
        by auto
    qed
  qed
  have unit: "W - mset_set (uminus ` lits_of M) = {#L#}"
    by (metis distinct_mset_minus distinct_mset_set_mset_ident distinct_mset_singleton
      set_mset_single unit_set w_nw(1))

  show ?thesis
    unfolding candidates_propagate_def using unit undef cw cw_eq by fastforce
qed

lemma wf_candidates_conflict_sound:
  assumes wf: "wf_twl_state S" and
    cand: "C \<in> candidates_conflict S"
  shows "trail S \<Turnstile>as CNot C \<and> C \<in># image_mset raw_clause (clauses S)"
proof
  def M \<equiv> "trail S"
  def N \<equiv> "init_clss S"
  def U \<equiv> "learned_clss S"

  note MNU_defs [simp] = M_def N_def U_def

  obtain Cw where cw:
    "C = raw_clause Cw"
    "Cw \<in># N + U"
    "watched Cw \<subseteq># mset_set (uminus ` lits_of (trail S))"
    using cand[unfolded candidates_conflict_def, simplified] by auto

  obtain W UW where cw_eq: "Cw = TWL_Clause W UW"
    by (case_tac Cw, blast)

  have wf_c: "wf_twl_cls M Cw"
    using wf cw(2) unfolding wf_twl_state_def by simp

  have w_nw:
    "distinct_mset W"
    "size W < 2 \<Longrightarrow> set_mset UW \<subseteq> set_mset W"
    "\<And>L L'. L \<in># W \<Longrightarrow> -L \<in> lits_of M \<Longrightarrow> L' \<in># UW \<Longrightarrow> L' \<notin># W \<Longrightarrow> -L' \<in> lits_of M"
   using wf_c unfolding cw_eq by auto

  have "\<forall>L \<in># C. -L \<in> lits_of M"
  proof (cases "W = {#}")
    case True
    then have "C = {#}"
      using cw(1) cw_eq w_nw(2) by auto
    then show ?thesis
      by simp
  next
    case False
    then obtain La where la: "La \<in># W"
      using multiset_eq_iff by force
    show ?thesis
    proof
      fix L
      assume l: "L \<in># C"
      show "-L \<in> lits_of M"
      proof (cases "L \<in># W")
        case True
        thus ?thesis
          using cw(3) cw_eq by fastforce
      next
        case False
        thus ?thesis
          by (smt M_def l add_diff_cancel_left' count_diff cw(1) cw(3) la cw_eq
            diff_zero elem_mset_set finite_imageI finite_lits_of_def gr0I imageE mset_leD
            uminus_of_uminus_id twl_clause.sel(1) twl_clause.sel(2) w_nw(3))
      qed
    qed
  qed
  then show "trail S \<Turnstile>as CNot C"
    unfolding CNot_def true_annots_def by auto

  show "C \<in># image_mset raw_clause (clauses S)"
    using cw by auto
qed

lemma wf_candidates_conflict_complete:
  assumes wf: "wf_twl_state S" and
    c_mem: "C \<in># image_mset raw_clause (clauses S)" and
    unsat: "trail S \<Turnstile>as CNot C"
  shows "C \<in> candidates_conflict S"
proof -
  def M \<equiv> "trail S"
  def N \<equiv> "init_clss S"
  def U \<equiv> "learned_clss S"

  note MNU_defs [simp] = M_def N_def U_def

  obtain Cw where cw: "C = raw_clause Cw" "Cw \<in># N + U"
    using c_mem by force

  obtain W UW where cw_eq: "Cw = TWL_Clause W UW"
    by (case_tac Cw, blast)

  have wf_c: "wf_twl_cls M Cw"
    using wf cw(2) unfolding wf_twl_state_def by simp

  have w_nw:
    "distinct_mset W"
    "size W < 2 \<Longrightarrow> set_mset UW \<subseteq> set_mset W"
    "\<And>L L'. L \<in># W \<Longrightarrow> -L \<in> lits_of M \<Longrightarrow> L' \<in># UW \<Longrightarrow> L' \<notin># W \<Longrightarrow> -L' \<in> lits_of M"
   using wf_c unfolding cw_eq by auto

  have "\<And>L. L \<in># C \<Longrightarrow> -L \<in> lits_of M"
    unfolding M_def using unsat[unfolded CNot_def true_annots_def, simplified] by blast
  then have "set_mset C \<subseteq> uminus ` lits_of M"
    by (metis imageI mem_set_mset_iff subsetI uminus_of_uminus_id)
  then have "set_mset W \<subseteq> uminus ` lits_of M"
    using cw(1) cw_eq by auto
  then have subset: "W \<subseteq># mset_set (uminus ` lits_of M)"
    by (simp add: w_nw(1))

  have "W = watched Cw"
    using cw_eq twl_clause.sel(1) by simp
  then show ?thesis
    using MNU_defs cw(1) cw(2) subset candidates_conflict_def by blast
qed

typedef 'v wf_twl = "{S::('v, nat, 'v clause) twl_state. wf_twl_state S}"
morphisms rough_state_of_twl twl_of_rough_state
proof -
  have "TWL_State ([]::('v, nat, 'v clause) marked_lits)
    {#} {#} 0 C_True \<in> {S:: ('v, nat, 'v clause) twl_state. wf_twl_state S} "
    by (auto simp: wf_twl_state_def)
  then show ?thesis by auto
qed

lemma wf_twl_state_rough_state_of_twl[simp]: "wf_twl_state (rough_state_of_twl S)"
  using rough_state_of_twl by auto

abbreviation candidates_conflict_twl :: "'v wf_twl \<Rightarrow> 'v literal multiset set" where
"candidates_conflict_twl S \<equiv> candidates_conflict (rough_state_of_twl S)"

abbreviation candidates_propagate_twl :: "'v wf_twl \<Rightarrow> ('v literal \<times> 'v clause) set" where
"candidates_propagate_twl S \<equiv> candidates_propagate (rough_state_of_twl S)"

abbreviation trail_twl :: "'a wf_twl \<Rightarrow> ('a, nat, 'a literal multiset) marked_lit list" where
"trail_twl S \<equiv> trail (rough_state_of_twl S)"

abbreviation clauses_twl :: "'a wf_twl \<Rightarrow> 'a twl_clause multiset" where
"clauses_twl S \<equiv> clauses (rough_state_of_twl S)"

abbreviation init_clss_twl where
"init_clss_twl S \<equiv> image_mset raw_clause (init_clss (rough_state_of_twl S))"

abbreviation learned_clss_twl where
"learned_clss_twl S \<equiv> image_mset raw_clause (learned_clss (rough_state_of_twl S))"

abbreviation backtrack_lvl_twl where
"backtrack_lvl_twl S \<equiv> backtrack_lvl (rough_state_of_twl S)"

abbreviation conflicting_twl where
"conflicting_twl S \<equiv> conflicting (rough_state_of_twl S)"

locale abstract_twl =
  fixes
    watch :: "('v, nat, 'v clause) twl_state \<Rightarrow> 'v clause \<Rightarrow> 'v twl_clause" and
    rewatch :: "('v, nat, 'v literal multiset) marked_lit \<Rightarrow> ('v, nat, 'v clause) twl_state \<Rightarrow>
      'v twl_clause \<Rightarrow> 'v twl_clause" and
    linearize :: "'v clauses \<Rightarrow> 'v clause list" and
    restart_learned :: "('v, nat, 'v clause) twl_state \<Rightarrow> 'v twl_clause multiset"
  assumes
    clause_watch: "raw_clause (watch S C) = C" and
    wf_watch: "wf_twl_cls (trail S) (watch S C)" and
    clause_rewatch: "raw_clause (rewatch L S C') = raw_clause C'" and
    wf_rewatch: "wf_twl_cls (trail S) C' \<Longrightarrow> wf_twl_cls (L # trail S) (rewatch L S C')" and
    linearize: "mset (linearize N) = N" and
    restart_learned: "restart_learned S \<subseteq># learned_clss S"
begin

definition
  cons_trail :: "('v, nat, 'v clause) marked_lit \<Rightarrow> ('v, nat, 'v clause) twl_state \<Rightarrow>
    ('v, nat, 'v clause) twl_state"
where
  "cons_trail L S =
   TWL_State (L # trail S) (image_mset (rewatch L S) (init_clss S))
     (image_mset (rewatch L S) (learned_clss S)) (backtrack_lvl S) (conflicting S)"

lemma
  assumes "\<forall>C \<in># clauses S. watched_decided_recently S C" and
    "wf_twl_state S"
  shows "\<forall>C \<in># clauses (cons_trail L S). watched_decided_recently S C"
  using assms apply clarify
  apply (case_tac "C")
  apply (auto simp: cons_trail_def)
  (* needs no_dup in the trail... *)
oops

definition
  add_init_cls :: "'v clause \<Rightarrow> ('v, nat, 'v clause) twl_state \<Rightarrow>
    ('v, nat, 'v clause) twl_state"
where
  "add_init_cls C S =
   TWL_State (trail S) ({#watch S C#} + init_clss S) (learned_clss S) (backtrack_lvl S)
     (conflicting S)"

definition
  add_learned_cls :: "'v clause \<Rightarrow> ('v, nat, 'v clause) twl_state \<Rightarrow>
    ('v, nat, 'v clause) twl_state"
where
  "add_learned_cls C S =
   TWL_State (trail S) (init_clss S) ({#watch S C#} + learned_clss S) (backtrack_lvl S)
     (conflicting S)"

definition
  remove_cls :: "'v clause \<Rightarrow> ('v, nat, 'v clause) twl_state \<Rightarrow> ('v, nat, 'v clause) twl_state"
where
  "remove_cls C S =
   TWL_State (trail S) (filter_mset (\<lambda>D. raw_clause D \<noteq> C) (init_clss S))
     (filter_mset (\<lambda>D. raw_clause D \<noteq> C) (learned_clss S)) (backtrack_lvl S)
     (conflicting S)"

definition init_state :: "'v clauses \<Rightarrow> ('v, nat, 'v clause) twl_state" where
  "init_state N = fold add_init_cls (linearize N) (TWL_State [] {#} {#} 0 C_True)"

lemma unchanged_fold_add_init_cls:
  "trail (fold add_init_cls Cs (TWL_State M N U k C)) = M"
  "learned_clss (fold add_init_cls Cs (TWL_State M N U k C)) = U"
  "backtrack_lvl (fold add_init_cls Cs (TWL_State M N U k C)) = k"
  "conflicting (fold add_init_cls Cs (TWL_State M N U k C)) = C"
  by (induct Cs arbitrary: N) (auto simp: add_init_cls_def)

lemma unchanged_init_state[simp]:
  "trail (init_state N) = []"
  "learned_clss (init_state N) = {#}"
  "backtrack_lvl (init_state N) = 0"
  "conflicting (init_state N) = C_True"
  unfolding init_state_def by (rule unchanged_fold_add_init_cls)+

lemma clauses_init_fold_add_init:
  "image_mset raw_clause (init_clss (fold add_init_cls Cs (TWL_State M N U k C))) =
   mset Cs + image_mset raw_clause N"
  by (induct Cs arbitrary: N) (auto simp: add.assoc add_init_cls_def clause_watch)

lemma init_clss_init_state[simp]: "image_mset raw_clause (init_clss (init_state N)) = N"
  unfolding init_state_def by (simp add: clauses_init_fold_add_init linearize)

definition update_backtrack_lvl where
  "update_backtrack_lvl k S =
   TWL_State (trail S) (init_clss S) (learned_clss S) k (conflicting S)"

definition update_conflicting where
  "update_conflicting C S = TWL_State (trail S) (init_clss S) (learned_clss S) (backtrack_lvl S) C"

definition tl_trail where
  "tl_trail S =
   TWL_State (tl (trail S)) (init_clss S) (learned_clss S) (backtrack_lvl S) (conflicting S)"

definition restart' where
  "restart' S = TWL_State [] (init_clss S) (restart_learned S) 0 C_True"

sublocale cw_state trail raw_init_clss raw_learned_clsss backtrack_lvl conflicting
  cons_trail tl_trail add_init_cls add_learned_cls remove_cls update_backtrack_lvl
  update_conflicting init_state restart'
  apply unfold_locales
  apply (simp_all add: add_init_cls_def add_learned_cls_def clause_rewatch clause_watch
    cons_trail_def remove_cls_def restart'_def tl_trail_def update_backtrack_lvl_def
    update_conflicting_def)
  apply (rule image_mset_subseteq_mono[OF restart_learned])
  done

sublocale cdcl_cw_ops trail raw_init_clss raw_learned_clsss backtrack_lvl conflicting
  cons_trail tl_trail add_init_cls add_learned_cls remove_cls update_backtrack_lvl
  update_conflicting init_state restart'
  by unfold_locales

interpretation cdcl\<^sub>N\<^sub>O\<^sub>T: cdcl\<^sub>N\<^sub>O\<^sub>T_merge_bj_learn_ops "convert_trail_from_W o trail" clauses
  "\<lambda>L S. cons_trail (convert_marked_lit_from_NOT L) S"
  "\<lambda>S. tl_trail S"
  "\<lambda>C S. add_learned_cls C S"
  "\<lambda>C S. remove_cls C S"
  (* propagate conditions: *)"\<lambda>L S. lit_of L \<in> fst ` candidates_propagate S"
  "\<lambda>_ S. conflicting S = C_True"
  "\<lambda>C L S. C+{#L#} \<in> candidates_conflict S \<and> distinct_mset (C + {#L#}) \<and> \<not>tautology (C + {#L#})"
  by unfold_locales

end


text \<open>Lifting to the abstract state.\<close>
context abstract_twl
begin

declare state_simp[simp del]

abbreviation cons_trail_twl where
"cons_trail_twl L S \<equiv> twl_of_rough_state (cons_trail L (rough_state_of_twl S))"

lemma wf_twl_state_cons_trail: "wf_twl_state S \<Longrightarrow> wf_twl_state (cons_trail L S)"
  unfolding wf_twl_state_def by (auto simp: cons_trail_def wf_rewatch)

lemma rough_state_of_twl_cons_trail:
  "rough_state_of_twl (cons_trail_twl L S) = cons_trail L (rough_state_of_twl S)"
  using rough_state_of_twl twl_of_rough_state_inverse wf_twl_state_cons_trail by blast

abbreviation add_init_cls_twl where
"add_init_cls_twl C S \<equiv> twl_of_rough_state (add_init_cls C (rough_state_of_twl S))"

lemma wf_twl_add_init_cls: "wf_twl_state S \<Longrightarrow> wf_twl_state (add_init_cls L S)"
  unfolding wf_twl_state_def by (auto simp: wf_watch add_init_cls_def split: split_if_asm)

lemma rough_state_of_twl_add_init_cls:
  "rough_state_of_twl (add_init_cls_twl L S) = add_init_cls L (rough_state_of_twl S)"
  using rough_state_of_twl twl_of_rough_state_inverse wf_twl_add_init_cls by blast

abbreviation add_learned_cls_twl where
"add_learned_cls_twl C S \<equiv> twl_of_rough_state (add_learned_cls C (rough_state_of_twl S))"

lemma wf_twl_add_learned_cls: "wf_twl_state S \<Longrightarrow> wf_twl_state (add_learned_cls L S)"
  unfolding wf_twl_state_def by (auto simp: wf_watch add_learned_cls_def split: split_if_asm)

lemma rough_state_of_twl_add_learned_cls:
  "rough_state_of_twl (add_learned_cls_twl L S) = add_learned_cls L (rough_state_of_twl S)"
  using rough_state_of_twl twl_of_rough_state_inverse wf_twl_add_learned_cls by blast

abbreviation remove_cls_twl where
"remove_cls_twl C S \<equiv> twl_of_rough_state (remove_cls C (rough_state_of_twl S))"

lemma wf_twl_remove_cls: "wf_twl_state S \<Longrightarrow> wf_twl_state (remove_cls L S)"
  unfolding wf_twl_state_def by (auto simp: wf_watch remove_cls_def split: split_if_asm)

lemma rough_state_of_twl_remove_cls:
  "rough_state_of_twl (remove_cls_twl L S) = remove_cls L (rough_state_of_twl S)"
  using rough_state_of_twl twl_of_rough_state_inverse wf_twl_remove_cls by blast


abbreviation init_state_twl where
"init_state_twl N \<equiv> twl_of_rough_state (init_state N)"

lemma wf_twl_init_state: "wf_twl_state (init_state N)"
  unfolding wf_twl_state_def init_state_def
  sorry

lemma rough_state_of_twl_init_state:
  "rough_state_of_twl (init_state_twl N) = init_state N"
  by (simp add: twl_of_rough_state_inverse wf_twl_init_state)

abbreviation tl_trail_twl where
"tl_trail_twl S \<equiv> twl_of_rough_state (tl_trail (rough_state_of_twl S))"

lemma wf_twl_state_tl_trail: "wf_twl_state S \<Longrightarrow> wf_twl_state (tl_trail S)"
  sorry

lemma rough_state_of_twl_tl_trail:
  "rough_state_of_twl (tl_trail_twl S) = tl_trail (rough_state_of_twl S)"
  using rough_state_of_twl twl_of_rough_state_inverse wf_twl_state_tl_trail by blast

abbreviation update_backtrack_lvl_twl where
"update_backtrack_lvl_twl k S \<equiv> twl_of_rough_state (update_backtrack_lvl k (rough_state_of_twl S))"

lemma wf_twl_state_update_backtrack_lvl:
  "wf_twl_state S \<Longrightarrow> wf_twl_state (update_backtrack_lvl k S)"
  unfolding wf_twl_state_def by (auto simp: update_backtrack_lvl_def)

lemma rough_state_of_twl_update_backtrack_lvl:
  "rough_state_of_twl (update_backtrack_lvl_twl k S) = update_backtrack_lvl k
    (rough_state_of_twl S)"
  using rough_state_of_twl twl_of_rough_state_inverse wf_twl_state_update_backtrack_lvl by fast

abbreviation update_conflicting_twl where
"update_conflicting_twl k S \<equiv> twl_of_rough_state (update_conflicting k (rough_state_of_twl S))"

lemma wf_twl_state_update_conflicting:
  "wf_twl_state S \<Longrightarrow> wf_twl_state (update_conflicting k S)"
  unfolding wf_twl_state_def by (auto simp: update_conflicting_def)

lemma rough_state_of_twl_update_conflicting:
  "rough_state_of_twl (update_conflicting_twl k S) = update_conflicting k
    (rough_state_of_twl S)"
  using rough_state_of_twl twl_of_rough_state_inverse wf_twl_state_update_conflicting by fast

abbreviation raw_clauses_twl where
"raw_clauses_twl S \<equiv> clauses (rough_state_of_twl S)"

abbreviation restart_twl where
"restart_twl S \<equiv>  twl_of_rough_state (restart' (rough_state_of_twl S))"

lemma wf_wf_restart': "wf_twl_state S \<Longrightarrow> wf_twl_state (restart' S)"
  unfolding restart'_def wf_twl_state_def apply clarify
  apply (rename_tac x)
  apply (subgoal_tac "wf_twl_cls (trail S) x")
  apply (case_tac x)
  using restart_learned by fastforce+

lemma rough_state_of_twl_restart_twl:
  "rough_state_of_twl (restart_twl S) = restart' (rough_state_of_twl S)"
  by (simp add: twl_of_rough_state_inverse wf_wf_restart')
(* Sledgehammer is awesome! *)
interpretation cdcl\<^sub>N\<^sub>O\<^sub>T_twl_NOT: dpll_state
  "convert_trail_from_W o trail_twl" raw_clauses_twl
  "\<lambda>L S. cons_trail_twl (convert_marked_lit_from_NOT L) S"
  "\<lambda>S. tl_trail_twl S"
  "\<lambda>C S. add_learned_cls_twl C S"
  "\<lambda>C S. remove_cls_twl C S"
  apply unfold_locales
         apply (metis comp_apply rough_state_of_twl_cons_trail trail_prepend_trail)
        apply (metis comp_apply rough_state_of_twl_tl_trail tl_trail)
       apply (metis comp_def rough_state_of_twl_add_learned_cls trail_add_cls\<^sub>N\<^sub>O\<^sub>T)
      apply (metis comp_apply rough_state_of_twl_remove_cls trail_remove_cls)
     using clauses_prepend_trail rough_state_of_twl_cons_trail apply presburger
    apply (metis clauses_tl_trail rough_state_of_twl_tl_trail)
   using clauses_add_cls\<^sub>N\<^sub>O\<^sub>T rough_state_of_twl_add_learned_cls apply presburger
  using clauses_remove_cls\<^sub>N\<^sub>O\<^sub>T rough_state_of_twl_remove_cls by presburger

interpretation cdcl\<^sub>N\<^sub>O\<^sub>T_twl: cw_state
  trail_twl
  init_clss_twl
  learned_clss_twl
  backtrack_lvl_twl
  conflicting_twl
  cons_trail_twl
  tl_trail_twl
  add_init_cls_twl
  add_learned_cls_twl
  remove_cls_twl
  update_backtrack_lvl_twl
  update_conflicting_twl
  init_state_twl
  restart_twl
  apply unfold_locales
  by (simp_all add: rough_state_of_twl_cons_trail rough_state_of_twl_tl_trail
  rough_state_of_twl_add_init_cls rough_state_of_twl_add_learned_cls rough_state_of_twl_remove_cls
  rough_state_of_twl_update_backtrack_lvl rough_state_of_twl_update_conflicting
  rough_state_of_twl_init_state rough_state_of_twl_restart_twl learned_clss_restart_state)

interpretation cdcl\<^sub>N\<^sub>O\<^sub>T_twl: cdcl_cw_ops
  trail_twl
  init_clss_twl
  learned_clss_twl
  backtrack_lvl_twl
  conflicting_twl
  cons_trail_twl
  tl_trail_twl
  add_init_cls_twl
  add_learned_cls_twl
  remove_cls_twl
  update_backtrack_lvl_twl
  update_conflicting_twl
  init_state_twl
  restart_twl
  by unfold_locales

(* interpretation cdcl\<^sub>N\<^sub>O\<^sub>T: cdcl\<^sub>N\<^sub>O\<^sub>T_merge_bj_learn "convert_trail_from_W o trail" clauses
  "\<lambda>L S. cons_trail (convert_marked_lit_from_NOT L) S"
  "\<lambda>S. tl_trail S"
  "\<lambda>C S. add_learned_cls C S"
  "\<lambda>C S. remove_cls C S"
  (* propagate conditions: *)"\<lambda>L S. lit_of L \<in> fst ` candidates_propagate S"
  inv\<^sub>N\<^sub>O\<^sub>T
  (* forget conditions *)"\<lambda>_ S. conflicting S = C_True"
  "\<lambda>C L S. C+{#L#} \<in> candidates_conflict S"
oops *)

abbreviation state_eq_twl (infix "\<sim>TWL" 51) where
"state_eq_twl S S' \<equiv> state_eq (rough_state_of_twl S) (rough_state_of_twl S')"
notation cdcl\<^sub>N\<^sub>O\<^sub>T_twl.state_eq(infix "\<sim>" 51)
declare cdcl\<^sub>N\<^sub>O\<^sub>T_twl.state_simp[simp del]

definition propagate_twl where
"propagate_twl S S' \<longleftrightarrow>
  (\<exists>L C. (L, C) \<in> candidates_propagate_twl S
  \<and> S' \<sim>TWL cons_trail_twl (Propagated L C) S
  \<and> conflicting_twl S = C_True)"

lemma
  assumes inv: "cdcl_all_struct_inv (rough_state_of_twl S)"
  shows "cdcl\<^sub>N\<^sub>O\<^sub>T_twl.propagate S T \<longleftrightarrow> propagate_twl S T" (is "?P \<longleftrightarrow> ?T")
proof
  assume ?P
  then obtain C L where
    "conflicting (rough_state_of_twl S) = C_True" and
    CL_Clauses: "C + {#L#} \<in># cdcl\<^sub>N\<^sub>O\<^sub>T_twl.clauses S" and
    tr_CNot: "trail_twl S \<Turnstile>as CNot C" and
    undef_lot: "undefined_lit L (trail_twl S)" and
    "T \<sim> cons_trail_twl (Propagated L (C + {#L#})) S"
    unfolding cdcl\<^sub>N\<^sub>O\<^sub>T_twl.propagate.simps by auto
  have "distinct_mset (C + {#L#})"
    using inv CL_Clauses unfolding cdcl_all_struct_inv_def distinct_cdcl_state_def
    cdcl\<^sub>N\<^sub>O\<^sub>T_twl.clauses_def distinct_mset_set_def
    by (metis (no_types, lifting) add_gr_0  mem_set_mset_iff plus_multiset.rep_eq)
  then have C_L_L: "mset_set (set_mset (C + {#L#}) - {L}) = C"
    by (metis Un_insert_right add_diff_cancel_left' add_diff_cancel_right'
      distinct_mset_set_mset_ident finite_set_mset insert_absorb2 mset_set.insert_remove
      set_mset_single set_mset_union)
  have "(L, C+{#L#}) \<in> candidates_propagate_twl S"
    apply (rule wf_candidates_propagate_complete)
         using rough_state_of_twl apply auto[]
        using CL_Clauses cdcl\<^sub>N\<^sub>O\<^sub>T_twl.clauses_def apply auto[]
       apply simp
      using C_L_L tr_CNot apply simp
     using undef_lot apply blast
     done
  show ?T unfolding propagate_twl_def
    apply (rule exI[of _ "L"], rule exI[of _ "C+{#L#}"])
    apply (auto simp: \<open>(L, C+{#L#}) \<in> candidates_propagate_twl S\<close>
      \<open>conflicting (rough_state_of_twl S) = C_True\<close> )
    using \<open>T \<sim> cons_trail_twl (Propagated L (C + {#L#})) S\<close> cdcl\<^sub>N\<^sub>O\<^sub>T_twl.state_eq_backtrack_lvl
    cdcl\<^sub>N\<^sub>O\<^sub>T_twl.state_eq_conflicting cdcl\<^sub>N\<^sub>O\<^sub>T_twl.state_eq_init_clss
    cdcl\<^sub>N\<^sub>O\<^sub>T_twl.state_eq_learned_clss cdcl\<^sub>N\<^sub>O\<^sub>T_twl.state_eq_trail state_eq_def by blast
next
  assume ?T
  then obtain L C where
    LC: "(L, C) \<in> candidates_propagate_twl S" and
    T: "T \<sim>TWL cons_trail_twl (Propagated L C) S" and
    confl: "conflicting (rough_state_of_twl S) = C_True"
    unfolding propagate_twl_def by auto
  have [simp]: "C - {#L#} + {#L#} = C"
    using LC unfolding candidates_propagate_def
    by clarify (metis add.commute add_diff_cancel_right' count_diff insert_DiffM
      multi_member_last not_gr0 zero_diff)
  have "C \<in># raw_clauses_twl S"
    using LC unfolding candidates_propagate_def clauses_def by auto
  then have "distinct_mset C"
    using inv unfolding cdcl_all_struct_inv_def distinct_cdcl_state_def
    cdcl\<^sub>N\<^sub>O\<^sub>T_twl.clauses_def distinct_mset_set_def clauses_def by auto
  then have C_L_L: "mset_set (set_mset C - {L}) = C - {#L#}"
    by (metis \<open>C - {#L#} + {#L#} = C\<close> add_left_imp_eq diff_single_trivial
      distinct_mset_set_mset_ident finite_set_mset mem_set_mset_iff mset_set.remove
      multi_self_add_other_not_self union_commute)

  show ?P
    apply (rule cdcl\<^sub>N\<^sub>O\<^sub>T_twl.propagate.intros[of _ "trail_twl S" "init_clss_twl S"
      "learned_clss_twl S" "backtrack_lvl_twl S" "C-{#L#}" L])
        using confl apply auto[]
       using LC unfolding candidates_propagate_def apply (auto simp: cdcl\<^sub>N\<^sub>O\<^sub>T_twl.clauses_def)[]
      using wf_candidates_propagate_sound[OF _ LC] rough_state_of_twl apply (simp add: C_L_L)
     using wf_candidates_propagate_sound[OF _ LC] rough_state_of_twl apply simp
    using T unfolding cdcl\<^sub>N\<^sub>O\<^sub>T_twl.state_eq_def state_eq_def by auto
qed

definition conflict_twl where
"conflict_twl S S' \<longleftrightarrow>
  (\<exists>C. C \<in> candidates_conflict_twl S
  \<and> S' \<sim>TWL update_conflicting_twl (C_Clause C) S
  \<and> conflicting_twl S = C_True)"

lemma
  assumes inv: "cdcl_all_struct_inv (rough_state_of_twl S)"
  shows "cdcl\<^sub>N\<^sub>O\<^sub>T_twl.conflict S T \<longleftrightarrow> conflict_twl S T" (is "?C \<longleftrightarrow> ?T")
proof
  assume ?C
  then obtain M N U k C where
    S: "state (rough_state_of_twl S) = (M, N, U, k, C_True)" and
    C: "C \<in># cdcl\<^sub>N\<^sub>O\<^sub>T_twl.clauses S" and
    M_C: "M \<Turnstile>as CNot C" and
    T: "T \<sim> update_conflicting_twl (C_Clause C) S"
    by auto
  have "C \<in> candidates_conflict_twl S"
    apply (rule wf_candidates_conflict_complete)
       apply simp
      using C apply (auto simp: cdcl\<^sub>N\<^sub>O\<^sub>T_twl.clauses_def)[]
    using M_C S by auto
  moreover have "T \<sim>TWL twl_of_rough_state (update_conflicting (C_Clause C) (rough_state_of_twl S))"
    using T unfolding state_eq_def cdcl\<^sub>N\<^sub>O\<^sub>T_twl.state_eq_def by auto
  ultimately show ?T
    using S unfolding conflict_twl_def by auto
next
  assume ?T
  then obtain C where
    C: "C \<in> candidates_conflict_twl S" and
    T: "T \<sim>TWL update_conflicting_twl (C_Clause C) S" and
    confl: "conflicting_twl S = C_True"
    unfolding conflict_twl_def by auto
  have "C \<in># cdcl\<^sub>N\<^sub>O\<^sub>T_twl.clauses S"
    using C unfolding candidates_conflict_def cdcl\<^sub>N\<^sub>O\<^sub>T_twl.clauses_def by auto
 moreover have "trail_twl S \<Turnstile>as CNot C"
    using wf_candidates_conflict_sound[OF _ C] by auto
 ultimately show ?C apply -
   apply (rule cdcl\<^sub>N\<^sub>O\<^sub>T_twl.conflict.conflict_rule[of _ _ _ _ _ C])
   using confl T unfolding state_eq_def cdcl\<^sub>N\<^sub>O\<^sub>T_twl.state_eq_def by auto
qed

end

definition pull :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "pull p xs = filter p xs @ filter (Not \<circ> p) xs"

lemma set_pull[simp]: "set (pull p xs) = set xs"
  unfolding pull_def by auto

lemma mset_pull[simp]: "mset (pull p xs) = mset xs"
  by (simp add: pull_def mset_filter_compl)

definition watch_nat :: "(nat, nat, nat clause) twl_state \<Rightarrow> nat clause \<Rightarrow> nat twl_clause" where
  "watch_nat S C =
   (let
      W = take 2 (pull (\<lambda>L. - L \<notin> lits_of (trail S)) (sorted_list_of_set (set_mset C)));
      UW = sorted_list_of_multiset (C - mset W)
    in TWL_Clause (mset W) (mset UW))"

definition
  rewatch_nat ::
  "(nat, nat, nat literal multiset) marked_lit \<Rightarrow> (nat, nat, nat clause) twl_state \<Rightarrow> nat twl_clause \<Rightarrow> nat twl_clause"
where
  "rewatch_nat L S C =
   (if - lit_of L \<in># watched C then
      case filter (\<lambda>L'. L' \<notin># watched C \<and> - L' \<notin> lits_of (L # trail S))
          (sorted_list_of_multiset (unwatched C)) of
        [] \<Rightarrow> C
      | L' # _ \<Rightarrow>
        TWL_Clause (watched C - {#- lit_of L#} + {#L'#}) (unwatched C - {#L'#} + {#- lit_of L#})
    else
      C)"

lemma mset_set_set_mset_subseteq[simp]: "mset_set (set_mset A) \<subseteq># A"
  by (metis count_mset_set(1) count_mset_set(3) finite_set_mset le_less_linear less_one
    mem_set_mset_iff mset_less_eqI not_gr0)

lemma mset_sorted_list_of_set[simp]:
  "mset (sorted_list_of_set A) = mset_set A"
  by (metis mset_sorted_list_of_multiset sorted_list_of_mset_set)

lemma mset_take_subseteq: "mset (take n xs) \<subseteq># mset xs"
  apply (induct xs arbitrary: n)
   apply simp
  by (case_tac n) simp_all

lemma mset_take_pull_sorted_list_of_set_subseteq:
  "mset (take n (pull p (sorted_list_of_set (set_mset A)))) \<subseteq># A"
  by (metis mset_pull mset_set_set_mset_subseteq mset_sorted_list_of_set mset_take_subseteq
    subset_mset.dual_order.trans)

lemma clause_watch_nat: "raw_clause (watch_nat S C) = C"
  by (simp add: watch_nat_def Let_def)
    (rule subset_mset.add_diff_inverse[OF mset_take_pull_sorted_list_of_set_subseteq])

lemma distinct_pull[simp]: "distinct (pull p xs) = distinct xs"
  unfolding pull_def by (induct xs) auto

lemma falsified_watiched_imp_unwatched_falsified:
  assumes
    watched: "L \<in> set (take n (pull (Not \<circ> fls) (sorted_list_of_set (set_mset C))))" and
    falsified: "fls L" and
    not_watched: "L' \<notin> set (take n (pull (Not \<circ> fls) (sorted_list_of_set (set_mset C))))" and
    unwatched: "L' \<in># C - mset (take n (pull (Not \<circ> fls) (sorted_list_of_set (set_mset C))))"
  shows "fls L'"
proof -
  let ?Ls = "sorted_list_of_set (set_mset C)"
  let ?W = "take n (pull (Not \<circ> fls) ?Ls)"

  have "n > length (filter (Not \<circ> fls) ?Ls)"
    using watched falsified
    unfolding pull_def comp_def
    apply auto
     using in_set_takeD apply fastforce
    by (metis gr0I length_greater_0_conv length_pos_if_in_set take_0 zero_less_diff)
  then have "\<And>L. L \<in> set ?Ls \<Longrightarrow> \<not> fls L \<Longrightarrow> L \<in> set ?W"
    unfolding pull_def by auto
  then show ?thesis
    by (metis Multiset.diff_le_self finite_set_mset mem_set_mset_iff mset_leD not_watched
      sorted_list_of_set unwatched)
qed

lemma wf_watch_nat: "wf_twl_cls (trail S) (watch_nat S C)"
  apply (simp only: watch_nat_def Let_def partition_filter_conv case_prod_beta fst_conv snd_conv)
  unfolding wf_twl_cls.simps
  apply (intro conjI)
     apply clarsimp+
  using falsified_watiched_imp_unwatched_falsified[unfolded comp_def]
  by (metis count_diff zero_less_diff)

lemma filter_sorted_list_of_multiset_eqD:
  assumes "[x \<leftarrow> sorted_list_of_multiset A. p x] = x # xs" (is "?comp = _")
  shows "x \<in># A"
proof -
  have "x \<in> set ?comp"
    using assms by simp
  then have "x \<in> set (sorted_list_of_multiset A)"
    by simp
  then show "x \<in># A"
    by simp
qed

lemma clause_rewatch_nat: "raw_clause (rewatch_nat L S C) = raw_clause C"
  apply (auto simp: rewatch_nat_def Let_def split: list.split)
  apply (subst subset_mset.add_diff_assoc2, simp)
  apply (subst subset_mset.add_diff_assoc2, simp)
  apply (subst subset_mset.add_diff_assoc2)
   apply (auto dest: filter_sorted_list_of_multiset_eqD)
  by (metis (no_types, lifting) add.assoc add_diff_cancel_right' filter_sorted_list_of_multiset_eqD
    insert_DiffM mset_leD mset_le_add_left)

lemma filter_sorted_list_of_multiset_Nil:
  "[x \<leftarrow> sorted_list_of_multiset M. p x] = [] \<longleftrightarrow> (\<forall>x \<in># M. \<not> p x)"
  by auto (metis empty_iff filter_set list.set(1) mem_set_mset_iff member_filter
    set_sorted_list_of_multiset)

lemma filter_sorted_list_of_multiset_ConsD:
  "[x \<leftarrow> sorted_list_of_multiset M. p x] = x # xs \<Longrightarrow> p x"
  by (metis filter_set insert_iff list.set(2) member_filter)


lemma mset_minus_single_eq_mempty:
  "a - {#b#} = {#} \<longleftrightarrow> a = {#b#} \<or> a = {#}"
  by (metis Multiset.diff_cancel add.right_neutral diff_single_eq_union
    diff_single_trivial zero_diff)

lemma wf_rewatch_nat':
  assumes wf: "wf_twl_cls (trail S) C"
  shows "wf_twl_cls (L # trail S) (rewatch_nat L S C)"
using filter_sorted_list_of_multiset_Nil[simp]
proof (cases "- lit_of L \<in># watched C")
  case falsified: True

  let ?unwatched_nonfalsified =
    "[L' \<leftarrow> sorted_list_of_multiset (unwatched C). L' \<notin># watched C \<and> - L' \<notin> lits_of (L # trail S)]"

  show ?thesis
  proof (cases ?unwatched_nonfalsified)
    case Nil
    show ?thesis
      unfolding rewatch_nat_def
      using falsified Nil apply auto
        apply (case_tac C)
        apply auto
        using local.wf wf_twl_cls.simps apply blast
        using local.wf wf_twl_cls.simps apply blast
        by (metis contra_subsetD local.wf mem_set_mset_iff wf_twl_cls.simps)
  next
    case (Cons L' Ls)
    show ?thesis
      using wf
      unfolding rewatch_nat_def
      using falsified Cons apply (auto dest!: filter_sorted_list_of_multiset_ConsD)
      apply (case_tac C)
      apply (auto simp: distinct_mset_single_add)
      apply (case_tac C)
apply (auto split: split_if_asm simp: mset_minus_single_eq_mempty)
apply (simp add: size_Diff_singleton)
apply (metis not_less_eq_eq numeral_2_eq_2 size_Suc_Diff1)

      sorry
  qed
next
  case False
  have "wf_twl_cls (L # trail S) C"
    using wf
    apply (case_tac C)
    apply auto
     apply (metis False twl_clause.sel(1) uminus_of_uminus_id)
    by (metis False twl_clause.sel(1) uminus_of_uminus_id)
  then show ?thesis
    unfolding rewatch_nat_def using False by simp
qed


(*TODO: remove when multiset is of sort linord again*)
instantiation multiset :: (linorder) linorder
begin

definition less_multiset :: "'a :: linorder multiset \<Rightarrow> 'a multiset \<Rightarrow> bool" where
  "M' < M \<longleftrightarrow> M' #<# M"

definition less_eq_multiset :: "'a multiset \<Rightarrow> 'a multiset \<Rightarrow> bool" where
  "M' \<le> M \<longleftrightarrow> M' #<=# M"

instance
  by standard (auto simp: less_eq_multiset_def less_multiset_def)

end

(* implementation of watch etc. *)
interpretation abstract_twl watch_nat rewatch_nat sorted_list_of_multiset learned_clss
  apply unfold_locales
  apply (rule clause_watch_nat)
  apply (rule wf_watch_nat)
  apply (rule clause_rewatch_nat)
  apply (rule wf_rewatch_nat', simp)
  apply (rule mset_sorted_list_of_multiset)
  apply (rule subset_mset.order_refl)
  oops

(* interpretation cdcl_cw_ops
oops
 *)

end
