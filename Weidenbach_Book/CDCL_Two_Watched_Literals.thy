(*  Title: CDCL with Two Watched Literals
    Author: Jasmin Blanchette <jasmin.blanchette@inria.fr>
    Author: Mathias Fleury <mathias.fleury@mpi-inf.mpg.de>
*)

theory CDCL_Two_Watched_Literals
imports CDCL_WNOT (* Have to decide which imports are the best *)
begin

text \<open>Only the 2-watched literals have to be verified here: the backtrack level and the trail that
  appear in the state are not related to the 2-watched algoritm.\<close>

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

abbreviation raw_learned_clss where
  "raw_learned_clss S \<equiv> image_mset raw_clause (learned_clss S)"

abbreviation clauses where
  "clauses S \<equiv> init_clss S + learned_clss S"

abbreviation raw_clauses where
  "raw_clauses S \<equiv> image_mset raw_clause (clauses S)"

definition
  candidates_propagate :: "('v, 'lvl, 'mark) twl_state \<Rightarrow> ('v literal \<times> 'v clause) set"
where
  "candidates_propagate S =
   {(L, raw_clause C) | L C.
    C \<in># clauses S \<and> watched C - mset_set (uminus ` lits_of (trail S)) = {#L#} \<and>
    undefined_lit (trail S) L}"

definition candidates_conflict :: "('v, 'lvl, 'mark) twl_state \<Rightarrow> 'v clause set" where
  "candidates_conflict S =
   {raw_clause C | C. C \<in># clauses S \<and> watched C \<subseteq># mset_set (uminus ` lits_of (trail S))}"

primrec (nonexhaustive) index :: "'a list \<Rightarrow>'a \<Rightarrow> nat" where
"index (a # l) c = (if a = c then 0 else 1+index l c)"

lemma index_nth:
  "a \<in> set l \<Longrightarrow> l ! (index l a) = a"
  by (induction l) auto

text \<open>We need the following property about updates: if there is a literal @{term L} with
  @{term "-L"} in the trail, and @{term L} is not  watched, then it stays unwatched; i.e., while
  updating with @{term rewatch} it does not get swap with a watched literal @{term L'} such that
  @{term "-L'"} is in the trail.\<close>
primrec watched_decided_most_recently :: "('v, 'lvl, 'mark) marked_lit list \<Rightarrow> 'v twl_clause \<Rightarrow> bool"
  where
"watched_decided_most_recently M (TWL_Clause W UW) \<longleftrightarrow>
  (\<forall>L'\<in>#W. \<forall>L\<in>#UW.
    -L' \<in> lits_of M \<longrightarrow> -L \<in> lits_of M \<longrightarrow> L \<notin># W \<longrightarrow>
      index (map lit_of M) (-L') \<le> index (map lit_of M) (-L))"

text \<open>Here are the invariant strictly related to the 2-WL data structure.\<close>
primrec wf_twl_cls :: "('v, 'lvl, 'mark) marked_lit list \<Rightarrow> 'v twl_clause \<Rightarrow> bool" where
  "wf_twl_cls M (TWL_Clause W UW) \<longleftrightarrow>
   distinct_mset W \<and> size W \<le> 2 \<and> (size W < 2 \<longrightarrow> set_mset UW \<subseteq> set_mset W) \<and>
   (\<forall>L \<in># W. -L \<in> lits_of M \<longrightarrow> (\<forall>L' \<in># UW. L' \<notin># W \<longrightarrow> -L' \<in> lits_of M)) \<and>
   watched_decided_most_recently M (TWL_Clause W UW)"

lemma "-L \<in> lits_of M \<Longrightarrow>  {i. map lit_of M!i = -L} \<noteq> {}"
  unfolding set_map_lit_of_lits_of[symmetric] set_conv_nth
  by (smt Collect_empty_eq mem_Collect_eq)

lemma size_mset_2: "size x1 = 2 \<longleftrightarrow> (\<exists>a b. x1 = {#a, b#})"
  by (metis (no_types, hide_lams) Suc_eq_plus1 one_add_one size_1_singleton_mset
  size_Diff_singleton size_Suc_Diff1 size_eq_Suc_imp_eq_union size_single union_single_eq_diff
  union_single_eq_member)

lemma distinct_mset_size_2: "distinct_mset {#a, b#} \<longleftrightarrow> a \<noteq> b"
  unfolding distinct_mset_def by auto

lemma wf_twl_cls_wf_twl_cls_tl:
  assumes wf: "wf_twl_cls M C" and n_d: "no_dup M"
  shows "wf_twl_cls (tl M) C"
proof (cases M)
  case Nil
  then show ?thesis using wf
    by (cases C) (simp add: wf_twl_cls.simps[of "tl _"])
next
  case (Cons l M') note M = this(1)
  obtain W UW where C: "C = TWL_Clause W UW"
    by (cases C)
  { fix L L'
    assume
      LW: "L \<in># W" and
      LM: "- L \<in> lits_of M'" and
      L'UW: "L' \<in># UW" and
      "count W L' = 0"
    then have
      L'M: "- L' \<in> lits_of M"
      using wf by (auto simp: C M)
    have "watched_decided_most_recently M C"
      using wf by (auto simp: C)
    then have
      "index (map lit_of M) (-L) \<le> index (map lit_of M) (-L')"
      using LM L'M L'UW LW \<open>count W L' = 0\<close>
      by (metis (no_types, lifting) C M bspec_mset insert_iff less_not_refl2 lits_of_cons
        watched_decided_most_recently.simps)
    then have "- L' \<in> lits_of M'"
      using \<open>count W L' = 0\<close> LW L'M by (auto simp: C M split: split_if_asm)
  }
  moreover
    {
      fix L' L
      assume
        "L' \<in># W" and
        "L \<in># UW" and
        L'M: "- L' \<in> lits_of M'" and
        "- L \<in> lits_of M'" and
        "L \<notin># W"
      moreover
        have "lit_of l \<noteq> - L'"
        using n_d unfolding M
          by (metis (no_types) L'M M Marked_Propagated_in_iff_in_lits_of defined_lit_map
            distinct.simps(2) list.simps(9) set_map)
      moreover have "watched_decided_most_recently M C"
        using wf by (auto simp: C)
      ultimately have "index (map lit_of M') (- L') \<le> index (map lit_of M') (- L)"
        by (fastforce simp: M C split: split_if_asm)
    }
  moreover have "distinct_mset W" and "size W \<le> 2" and "(size W < 2 \<longrightarrow> set_mset UW \<subseteq> set_mset W)"
    using wf by (auto simp: C M)
  ultimately show ?thesis by (auto simp add: M C)
qed

definition wf_twl_state :: "('v, 'lvl, 'mark) twl_state \<Rightarrow> bool" where
  "wf_twl_state S \<longleftrightarrow> (\<forall>C \<in># clauses S. wf_twl_cls (trail S) C) \<and> no_dup (trail S)"

lemma wf_candidates_propagate_sound:
  assumes wf: "wf_twl_state S" and
    cand: "(L, C) \<in> candidates_propagate S"
  shows "trail S \<Turnstile>as CNot (mset_set (set_mset C - {L})) \<and> undefined_lit (trail S) L"
proof
  def M \<equiv> "trail S"
  def N \<equiv> "init_clss S"
  def U \<equiv> "learned_clss S"

  note MNU_defs [simp] = M_def N_def U_def

  obtain Cw where cw:
    "C = raw_clause Cw"
    "Cw \<in># N + U"
    "watched Cw - mset_set (uminus ` lits_of M) = {#L#}"
    "undefined_lit M L"
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

  show "undefined_lit (trail S) L"
    using cw(4) M_def by blast
qed

lemma wf_candidates_propagate_complete:
  assumes wf: "wf_twl_state S" and
    c_mem: "C \<in># raw_clauses S" and
    l_mem: "L \<in># C" and
    unsat: "trail S \<Turnstile>as CNot (mset_set (set_mset C - {L}))" and
    undef: "undefined_lit (trail S) L"
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
    c_mem: "C \<in># raw_clauses S" and
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

abbreviation clauses_twl :: "'a wf_twl \<Rightarrow> 'a literal multiset multiset" where
"clauses_twl S \<equiv> raw_clauses (rough_state_of_twl S)"

abbreviation init_clss_twl :: "'a wf_twl \<Rightarrow> 'a literal multiset multiset" where
"init_clss_twl S \<equiv> raw_init_clss (rough_state_of_twl S)"

abbreviation learned_clss_twl :: "'a wf_twl \<Rightarrow> 'a literal multiset multiset" where
"learned_clss_twl S \<equiv> raw_learned_clss (rough_state_of_twl S)"

abbreviation backtrack_lvl_twl where
"backtrack_lvl_twl S \<equiv> backtrack_lvl (rough_state_of_twl S)"

abbreviation conflicting_twl where
"conflicting_twl S \<equiv> conflicting (rough_state_of_twl S)"

lemma wf_candidates_twl_conflict_complete:
  assumes
    c_mem: "C \<in># clauses_twl S" and
    unsat: "trail_twl S \<Turnstile>as CNot C"
  shows "C \<in> candidates_conflict_twl S"
  using c_mem unsat wf_candidates_conflict_complete wf_twl_state_rough_state_of_twl by blast

locale abstract_twl =
  fixes
    watch :: "('v, nat, 'v clause) twl_state \<Rightarrow> 'v clause \<Rightarrow> 'v twl_clause" and
    rewatch :: "('v, nat, 'v literal multiset) marked_lit \<Rightarrow> ('v, nat, 'v clause) twl_state \<Rightarrow>
      'v twl_clause \<Rightarrow> 'v twl_clause" and
    linearize :: "'v clauses \<Rightarrow> 'v clause list" and
    restart_learned :: "('v, nat, 'v clause) twl_state \<Rightarrow> 'v twl_clause multiset"
  assumes
    clause_watch: "no_dup(trail S) \<Longrightarrow> raw_clause (watch S C) = C" and
    wf_watch: "no_dup (trail S) \<Longrightarrow> wf_twl_cls (trail S) (watch S C)" and
    clause_rewatch: "raw_clause (rewatch L S C') = raw_clause C'" and
    wf_rewatch:
      "no_dup (trail S) \<Longrightarrow> undefined_lit (trail S) (lit_of L) \<Longrightarrow> wf_twl_cls (trail S) C' \<Longrightarrow>
        wf_twl_cls (L # trail S) (rewatch L S C')"
      and
    linearize: "mset (linearize N) = N" and
    restart_learned: "restart_learned S \<subseteq># learned_clss S"
begin

lemma linearize_mempty[simp]: "linearize {#} = []"
  using linearize mset_zero_iff by blast

definition
  cons_trail :: "('v, nat, 'v clause) marked_lit \<Rightarrow> ('v, nat, 'v clause) twl_state \<Rightarrow>
    ('v, nat, 'v clause) twl_state"
where
  "cons_trail L S =
   TWL_State (L # trail S) (image_mset (rewatch L S) (init_clss S))
     (image_mset (rewatch L S) (learned_clss S)) (backtrack_lvl S) (conflicting S)"

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
  "no_dup M \<Longrightarrow>
  image_mset raw_clause (init_clss (fold add_init_cls Cs (TWL_State M N U k C))) =
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
end

definition pull :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "pull p xs = filter p xs @ filter (Not \<circ> p) xs"

lemma set_pull[simp]: "set (pull p xs) = set xs"
  unfolding pull_def by auto

lemma mset_pull[simp]: "mset (pull p xs) = mset xs"
  by (simp add: pull_def mset_filter_compl)

lemma mset_take_pull_sorted_list_of_set_subseteq:
  "mset (take n (pull p (sorted_list_of_set (set_mset A)))) \<subseteq># A"
  by (metis mset_pull mset_set_set_mset_subseteq mset_sorted_list_of_set mset_take_subseteq
    subset_mset.dual_order.trans)

definition watch_nat :: "(nat, nat, nat clause) twl_state \<Rightarrow> nat clause \<Rightarrow> nat twl_clause" where
  "watch_nat S C =
   (let
      C' = remdups (sorted_list_of_set (set_mset C));
      negation_not_assigned = filter (\<lambda>L. -L \<notin> lits_of (trail S)) C';
      negation_assigned_sorted_by_trail = filter (\<lambda>L. L \<in># C) (map (\<lambda>L. -lit_of L) (trail S));
      W = take 2 (negation_not_assigned @ negation_assigned_sorted_by_trail);
      UW = sorted_list_of_multiset (C - mset W)
    in TWL_Clause (mset W) (mset UW))"

  thm rev_cases
lemma list_cases2:
  fixes l :: "'a list"
  assumes
    "l = [] \<Longrightarrow> P" and
    "\<And>x. l = [x] \<Longrightarrow> P" and
    "\<And>x y xs. l = x # y # xs \<Longrightarrow> P"
  shows "P"
  by (metis assms list.collapse)

lemma filter_in_list_prop_verifiedD:
  assumes "[L\<leftarrow>P . Q L] = l"
  shows "\<forall>x \<in> set l. x \<in> set P \<and> Q x"
  using assms by auto

lemma no_dup_filter_diff:
  assumes n_d: "no_dup M" and H: "[L\<leftarrow>map (\<lambda>L. - lit_of L) M. L \<in># C] = l"
  shows "distinct l"
  unfolding H[symmetric]
  apply (rule distinct_filter)
  using n_d by (induction M) auto

lemma watch_nat_lists_disjointD:
  assumes
    l: "[L\<leftarrow>remdups (sorted_list_of_set (set_mset C)) . - L \<notin> lits_of (trail S)] = l" and
    l': "[L\<leftarrow>map (\<lambda>L. - lit_of L) (trail S) . L \<in># C] = l'"
  shows "\<forall>x \<in> set l. \<forall>y \<in> set l'. x \<noteq> y"
  by (auto simp: l[symmetric] l'[symmetric] lits_of_def)

lemma watch_nat_list_cases:
  fixes C :: "'v::linorder literal multiset" and S :: "('v, 'a, 'b) twl_state"
  defines
    "xs \<equiv> [L\<leftarrow>remdups (sorted_list_of_set (set_mset C)) . - L \<notin> lits_of (trail S)]" and
    "ys \<equiv> [L\<leftarrow>map (\<lambda>L. - lit_of L) (trail S) . L \<in># C]"
  assumes n_d: "no_dup (trail S)" and
    nil_nil: "xs = [] \<Longrightarrow> ys = [] \<Longrightarrow> P" and
    nil_single:
      "\<And>a. xs = [] \<Longrightarrow> ys = [a] \<Longrightarrow>  a \<in># C \<Longrightarrow> P" and
    nil_other: "\<And>a b ys'. xs = [] \<Longrightarrow> ys = a # b # ys' \<Longrightarrow> a \<noteq> b \<Longrightarrow> P" and
    single_nil: "\<And>a. xs = [a] \<Longrightarrow> ys = [] \<Longrightarrow> P" and
    single_other: "\<And>a b ys'. xs = [a] \<Longrightarrow> ys = b # ys' \<Longrightarrow> a \<noteq> b \<Longrightarrow> P" and
    other: "\<And>a b xs'. xs = a # b # xs' \<Longrightarrow> a \<noteq> b \<Longrightarrow> P"
  shows P
proof -
  note xs_def[simp] and ys_def[simp]
  have dist: "distinct [L\<leftarrow>remdups (sorted_list_of_set (set_mset C)) . - L \<notin> lits_of (trail S)]"
    by auto
  then have H: "\<And>a xs. [L\<leftarrow>remdups (sorted_list_of_set (set_mset C)) . - L \<notin> lits_of (trail S)]
    \<noteq> a # a # xs"
    by force
  show ?thesis
  apply (cases "[L\<leftarrow>remdups (sorted_list_of_set (set_mset C)). - L \<notin> lits_of (trail S)]"
        rule: list_cases2;
      cases "[L\<leftarrow>map (\<lambda>L. - lit_of L) (trail S) . L \<in># C]" rule: list_cases2)
          using nil_nil apply simp
         using nil_single apply (force dest: filter_in_list_prop_verifiedD)
        using nil_other
        apply (auto dest: filter_in_list_prop_verifiedD watch_nat_lists_disjointD
          no_dup_filter_diff[OF n_d] simp: H)[]
       using single_nil apply simp
      using single_other
      apply (auto dest: filter_in_list_prop_verifiedD watch_nat_lists_disjointD
        no_dup_filter_diff[OF n_d] simp: H)[]
     using single_other apply (auto dest: filter_in_list_prop_verifiedD watch_nat_lists_disjointD
       no_dup_filter_diff[OF n_d] simp: H)[]
    using other xs_def ys_def by (metis H)+
qed

lemma watch_nat_lists_set_union:
  fixes C :: "'v::linorder literal multiset" and S :: "('v, 'a, 'b) twl_state"
  defines
    "xs \<equiv> [L\<leftarrow>remdups (sorted_list_of_set (set_mset C)) . - L \<notin> lits_of (trail S)]" and
    "ys \<equiv> [L\<leftarrow>map (\<lambda>L. - lit_of L) (trail S) . L \<in># C]"
  assumes n_d: "no_dup (trail S)"
  shows "set_mset C = set xs \<union> set ys"
  using n_d unfolding xs_def ys_def by (auto simp: lits_of_def uminus_lit_swap)

definition
  rewatch_nat ::
  "(nat, nat, nat literal multiset) marked_lit \<Rightarrow> (nat, nat, nat clause) twl_state \<Rightarrow>
    nat twl_clause \<Rightarrow> nat twl_clause"
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

lemma mset_intersection_inclusion: "A + (B - A) = B \<longleftrightarrow> A \<subseteq># B"
  apply (rule iffI)
   apply (metis mset_le_add_left)
  by (auto simp: ac_simps multiset_eq_iff subseteq_mset_def)

lemma clause_watch_nat:
  assumes "no_dup (trail S)"
  shows "raw_clause (watch_nat S C) = C"
  using assms
  apply (cases rule: watch_nat_list_cases[OF assms(1), of C])
  by (auto dest: filter_in_list_prop_verifiedD simp: watch_nat_def Let_def
    mset_intersection_inclusion subseteq_mset_def)

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

lemma set_mset_is_single_in_mset_is_single:
  "set_mset C = {a} \<Longrightarrow> x \<in># C \<Longrightarrow> x = a"
  by fastforce

lemma index_uminus_index_map_uminus:
  "-a \<in> set L \<Longrightarrow> index L (-a) = index (map uminus L) (a::'a literal)"
  by (induction L) auto

lemma index_filter:
  "a \<in> set L \<Longrightarrow> b \<in> set L \<Longrightarrow> P a \<Longrightarrow> P b \<Longrightarrow>
   index L a \<le> index L b \<longleftrightarrow> index (filter P L) a \<le> index (filter P L) b"
  by (induction L) auto

lemma wf_watch_nat: "no_dup (trail S) \<Longrightarrow> wf_twl_cls (trail S) (watch_nat S C)"
  apply (simp only: watch_nat_def Let_def partition_filter_conv case_prod_beta fst_conv snd_conv)
  unfolding wf_twl_cls.simps
  apply (intro conjI)
proof goal_cases
  case 1
  then show ?case
    by (cases rule: watch_nat_list_cases[of S C]) (auto dest: filter_in_list_prop_verifiedD
      simp: distinct_mset_add_single)
next
  case 2
  then show ?case by simp
next
  case 3
  then show ?case
    apply (cases rule: watch_nat_list_cases[of S C])
          apply  (auto dest: filter_in_list_prop_verifiedD simp: distinct_mset_add_single mset_intersection_inclusion
            subseteq_mset_def)[7]
       apply(auto dest!: arg_cong[of _ "[]" set])[]
       apply (cases C; auto split: split_if_asm simp: lits_of_def image_image)
       apply (metis image_eqI image_image uminus_of_uminus_id)
      using watch_nat_lists_set_union[of S C]
      apply (auto split: split_if_asm dest!: arg_cong[of _ "[_]" set] arg_cong[of _ "[]" set]
        dest: set_mset_is_single_in_mset_is_single simp: lits_of_def)[2]
    done
next
  case 4 note _[simp] = this
  moreover
  {
    fix a :: "nat literal" and ys' :: "nat literal list" and L :: "nat literal" and
      L' :: "nat literal"
    assume a1: "[L\<leftarrow>remdups (insort L (sorted_list_of_set (insert a (set ys') - {L}))).
      - L \<notin> lits_of (trail S)] = [a]"
    assume a2: "set_mset C = insert L (insert a (set ys'))"
    assume a3: "L' \<in># C"
    assume a4: "a \<noteq> L'"
    have "set (L # a # ys') = set_mset C"
      using a2 by auto
    then have "L' \<notin> set [l\<leftarrow>remdups (sorted_list_of_set (set_mset C)) . - l \<notin> lits_of (trail S)]"
      using a4 a1 by (metis List.finite_set list.set(1) list.set(2) singleton_iff
        sorted_list_of_set.insert_remove)
    then have "- L' \<in> lits_of (trail S)"
      using a3 by simp
      } note H =this
  show ?case
    apply (cases rule: watch_nat_list_cases[of S C])
    apply simp
      using watch_nat_lists_set_union[of S C]
     apply (auto dest: filter_in_list_prop_verifiedD H simp: lits_of_def filter_empty_conv
       dest!: arg_cong[of _ "[_]" set] arg_cong[of _ "[]" set]
        dest: set_mset_is_single_in_mset_is_single)[4]
    using watch_nat_lists_set_union[of S C] by (auto dest: filter_in_list_prop_verifiedD H)
next
  case 5
  then show ?case
    apply (cases rule: watch_nat_list_cases[of S C])
           using watch_nat_lists_set_union[of S C] apply (auto
             dest: filter_in_list_prop_verifiedD set_mset_is_single_in_mset_is_single
             simp: lits_of_def
             dest!: arg_cong[of _ "[_]" set] arg_cong[of _ "[]" set])[3]
unfolding watched_decided_most_recently.simps Ball_mset_def
apply (clarify)
apply (subst index_uminus_index_map_uminus)
  apply (simp add: index_uminus_index_map_uminus lits_of_def o_def)[1]

apply (subst index_uminus_index_map_uminus)
  apply (simp add: index_uminus_index_map_uminus lits_of_def o_def)[1]

apply (subst index_filter[of _ _ _ "\<lambda>L. L \<in># C"])
apply (auto dest: filter_in_list_prop_verifiedD
simp: uminus_lit_swap index_uminus_index_map_uminus lits_of_def o_def)[5]

apply (auto simp add:  lits_of_def o_def )[]
apply (subst index_filter[of _ _ _ "\<lambda>L. L \<in># C"])
apply (auto dest: filter_in_list_prop_verifiedD)[1]
apply (metis (no_types) imageI image_image image_set uminus_of_uminus_id)
apply (auto dest: filter_in_list_prop_verifiedD)[1]
apply (auto dest: filter_in_list_prop_verifiedD)[1]
apply (auto dest: filter_in_list_prop_verifiedD)[1]


apply (clarify)
apply clarsimp
apply (elim disjE)

apply (subst index_uminus_index_map_uminus)
  apply (simp add: index_uminus_index_map_uminus lits_of_def o_def)[1]

apply (subst index_uminus_index_map_uminus)
  apply (simp add: index_uminus_index_map_uminus lits_of_def o_def)[1]

apply (subst index_filter[of _ _ _ "\<lambda>L. L \<in># C"])
apply (auto dest: filter_in_list_prop_verifiedD
  simp: index_uminus_index_map_uminus lits_of_def o_def uminus_lit_swap)[5]


apply (subst index_uminus_index_map_uminus)
  apply (simp add: index_uminus_index_map_uminus lits_of_def o_def)[1]

apply (subst index_uminus_index_map_uminus)
  apply (simp add: index_uminus_index_map_uminus lits_of_def o_def)[1]

apply (subst index_filter[of _ _ _ "\<lambda>L. L \<in># C"])
apply (auto dest: filter_in_list_prop_verifiedD simp: index_filter[of _ _ _ "\<lambda>L. L \<in># C"])[5]

apply (auto dest: filter_in_list_prop_verifiedD)[1]
done
qed

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

lemma size_mset_le_2_cases:
  assumes "size W \<le> 2"
  shows "W = {#} \<or> (\<exists>a. W = {#a#}) \<or> (\<exists>a b. W = {#a,b#})"
  by (metis One_nat_def Suc_1 Suc_eq_plus1_left assms linorder_not_less nat_less_le
    not_less_eq_eq ordered_cancel_comm_monoid_diff_class.le_iff_add size_1_singleton_mset
    size_eq_0_iff_empty size_mset_2)

lemma wf_rewatch_nat':
  assumes
    wf: "wf_twl_cls (trail S) C" and
    n_d: "no_dup (trail S)" and
    undef: "undefined_lit (trail S) (lit_of L)"
  shows "wf_twl_cls (L # trail S) (rewatch_nat L S C)"
  using filter_sorted_list_of_multiset_Nil[simp]
proof (cases "- lit_of L \<in># watched C")
  case falsified: True

  let ?unwatched_nonfalsified =
    "[L'\<leftarrow>sorted_list_of_multiset (unwatched C) . L' \<notin># watched C \<and> - L' \<notin> lits_of (L # trail S)]"
  obtain W UW where C: "C = TWL_Clause W UW"
    by (cases C)

  show ?thesis
  proof (cases ?unwatched_nonfalsified)
    case Nil
    show ?thesis
      unfolding rewatch_nat_def
      using falsified Nil
      apply (simp only: wf_twl_cls.simps if_True list.cases C)
      apply (intro conjI)
      proof goal_cases
        case 1
        then show ?case using wf C by simp
      next
        case 2
        then show ?case using wf C by simp
      next
        case 3
        then show ?case using wf C by simp
      next
        case 4
        then show ?case using wf C by auto
      next
        case 5
        then show ?case
          using  C apply simp
          using wf by (smt ball_msetI bspec_mset not_gr0 uminus_of_uminus_id
            watched_decided_most_recently.simps wf_twl_cls.simps)
      qed
  next
    case (Cons L' Ls)
    show ?thesis
      unfolding rewatch_nat_def C
      using falsified Cons
      apply (simp only: wf_twl_cls.simps if_True list.cases C)
      apply (intro conjI)
      proof goal_cases
        case 1
        then show ?case using wf C n_d
          by (smt Multiset.diff_le_self distinct_mset_add_single distinct_mset_single_add
            filter_sorted_list_of_multiset_ConsD insert_DiffM mset_leD twl_clause.sel(1)
            wf_twl_cls.simps)
      next
        case 2
        then show ?case using wf C by (metis insert_DiffM2 size_single size_union twl_clause.sel(1)
          wf_twl_cls.simps)
      next
        case 3
        then show ?case
          using wf C by (force simp: mset_minus_single_eq_mempty dest: subset_singletonD)
      next
        case 4
        have H: "\<forall>L\<in>#W. - L \<in> lits_of (trail S) \<longrightarrow>
          (\<forall>L'\<in>#UW. count W L' = 0 \<longrightarrow> - L' \<in> lits_of (trail S))"
          using wf by (auto simp: C)
        have W: "size W \<le> 2" and W_UW: "size W < 2 \<longrightarrow> set_mset UW \<subseteq> set_mset W"
          using wf by (auto simp: C)

        have distinct: "distinct_mset W"
          using wf by (auto simp: C)
        show ?case
          using 4
          unfolding C watched_decided_most_recently.simps Ball_mset_def twl_clause.sel
          apply (intro allI impI)
          apply (rename_tac xW xUW)
          apply (case_tac "- lit_of L = xW"; case_tac "xW = xUW"; case_tac "L' = xW")
                  apply (auto simp: uminus_lit_swap)[2]
                using filter_sorted_list_of_multiset_ConsD apply blast
               using H size_mset_le_2_cases[OF W]
              using distinct apply (fastforce split: split_if_asm simp: distinct_mset_size_2)
             using distinct apply (fastforce split: split_if_asm simp: distinct_mset_size_2)
            using distinct apply (fastforce split: split_if_asm simp: distinct_mset_size_2)
           using filter_sorted_list_of_multiset_ConsD apply blast
          using size_mset_le_2_cases[OF W] H by (fastforce simp: uminus_lit_swap
            dest: filter_sorted_list_of_multiset_ConsD filter_sorted_list_of_multiset_eqD)
          (* SLOW ~4s *)
      next
        case 5
        have H: "\<forall>x. x \<in># W \<longrightarrow> - x \<in> lits_of (trail S) \<longrightarrow> (\<forall>x. x \<in># UW \<longrightarrow> count W x = 0
          \<longrightarrow> - x \<in> lits_of (trail S))"
          using wf by (auto simp: C)

        show ?case
          using 5 unfolding C watched_decided_most_recently.simps Ball_mset_def
          apply (intro allI impI conjI)
          apply (rename_tac xW x)
          apply (case_tac "- lit_of L = xW"; case_tac "xW = x")
              apply (auto simp: uminus_lit_swap)[3]
          apply (case_tac "- lit_of L = x")
           apply (clarsimp)
           using H apply (blast dest: filter_sorted_list_of_multiset_ConsD
             filter_sorted_list_of_multiset_eqD)
          apply (clarsimp)
          using H apply (blast dest: filter_sorted_list_of_multiset_ConsD
             filter_sorted_list_of_multiset_eqD)
          done
      qed
  qed
next
  case False
  then have "wf_twl_cls (L # trail S) C"
    apply (cases C)
    using wf n_d undef apply (clarify)
    unfolding wf_twl_cls.simps
    apply (intro conjI)
         apply blast
        apply blast
       apply blast
      apply (smt ball_mset_cong bspec_mset insert_iff lits_of_cons nat_neq_iff twl_clause.sel(1)
        uminus_of_uminus_id)
     apply (auto simp: Marked_Propagated_in_iff_in_lits_of)
    done
  then show ?thesis
    unfolding rewatch_nat_def using False by simp
qed

(* implementation of watch etc. *)
interpretation twl: abstract_twl watch_nat rewatch_nat sorted_list_of_multiset learned_clss
  apply unfold_locales
  apply (rule clause_watch_nat; simp)
  apply (rule wf_watch_nat; simp)
  apply (rule clause_rewatch_nat)
  apply (rule wf_rewatch_nat'; simp)
  apply (rule mset_sorted_list_of_multiset)
  apply (rule subset_mset.order_refl)
  done

text \<open>Lifting to the abstract state.\<close>
context abstract_twl
begin

interpretation state\<^sub>W trail raw_init_clss raw_learned_clss backtrack_lvl conflicting
  cons_trail tl_trail add_init_cls add_learned_cls remove_cls update_backtrack_lvl
  update_conflicting init_state restart'
  apply unfold_locales
  apply (simp_all add: add_init_cls_def add_learned_cls_def clause_rewatch clause_watch
    cons_trail_def remove_cls_def restart'_def tl_trail_def update_backtrack_lvl_def
    update_conflicting_def)
  apply (rule image_mset_subseteq_mono[OF restart_learned])
  done

interpretation cdcl\<^sub>W_ops trail raw_init_clss raw_learned_clss backtrack_lvl conflicting
  cons_trail tl_trail add_init_cls add_learned_cls remove_cls update_backtrack_lvl
  update_conflicting init_state restart'
  by unfold_locales

interpretation cdcl\<^sub>N\<^sub>O\<^sub>T: cdcl\<^sub>N\<^sub>O\<^sub>T_merge_bj_learn_ops
  "\<lambda>S. convert_trail_from_W (trail S)"
  clauses
  "\<lambda>L S. cons_trail (convert_marked_lit_from_NOT L) S"
  "\<lambda>S. tl_trail S"
  "\<lambda>C S. add_learned_cls C S"
  "\<lambda>C S. remove_cls C S"
  (* propagate conditions: *)"\<lambda>L S. lit_of L \<in> fst ` candidates_propagate S"
  "\<lambda>_ S. conflicting S = C_True"
  "\<lambda>C C' L' S. C \<in> candidates_conflict S \<and> distinct_mset (C' + {#L'#}) \<and> \<not>tautology (C' + {#L'#})"
  by unfold_locales

interpretation cdcl\<^sub>N\<^sub>O\<^sub>T: cdcl\<^sub>N\<^sub>O\<^sub>T_merge_bj_learn_proxy
  "\<lambda>S. convert_trail_from_W (trail S)"
  clauses
  "\<lambda>L S. cons_trail (convert_marked_lit_from_NOT L) S"
  "\<lambda>S. tl_trail S"
  "\<lambda>C S. add_learned_cls C S"
  "\<lambda>C S. remove_cls C S"
  (* propagate conditions: *)"\<lambda>L S. lit_of L \<in> fst ` candidates_propagate S"
  "\<lambda>_ S. conflicting S = C_True"
  "\<lambda>C C' L' S. C \<in> candidates_conflict S"
  apply unfold_locales
  oops

declare state_simp[simp del]

abbreviation cons_trail_twl where
"cons_trail_twl L S \<equiv> twl_of_rough_state (cons_trail L (rough_state_of_twl S))"

lemma wf_twl_state_cons_trail:
  "undefined_lit (trail S) (lit_of L) \<Longrightarrow> wf_twl_state S \<Longrightarrow> wf_twl_state (cons_trail L S)"
  unfolding wf_twl_state_def by (auto simp: cons_trail_def wf_rewatch defined_lit_map)

lemma rough_state_of_twl_cons_trail:
  "undefined_lit (trail_twl S) (lit_of L) \<Longrightarrow>
    rough_state_of_twl (cons_trail_twl L S) = cons_trail L (rough_state_of_twl S)"
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

lemma wf_twl_state_wf_twl_state_fold_add_init_cls:
  assumes "wf_twl_state S"
  shows "wf_twl_state (fold add_init_cls N S)"
  using assms apply (induction N arbitrary: S)
   apply (auto simp: wf_twl_state_def)[]
  by (simp add: wf_twl_add_init_cls)

lemma wf_twl_state_epsilon_state[simp]:
  "wf_twl_state (TWL_State [] {#} {#} 0 C_True)"
  by (auto simp: wf_twl_state_def)

lemma wf_twl_init_state: "wf_twl_state (init_state N)"
  unfolding init_state_def by (auto intro!: wf_twl_state_wf_twl_state_fold_add_init_cls)

lemma rough_state_of_twl_init_state:
  "rough_state_of_twl (init_state_twl N) = init_state N"
  by (simp add: twl_of_rough_state_inverse wf_twl_init_state)

abbreviation tl_trail_twl where
"tl_trail_twl S \<equiv> twl_of_rough_state (tl_trail (rough_state_of_twl S))"

lemma wf_twl_state_tl_trail: "wf_twl_state S \<Longrightarrow> wf_twl_state (tl_trail S)"
  by (simp add: twl_of_rough_state_inverse wf_twl_init_state wf_twl_cls_wf_twl_cls_tl
    tl_trail_def wf_twl_state_def distinct_tl map_tl)

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
"restart_twl S \<equiv> twl_of_rough_state (restart' (rough_state_of_twl S))"

lemma wf_wf_restart': "wf_twl_state S \<Longrightarrow> wf_twl_state (restart' S)"
  unfolding restart'_def wf_twl_state_def apply standard
   apply clarify
   apply (rename_tac x)
   apply (subgoal_tac "wf_twl_cls (trail S) x")
    apply (case_tac x)
  using restart_learned by fastforce+

lemma rough_state_of_twl_restart_twl:
  "rough_state_of_twl (restart_twl S) = restart' (rough_state_of_twl S)"
  by (simp add: twl_of_rough_state_inverse wf_wf_restart')

(* Sledgehammer is awesome! *)
interpretation cdcl\<^sub>W_twl_NOT: dpll_state
  "\<lambda>S. convert_trail_from_W (trail_twl S)"
  raw_clauses_twl
  "\<lambda>L S. cons_trail_twl (convert_marked_lit_from_NOT L) S"
  "\<lambda>S. tl_trail_twl S"
  "\<lambda>C S. add_learned_cls_twl C S"
  "\<lambda>C S. remove_cls_twl C S"
  apply unfold_locales
         apply (simp add: rough_state_of_twl_cons_trail)
        apply (metis rough_state_of_twl_tl_trail tl_trail)
       apply (metis rough_state_of_twl_add_learned_cls trail_add_cls\<^sub>N\<^sub>O\<^sub>T)
      apply (metis rough_state_of_twl_remove_cls trail_remove_cls)
     apply (simp add: rough_state_of_twl_cons_trail)
    apply (metis clauses_tl_trail rough_state_of_twl_tl_trail)
   apply (simp add: rough_state_of_twl_add_learned_cls)
  using clauses_remove_cls\<^sub>N\<^sub>O\<^sub>T rough_state_of_twl_remove_cls by presburger

interpretation cdcl\<^sub>W_twl: state\<^sub>W
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

interpretation cdcl\<^sub>W_twl: cdcl\<^sub>W_ops
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

abbreviation state_eq_twl (infix "\<sim>TWL" 51) where
"state_eq_twl S S' \<equiv> state_eq (rough_state_of_twl S) (rough_state_of_twl S')"
notation cdcl\<^sub>W_twl.state_eq (infix "\<sim>" 51)
declare cdcl\<^sub>W_twl.state_simp[simp del]
  cdcl\<^sub>W_twl.state_simp\<^sub>N\<^sub>O\<^sub>T[simp del]
  cdcl\<^sub>W_twl_NOT.state_simp\<^sub>N\<^sub>O\<^sub>T[simp del]

text \<open>To avoid ambiguities:\<close>
no_notation CDCL_Two_Watched_Literals.twl.state_eq_twl (infix "\<sim>TWL" 51)

definition propagate_twl where
"propagate_twl S S' \<longleftrightarrow>
  (\<exists>L C. (L, C) \<in> candidates_propagate_twl S
  \<and> S' \<sim>TWL cons_trail_twl (Propagated L C) S
  \<and> conflicting_twl S = C_True)"

lemma propagate_twl_iff_propagate:
  assumes inv: "cdcl\<^sub>W_twl.cdcl\<^sub>W_all_struct_inv S"
  shows "cdcl\<^sub>W_twl.propagate S T \<longleftrightarrow> propagate_twl S T" (is "?P \<longleftrightarrow> ?T")
proof
  assume ?P
  then obtain C L where
    "conflicting (rough_state_of_twl S) = C_True" and
    CL_Clauses: "C + {#L#} \<in># cdcl\<^sub>W_twl.clauses S" and
    tr_CNot: "trail_twl S \<Turnstile>as CNot C" and
    undef_lot: "undefined_lit (trail_twl S) L" and
    "T \<sim> cons_trail_twl (Propagated L (C + {#L#})) S"
    unfolding cdcl\<^sub>W_twl.propagate.simps by blast
  have "distinct_mset (C + {#L#})"
    using inv CL_Clauses unfolding cdcl\<^sub>W_twl.cdcl\<^sub>W_all_struct_inv_def
    cdcl\<^sub>W_twl.distinct_cdcl\<^sub>W_state_def cdcl\<^sub>W_twl.clauses_def distinct_mset_set_def
    by (metis (no_types, lifting) add_gr_0  mem_set_mset_iff plus_multiset.rep_eq)
  then have C_L_L: "mset_set (set_mset (C + {#L#}) - {L}) = C"
    by (metis Un_insert_right add_diff_cancel_left' add_diff_cancel_right'
      distinct_mset_set_mset_ident finite_set_mset insert_absorb2 mset_set.insert_remove
      set_mset_single set_mset_union)
  have "(L, C+{#L#}) \<in> candidates_propagate_twl S"
    apply (rule wf_candidates_propagate_complete)
         using rough_state_of_twl apply auto[]
        using CL_Clauses unfolding cdcl\<^sub>W_twl.clauses_def apply auto[]
       apply simp
      using C_L_L tr_CNot apply simp
     using undef_lot apply blast
     done
  show ?T unfolding propagate_twl_def
    apply (rule exI[of _ "L"], rule exI[of _ "C+{#L#}"])
    apply (auto simp: \<open>(L, C+{#L#}) \<in> candidates_propagate_twl S\<close>
      \<open>conflicting (rough_state_of_twl S) = C_True\<close> )
    using \<open>T \<sim> cons_trail_twl (Propagated L (C + {#L#})) S\<close> cdcl\<^sub>W_twl.state_eq_backtrack_lvl
    cdcl\<^sub>W_twl.state_eq_conflicting cdcl\<^sub>W_twl.state_eq_init_clss
    cdcl\<^sub>W_twl.state_eq_learned_clss cdcl\<^sub>W_twl.state_eq_trail state_eq_def by blast
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
    using inv unfolding cdcl\<^sub>W_twl.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_twl.distinct_cdcl\<^sub>W_state_def
    cdcl\<^sub>W_twl.clauses_def distinct_mset_set_def clauses_def by auto
  then have C_L_L: "mset_set (set_mset C - {L}) = C - {#L#}"
    by (metis \<open>C - {#L#} + {#L#} = C\<close> add_left_imp_eq diff_single_trivial
      distinct_mset_set_mset_ident finite_set_mset mem_set_mset_iff mset_set.remove
      multi_self_add_other_not_self union_commute)

  show ?P
    apply (rule cdcl\<^sub>W_twl.propagate.intros[of _ "trail_twl S" "init_clss_twl S"
      "learned_clss_twl S" "backtrack_lvl_twl S" "C-{#L#}" L])
        using confl apply auto[]
       using LC unfolding candidates_propagate_def apply (auto simp: cdcl\<^sub>W_twl.clauses_def)[]
      using wf_candidates_propagate_sound[OF _ LC] rough_state_of_twl apply (simp add: C_L_L)
     using wf_candidates_propagate_sound[OF _ LC] rough_state_of_twl apply simp
    using T unfolding cdcl\<^sub>W_twl.state_eq_def state_eq_def by auto
qed

term local.state_eq_twl
term CDCL_Two_Watched_Literals.twl.state_eq_twl
definition conflict_twl where
"conflict_twl S S' \<longleftrightarrow>
  (\<exists>C. C \<in> candidates_conflict_twl S
  \<and> S' \<sim>TWL update_conflicting_twl (C_Clause C) S
  \<and> conflicting_twl S = C_True)"

lemma conflict_twl_iff_conflict:
  shows "cdcl\<^sub>W_twl.conflict S T \<longleftrightarrow> conflict_twl S T" (is "?C \<longleftrightarrow> ?T")
proof
  assume ?C
  then obtain M N U k C where
    S: "state (rough_state_of_twl S) = (M, N, U, k, C_True)" and
    C: "C \<in># cdcl\<^sub>W_twl.clauses S" and
    M_C: "M \<Turnstile>as CNot C" and
    T: "T \<sim> update_conflicting_twl (C_Clause C) S"
    by auto
  have "C \<in> candidates_conflict_twl S"
    apply (rule wf_candidates_conflict_complete)
       apply simp
      using C apply (auto simp: cdcl\<^sub>W_twl.clauses_def)[]
    using M_C S by auto
  moreover have "T \<sim>TWL twl_of_rough_state (update_conflicting (C_Clause C) (rough_state_of_twl S))"
    using T unfolding state_eq_def cdcl\<^sub>W_twl.state_eq_def by auto
  ultimately show ?T
    using S unfolding conflict_twl_def by auto
next
  assume ?T
  then obtain C where
    C: "C \<in> candidates_conflict_twl S" and
    T: "T \<sim>TWL update_conflicting_twl (C_Clause C) S" and
    confl: "conflicting_twl S = C_True"
    unfolding conflict_twl_def by auto
  have "C \<in># cdcl\<^sub>W_twl.clauses S"
    using C unfolding candidates_conflict_def cdcl\<^sub>W_twl.clauses_def by auto
 moreover have "trail_twl S \<Turnstile>as CNot C"
    using wf_candidates_conflict_sound[OF _ C] by auto
 ultimately show ?C apply -
   apply (rule cdcl\<^sub>W_twl.conflict.conflict_rule[of _ _ _ _ _ C])
   using confl T unfolding state_eq_def cdcl\<^sub>W_twl.state_eq_def by auto
qed

inductive cdcl\<^sub>W_twl :: "'v wf_twl \<Rightarrow> 'v wf_twl \<Rightarrow> bool" for S :: "'v wf_twl" where
propagate: "propagate_twl S S' \<Longrightarrow> cdcl\<^sub>W_twl S S'" |
conflict: "conflict_twl S S' \<Longrightarrow> cdcl\<^sub>W_twl S S'" |
other: "cdcl\<^sub>W_twl.cdcl\<^sub>W_o S S' \<Longrightarrow> cdcl\<^sub>W_twl S S'"|
rf: "cdcl\<^sub>W_twl.cdcl\<^sub>W_rf S S' \<Longrightarrow> cdcl\<^sub>W_twl S S'"

lemma cdcl\<^sub>W_twl_iff_cdcl\<^sub>W:
  assumes "cdcl\<^sub>W_twl.cdcl\<^sub>W_all_struct_inv S"
  shows "cdcl\<^sub>W_twl S T \<longleftrightarrow> cdcl\<^sub>W_twl.cdcl\<^sub>W S T"
  by (simp add: assms cdcl\<^sub>W_twl.cdcl\<^sub>W.simps cdcl\<^sub>W_twl.simps conflict_twl_iff_conflict
    propagate_twl_iff_propagate)

lemma rtranclp_cdcl\<^sub>W_twl_all_struct_inv_inv:
  assumes "cdcl\<^sub>W_twl\<^sup>*\<^sup>* S T" and "cdcl\<^sub>W_twl.cdcl\<^sub>W_all_struct_inv S"
  shows "cdcl\<^sub>W_twl.cdcl\<^sub>W_all_struct_inv T"
  using assms by (induction rule: rtranclp_induct)
  (simp_all add: cdcl\<^sub>W_twl_iff_cdcl\<^sub>W cdcl\<^sub>W_twl.cdcl\<^sub>W_all_struct_inv_inv)

lemma rtranclp_cdcl\<^sub>W_twl_iff_rtranclp_cdcl\<^sub>W:
  assumes "cdcl\<^sub>W_twl.cdcl\<^sub>W_all_struct_inv S"
  shows "cdcl\<^sub>W_twl\<^sup>*\<^sup>* S T \<longleftrightarrow> cdcl\<^sub>W_twl.cdcl\<^sub>W\<^sup>*\<^sup>* S T" (is "?T \<longleftrightarrow> ?W")
proof
  assume ?W
  then show ?T
    proof (induction rule: rtranclp_induct)
      case base
      then show ?case by simp
    next
      case (step T U) note st = this(1) and cdcl = this(2) and IH = this(3)
      have "cdcl\<^sub>W_twl T U"
        using assms st cdcl cdcl\<^sub>W_twl.rtranclp_cdcl\<^sub>W_all_struct_inv_inv cdcl\<^sub>W_twl_iff_cdcl\<^sub>W
        by blast
      then show ?case using IH by auto
    qed
next
  assume ?T
  then show ?W
    proof (induction rule: rtranclp_induct)
      case base
      then show ?case by simp
    next
      case (step T U) note st = this(1) and cdcl = this(2) and IH = this(3)
      have "cdcl\<^sub>W_twl.cdcl\<^sub>W T U"
        using assms st cdcl rtranclp_cdcl\<^sub>W_twl_all_struct_inv_inv cdcl\<^sub>W_twl_iff_cdcl\<^sub>W
        by blast
      then show ?case using IH by auto
    qed
qed

interpretation cdcl\<^sub>N\<^sub>O\<^sub>T_twl: backjumping_ops
  "\<lambda>S. convert_trail_from_W (trail_twl S)"
  abstract_twl.raw_clauses_twl
  "\<lambda>L (S:: 'v wf_twl).
    cons_trail_twl
      (convert_marked_lit_from_NOT L) (S:: 'v wf_twl)"
  tl_trail_twl
  add_learned_cls_twl
  remove_cls_twl
  (* bj conditions *) "\<lambda>C _ _ (S:: 'v wf_twl) _. C \<in> candidates_conflict_twl S"
  by unfold_locales

lemma reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_skip_beginning_twl:
  assumes "trail_twl S = convert_trail_from_NOT (F' @ F)"
  shows "trail_twl (cdcl\<^sub>W_twl.reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S) = convert_trail_from_NOT F"
  using assms by (induction F' arbitrary: S) auto

lemma reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_trail_tl_trail_twl_decomp[simp]:
  "trail_twl S = convert_trail_from_NOT (F' @ Marked K () # F) \<Longrightarrow>
     trail_twl (cdcl\<^sub>W_twl.reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F (tl_trail_twl S)) = convert_trail_from_NOT F"
  apply (rule reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_skip_beginning_twl[of _ "tl (F' @ Marked K () # [])"])
  by (cases F') (auto simp add:tl_append reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_skip_beginning)

thm tl_append reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_skip_beginning cdcl\<^sub>W_twl.reduce_trail_to\<^sub>N\<^sub>O\<^sub>T.simps
lemma trail_twl_reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_drop:
  "trail_twl (cdcl\<^sub>W_twl.reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S) =
    (if length (trail_twl S) \<ge> length F
    then drop (length (trail_twl S) - length F) (trail_twl S)
    else [])"
  apply (induction F S rule: cdcl\<^sub>W_twl.reduce_trail_to\<^sub>N\<^sub>O\<^sub>T.induct)
  apply (rename_tac F S)
  apply (case_tac "trail_twl S")
   apply auto[]
  apply (rename_tac list)
  apply (case_tac "Suc (length list) > length F")
   prefer 2 apply simp
  apply (subgoal_tac "Suc (length list) - length F = Suc (length list - length F)")
   apply simp
  apply simp
  done

(* TODO Move? *)
lemma convert_trail_from_NOT_convert_trail_from_W:
  "(\<forall>l\<in>set F. is_marked l \<and> level_of l = 0 \<or> is_proped l \<and> mark_of l = {#}) \<Longrightarrow>
    convert_trail_from_NOT (convert_trail_from_W F) = F"
  by (induction F rule: marked_lit_list_induct) auto

lemma undefined_lit_convert_trail_from_NOT[simp]:
  "undefined_lit (convert_trail_from_NOT F) L \<longleftrightarrow> undefined_lit F L"
  by (induction F rule: marked_lit_list_induct) (auto simp: defined_lit_map)

lemma lits_of_convert_trail_from_NOT:
  "lits_of (convert_trail_from_NOT F) = lits_of F"
  by (induction F rule: marked_lit_list_induct) auto

(* TODO Move to List_More *)
lemma map_eq_cons_decomp:
  assumes SF: "map f l = xs @ ys"
  shows "\<exists>xs' ys'. l = xs' @ ys' \<and> map f xs' = xs \<and> map f ys' = ys"
proof -
  let ?F' = "take (length xs) l"
  let ?G = "drop (length xs) l"
  have tr1: "l = ?F' @ ?G"
    by simp
  moreover
    have [simp]: "length l = length xs + length ys"
      using arg_cong[OF SF, of length] by auto
    have "map f ?F' = xs" and  "map f ?G = ys"
       using arg_cong[OF SF, of "take (length xs)"] apply (subst (asm) tr1)
       unfolding map_append apply simp
      using arg_cong[OF SF, of "drop (length xs)"] apply (subst (asm) tr1)
      unfolding map_append apply simp
      done
  ultimately show ?thesis by blast
qed

(* END Move? *)

lemma
  fixes F F' :: "('v, unit, unit) marked_lit list"
  assumes SF: "convert_trail_from_W (trail_twl S) = F' @ Marked K () # F"
  shows "\<exists>F' K. trail_twl S = convert_trail_from_NOT F' @ Marked K 0 # convert_trail_from_NOT F"
proof -
  obtain G' H where
    tr_S: "trail_twl S = G' @ H" and
    "convert_trail_from_W G' = F'" and
    H: "convert_trail_from_W H = Marked K () # F"
  using map_eq_cons_decomp[OF SF] by auto

  obtain G HK where
    H_G: "H = HK @ G" and
    HK: "convert_trail_from_W HK = [Marked K ()]" and
    "convert_trail_from_W G = F"
    using H map_eq_cons_decomp[of convert_marked_lit_from_W H "[Marked K ()]" F, simplified]
    by meson
  obtain n where [simp]: "HK = [Marked K n]"
    using HK apply auto
    apply (rename_tac L)
    apply (case_tac L)
    apply auto
    done
  show ?thesis
    using tr_S unfolding H_G apply simp
oops

interpretation cdcl\<^sub>N\<^sub>O\<^sub>T_twl: dpll_with_backjumping_ops
  "\<lambda>S. convert_trail_from_W (trail_twl S)"
  abstract_twl.raw_clauses_twl
  "\<lambda>L (S:: 'v wf_twl).
    cons_trail_twl
      (convert_marked_lit_from_NOT L) (S:: 'v wf_twl)"
  tl_trail_twl
  add_learned_cls_twl
  remove_cls_twl
  (* propagate conditions: *)"\<lambda>L S. lit_of L \<in> fst ` candidates_propagate_twl S"
  (* state invariant *)"\<lambda>S. no_dup (trail_twl S)
      (* \<and> (\<forall>l \<in> set (trail_twl S). (is_marked l \<and> level_of l = 0) \<or> (is_proped l \<and> mark_of l = 0)) *)"
  (* backjump conditions *)"\<lambda>C _ _ (S:: 'v wf_twl) _. C \<in> candidates_conflict_twl S"
proof (unfold_locales, goal_cases)
  case (1 C' S C F' K F L)
  let ?T' = "(cons_trail (Propagated L {#}) (rough_state_of_twl (cdcl\<^sub>W_twl.reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S)))"
  let ?T = "(cons_trail_twl (Propagated L {#}) (cdcl\<^sub>W_twl.reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S))"
  have tr_F_S: "trail_twl (cdcl\<^sub>W_twl.reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S) = convert_trail_from_NOT F"
    apply (subst trail_twl_reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_drop[of F S])
    using 1(1) arg_cong[OF 1(3), of length] apply auto sorry

  have "no_dup (trail_twl S)"
    using "1"(1) by blast
  have "wf_twl_state (rough_state_of_twl (cdcl\<^sub>W_twl.reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S))"
    using wf_twl_state_rough_state_of_twl by blast

  then have "wf_twl_state ?T'"
    by (simp add: "1"(6) tr_F_S wf_twl_state_cons_trail)
  then have "init_clss_twl ?T = init_clss_twl (cdcl\<^sub>W_twl.reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S)"
      using 1(6) by (simp_all add: tr_F_S twl_of_rough_state_inverse)
  then have [simp]: "init_clss_twl ?T = init_clss_twl S"
     by (simp add: cdcl\<^sub>W_twl.reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_reduce_trail_convert)

  have "learned_clss_twl ?T = learned_clss_twl (cdcl\<^sub>W_twl.reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S)"
    by (smt "1"(3) "1"(6) append_assoc cdcl\<^sub>W_twl.learned_clss_cons_trail
      cdcl\<^sub>W_twl_NOT.reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_eq_length cdcl\<^sub>W_twl_NOT.reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_nil
      cdcl\<^sub>W_twl_NOT.reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_skip_beginning comp_apply defined_lit_convert_trail_from_W
      list.sel(3) marked_lit.sel(2) rev.simps(2) rev_append rev_eq_Cons_iff)
  moreover have "learned_clss_twl (cdcl\<^sub>W_twl.reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S)
    = learned_clss_twl S"
    by (simp add: cdcl\<^sub>W_twl.reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_reduce_trail_convert)
  ultimately have [simp]: "learned_clss_twl ?T = learned_clss_twl S"
    by simp
  have tr_L_F_S: "trail_twl ?T = Propagated L {#} # convert_trail_from_NOT F"
    using 1(1,6) tr_F_S by simp
  have C_confl_cand: "C \<in> candidates_conflict_twl S"
    apply(rule wf_candidates_twl_conflict_complete)
     using 1(1,4) apply (simp del: cdcl\<^sub>W_twl.state_simp add: clauses_def)
    using 1(5) by (simp add: tr_L_F_S true_annots_true_cls lits_of_convert_trail_from_NOT)

  have "cdcl\<^sub>N\<^sub>O\<^sub>T_twl.backjump S
    (cons_trail_twl (convert_marked_lit_from_NOT (Propagated L ()))
      (cdcl\<^sub>W_twl.reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S))"
    apply (rule cdcl\<^sub>N\<^sub>O\<^sub>T_twl.backjump.intros[of S F' K F _ L C, OF 1(3) _ 1(4-6) _ 1(8-9)])
      unfolding cdcl\<^sub>W_twl_NOT.state_eq\<^sub>N\<^sub>O\<^sub>T_def apply (metis convert_marked_lit_from_NOT.simps(1))
     using 1(7) 1(3) apply presburger
    using C_confl_cand by simp
  then show ?case
    by blast
qed
(*
lemma
  assumes
    dpll: "cdcl\<^sub>N\<^sub>O\<^sub>T_twl.dpll_bj S T" and
    n_d: "no_dup (trail_twl S)" and
    tr: "\<forall>l\<in>set (trail_twl S). is_marked l \<and> level_of l = 0 \<or> is_proped l \<and> mark_of l = {#}"
  shows "(\<forall>l\<in>set (trail_twl T). is_marked l \<and> level_of l = 0 \<or> is_proped l \<and> mark_of l = {#})"
    (is "?tr T")
proof -
  have "no_dup (trail_twl T)"
    using cdcl\<^sub>N\<^sub>O\<^sub>T_twl.dpll_bj_no_dup[OF dpll] n_d tr by simp
  have H: "no_dup (trail_twl S) \<and>
    (\<forall>l\<in>set (trail_twl S). is_marked l \<and> level_of l = 0 \<or> is_proped l \<and> mark_of l = {#})"
    using tr n_d by auto
  show ?thesis
    using dpll H
    proof (induction rule: cdcl\<^sub>N\<^sub>O\<^sub>T_twl.dpll_bj_all_induct)
      case (decide\<^sub>N\<^sub>O\<^sub>T L T) note undef =this(1) and L = this(2) and T = this(3)
      have "?tr (cons_trail_twl (convert_marked_lit_from_NOT (Marked L ())) S)"
        using undef tr by simp
      have "convert_trail_from_W (trail_twl T) =
        convert_trail_from_W (trail_twl (cons_trail_twl (convert_marked_lit_from_NOT (Marked L ())) S))"
        using cdcl\<^sub>W_twl_NOT.state_simp\<^sub>N\<^sub>O\<^sub>T(1)[OF T] by simp
      from arg_cong[OF this, of convert_trail_from_NOT]
      have "trail_twl T = trail_twl (cons_trail_twl (convert_marked_lit_from_NOT (Marked L ())) S)"
        using undef apply (simp add: convert_trail_from_NOT_convert_trail_from_W tr)
        thm cdcl\<^sub>W_twl_NOT.state_eq\<^sub>N\<^sub>O\<^sub>T_def
    apply simp
    thm cdcl\<^sub>W_twl_NOT.state_simp\<^sub>N\<^sub>O\<^sub>T *)

interpretation cdcl\<^sub>N\<^sub>O\<^sub>T_twl: dpll_with_backjumping
  "\<lambda>S. convert_trail_from_W (trail_twl S)"
  abstract_twl.raw_clauses_twl
  "\<lambda>L (S:: 'v wf_twl).
    cons_trail_twl
      (convert_marked_lit_from_NOT L) (S:: 'v wf_twl)"
  tl_trail_twl
  add_learned_cls_twl
  remove_cls_twl
  (* propagate conditions: *)"\<lambda>L S. lit_of L \<in> fst ` candidates_propagate_twl S"
  (* state invariant *)"\<lambda>S. no_dup (trail_twl S)
      (* \<and> (\<forall>l \<in> set (trail_twl S). (is_marked l \<and> level_of l = 0) \<or> (is_proped l \<and> mark_of l = 0)) *)"
  (* backjump conditions *)"\<lambda>C _ _ (S:: 'v wf_twl) _. C \<in> candidates_conflict_twl S"
apply (unfold_locales, goal_cases)
oops
end

end
