(*  Title: CDCL with Two Watched Literals
    Author: Jasmin Blanchette <jasmin.blanchette@inria.fr>
    Author: Mathias Fleury <mathias.fleury@mpi-inf.mpg.de>
*)

section \<open>2-Watched-Literal\<close>

theory CDCL_Two_Watched_Literals
imports CDCL_WNOT (* Have to decide which imports are the best *)
begin
text \<open>First we define here the core of the two-watched literal data structure:
  \<^enum> A clause is composed of (at most) two watched literals.
  \<^enum> It is sufficient to find the candidates for propagation and conflict from the clauses such that
  the new literal is watched.\<close>
text \<open>
  While this it the principle behind the two-watched literals, an implementation have to remember
  the candidates that have been found so far while updating the data structure.

  We will directly on the two-watched literals data structure with lists: it could be also
  seen as a state over some abstract clause representation we would later refine as lists. However,
  as we need a way to select element from a clause, working on lists is better.\<close>


subsection \<open>Essence of 2-WL\<close>
subsubsection \<open>Data structure and Access Functions\<close>

text \<open>Only the 2-watched literals have to be verified here: the backtrack level and the trail that
  appear in the state are not related to the 2-watched algoritm.\<close>

datatype 'v twl_clause =
  TWL_Clause (watched: "'v literal list") (unwatched: "'v literal list")

datatype 'v twl_state =
  TWL_State (raw_trail: "('v, 'v twl_clause) ann_lits")
    (raw_init_clss: "'v twl_clause list")
    (raw_learned_clss: "'v twl_clause list") (backtrack_lvl: nat)
    (raw_conflicting: "'v literal list option")

fun mmset_of_mlit :: "('v, 'v twl_clause) ann_lit  \<Rightarrow> ('v, 'v clause) ann_lit"
  where
"mmset_of_mlit (Propagated L C) = Propagated L (mset (watched C @ unwatched C))" |
"mmset_of_mlit (Decided L) = Decided L"

lemma lit_of_mmset_of_mlit[simp]: "lit_of (mmset_of_mlit x) = lit_of x"
  by (cases x) auto

lemma lits_of_mmset_of_mlit[simp]: "lits_of (mmset_of_mlit ` S) = lits_of S"
  by (auto simp: lits_of_def image_image)

abbreviation trail where
"trail S \<equiv> map mmset_of_mlit (raw_trail S)"

abbreviation clauses_of_l where
  "clauses_of_l \<equiv> \<lambda>L. mset (map mset L)"

definition raw_clause :: "'v twl_clause \<Rightarrow> 'v literal list" where
  "raw_clause C \<equiv> watched C @ unwatched C"

definition clause :: "'v twl_clause \<Rightarrow> 'v clause" where
  "clause C \<equiv> mset (raw_clause C)"

lemma clause_def_lambda:
  "clause = (\<lambda>C. mset (raw_clause C))"
  by (auto simp: clause_def)

abbreviation raw_clss :: "'v twl_state \<Rightarrow> 'v clauses" where
  "raw_clss S \<equiv> mset (map clause (raw_init_clss S @ raw_learned_clss S))"

abbreviation raw_clss_l :: "'a twl_clause list \<Rightarrow> 'a literal multiset multiset" where
  "raw_clss_l C \<equiv> mset (map clause C)"

interpretation raw_cls clause .

lemma mset_map_clause_remove1_cond:
  "mset (map (\<lambda>x. mset (unwatched x) + mset (watched x))
    (remove1_cond (\<lambda>D. clause D = clause a) Cs)) =
   remove1_mset (clause a) (mset (map clause Cs))"
   apply (induction Cs)
     apply simp
   by (auto simp: ac_simps remove1_mset_single_add raw_clause_def clause_def)

interpretation raw_clss
  clause
  raw_clss_l "op @"
  "\<lambda>L C. L \<in> set C" "op #" "\<lambda>C. remove1_cond (\<lambda>D. clause D = clause C)"
  apply (unfold_locales)
  using mset_map_clause_remove1_cond by (auto simp: hd_map comp_def map_tl ac_simps raw_clause_def
    union_mset_list mset_map_mset_remove1_cond ex_mset clause_def_lambda)

lemma ex_mset_unwatched_watched:
  "\<exists>a. mset (unwatched a) + mset (watched a) = E"
proof -
  obtain e where "mset e = E"
    using ex_mset by blast
  then have "mset (unwatched (TWL_Clause [] e)) + mset (watched (TWL_Clause [] e)) = E"
    by auto
  then show ?thesis by fast
qed

interpretation twl: state\<^sub>W_ops
  clause
  raw_clss_l "op @"
  "\<lambda>L C. L \<in> set C" "op #" "\<lambda>C. remove1_cond (\<lambda>D. clause D = clause C)"

  mset "\<lambda>xs ys. case_prod append (fold (\<lambda>x (ys, zs). (remove1 x ys, x # zs)) xs (ys, []))"
  remove1

  raw_clause "\<lambda>C. TWL_Clause [] C"
  trail "\<lambda>S. hd (raw_trail S)"
  raw_init_clss raw_learned_clss backtrack_lvl raw_conflicting
  rewrites
    "twl.mmset_of_mlit = mmset_of_mlit"
proof goal_cases
  case 1
  show H: ?case
  apply unfold_locales apply (auto simp: hd_map comp_def map_tl ac_simps raw_clause_def
    union_mset_list mset_map_mset_remove1_cond ex_mset_unwatched_watched clause_def)
  done

  case 2
  show ?case
    apply (rule ext)
    apply (rename_tac x)
    apply (case_tac x)
    apply (simp_all add: state\<^sub>W_ops.mmset_of_mlit.simps[OF H] raw_clause_def clause_def)
  done
qed

declare CDCL_Two_Watched_Literals.twl.mset_ccls_ccls_of_cls[simp del]

definition
  candidates_propagate :: "'v twl_state \<Rightarrow> ('v literal \<times> 'v twl_clause) set"
where
  "candidates_propagate S =
   {(L, C) | L C.
     C \<in> set (twl.raw_clauses S)  \<and>
     set (watched C) - (uminus ` lits_of_l (trail S)) = {L} \<and>
     undefined_lit (raw_trail S) L}"

definition candidates_conflict :: "'v twl_state \<Rightarrow> 'v twl_clause set" where
  "candidates_conflict S =
   {C. C \<in> set (twl.raw_clauses S) \<and>
     set (watched C) \<subseteq> uminus ` lits_of_l (raw_trail S)}"

primrec (nonexhaustive) index :: "'a list \<Rightarrow>'a \<Rightarrow> nat" where
"index (a # l) c = (if a = c then 0 else 1+index l c)"

lemma index_nth:
  "a \<in> set l \<Longrightarrow> l ! (index l a) = a"
  by (induction l) auto


subsubsection \<open>Invariants\<close>
text \<open>The structural invariants states that there are at most two watched elements, that the watched
  literals are distinct, and that there are 2 watched literals if there are at least than two
  different literals in the full clauses.\<close>
primrec struct_wf_twl_cls :: "'v twl_clause \<Rightarrow> bool" where
"struct_wf_twl_cls (TWL_Clause W UW) \<longleftrightarrow>
   distinct W \<and> length W \<le> 2 \<and> (length W < 2 \<longrightarrow> set UW \<subseteq> set W)"

text \<open>We need the following property about updates: if there is a literal @{term L} with
  @{term "-L"} in the trail, and @{term L} is not  watched, then it stays unwatched; i.e., while
  updating with @{term rewatch}, @{term L} does not get swapped with a watched literal @{term L'}
  such that @{term "-L'"} is in the trail. This corresponds to the laziness of the data structure.

  Remark that @{term M} is a trail: literals at the end were the first to be added to the trail.\<close>
primrec watched_only_lazy_updates :: "('v, 'mark) ann_lits \<Rightarrow>
  'v twl_clause \<Rightarrow> bool"
  where
"watched_only_lazy_updates M (TWL_Clause W UW) \<longleftrightarrow>
  (\<forall>L'\<in> set W. \<forall>L\<in> set UW.
    -L' \<in> lits_of_l M \<longrightarrow> -L \<in> lits_of_l M \<longrightarrow> L \<notin> set W \<longrightarrow>
      index (map lit_of M) (-L') \<le> index (map lit_of M) (-L))"

text \<open>If the negation of a watched literal is included in the trail, then the negation of
  every unwatched literals is also included in the trail. Otherwise, the data-structure has to be
  updated.\<close>
primrec watched_wf_twl_cls :: "('a, 'b) ann_lits \<Rightarrow> 'a twl_clause \<Rightarrow>
  bool" where
"watched_wf_twl_cls M (TWL_Clause W UW) \<longleftrightarrow>
   (\<forall>L \<in> set W. -L \<in> lits_of_l M \<longrightarrow> (\<forall>L' \<in> set UW. L' \<notin> set W \<longrightarrow> -L' \<in> lits_of_l M))"

text \<open>Here are the invariant strictly related to the 2-WL data structure.\<close>
primrec wf_twl_cls :: "('v, 'mark) ann_lits \<Rightarrow> 'v twl_clause \<Rightarrow> bool" where
  "wf_twl_cls M (TWL_Clause W UW) \<longleftrightarrow>
   struct_wf_twl_cls (TWL_Clause W UW) \<and> watched_wf_twl_cls M (TWL_Clause W UW) \<and>
   watched_only_lazy_updates M (TWL_Clause W UW)"

lemma wf_twl_cls_annotation_independant:
  assumes M: "map lit_of M = map lit_of M'"
  shows "wf_twl_cls M (TWL_Clause W UW) \<longleftrightarrow> wf_twl_cls M' (TWL_Clause W UW)"
proof -
  have "lits_of_l M = lits_of_l M'"
    using arg_cong[OF M, of set] by (simp add: lits_of_def)
  then show ?thesis
    by (simp add: lits_of_def M)
qed

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
      LW: "L \<in> set W" and
      LM: "- L \<in> lits_of_l M'" and
      L'UW: "L' \<in> set UW" and
      "L'\<notin> set W"
    then have
      L'M: "- L' \<in> lits_of_l M"
      using wf by (auto simp: C M)
    have "watched_only_lazy_updates M C"
      using wf by (auto simp: C)
    then have
      "index (map lit_of M) (-L) \<le> index (map lit_of M) (-L')"
      using LM L'M L'UW LW \<open>L'\<notin> set W\<close> C M unfolding lits_of_def
      by (fastforce simp: lits_of_def)
    then have "- L' \<in> lits_of_l M'"
      using \<open>L'\<notin> set W\<close> LW L'M by (auto simp: C M split: if_split_asm)
  }
  moreover
    {
      fix L' L
      assume
        "L' \<in> set W" and
        "L \<in> set UW" and
        L'M: "- L' \<in> lits_of_l M'" and
        "- L \<in> lits_of_l M'" and
        "L \<notin> set W"
      moreover
        have "lit_of l \<noteq> - L'"
        using n_d unfolding M
          by (metis (no_types) L'M M Decided_Propagated_in_iff_in_lits_of_l defined_lit_map
            distinct.simps(2) list.simps(9) set_map)
      moreover have "watched_only_lazy_updates M C"
        using wf by (auto simp: C)
      ultimately have "index (map lit_of M') (- L') \<le> index (map lit_of M') (- L)"
        by (fastforce simp: M C split: if_split_asm)
    }
  moreover have "distinct W" and "length W \<le> 2" and "(length W < 2 \<longrightarrow> set UW \<subseteq> set W)"
    using wf by (auto simp: C M)
  ultimately show ?thesis by (auto simp add: M C)
qed

lemma wf_twl_cls_append:
  assumes
    n_d: "no_dup (M' @ M)" and
    wf: "wf_twl_cls (M' @ M) C"
  shows "wf_twl_cls M C"
  using wf n_d apply (induction M')
    apply simp
  using wf_twl_cls_wf_twl_cls_tl by fastforce

definition wf_twl_state :: "'v twl_state \<Rightarrow> bool" where
  "wf_twl_state S \<longleftrightarrow>
    (\<forall>C \<in> set (twl.raw_clauses S). wf_twl_cls (raw_trail S) C) \<and> no_dup (raw_trail S)"

lemma wf_candidates_propagate_sound:
  assumes wf: "wf_twl_state S" and
    cand: "(L, C) \<in> candidates_propagate S"
  shows "raw_trail S \<Turnstile>as CNot (mset (removeAll L (raw_clause C))) \<and> undefined_lit (raw_trail S) L"
    (is "?Not \<and> ?undef")
proof
  def M \<equiv> "raw_trail S"
  def N \<equiv> "raw_init_clss S"
  def U \<equiv> "raw_learned_clss S"

  note MNU_defs [simp] = M_def N_def U_def

  have cw:
    "C \<in> set (N @ U)"
    "set (watched C) - uminus ` lits_of_l M = {L}"
    "undefined_lit M L"
    using cand unfolding candidates_propagate_def MNU_defs twl.raw_clauses_def by auto

  obtain W UW where cw_eq: "C = TWL_Clause W UW"
    by (cases C)

  have l_w: "L \<in> set W"
    using cw(2) cw_eq by auto

  have wf_c: "wf_twl_cls M C"
    using wf cw(1) unfolding wf_twl_state_def by (simp add: twl.raw_clauses_def)

  have w_nw:
    "distinct W"
    "length W < 2 \<Longrightarrow> set UW \<subseteq> set W"
    "\<And>L L'. L \<in> set W \<Longrightarrow> -L \<in> lits_of_l M \<Longrightarrow> L' \<in> set UW \<Longrightarrow> L' \<notin> set W \<Longrightarrow> -L' \<in> lits_of_l M"
   using wf_c unfolding cw_eq by (auto simp: image_image)

  have "\<forall>L' \<in> set (raw_clause C) - {L}. -L' \<in> lits_of_l M"
  proof (cases "length W < 2")
    case True
    moreover have "size W \<noteq> 0"
      using cw(2) cw_eq by auto
    ultimately have "size W = 1"
      by linarith
    then have w: "W = [L]"
      using l_w by (auto simp: length_list_Suc_0)
    from True have "set UW \<subseteq> set W"
      using w_nw(2) by blast
    then show ?thesis
      using w cw(1) cw_eq by (auto simp: raw_clause_def)
  next
    case sz2: False
    show ?thesis
    proof
      fix L'
      assume l': "L' \<in> set (raw_clause C) - {L}"
      have ex_la: "\<exists>La. La \<noteq> L \<and> La \<in> set W"
      proof (cases W)
        case w: Nil
        thus ?thesis
          using l_w by auto
      next
        case lb: (Cons Lb W')
        show ?thesis
        proof (cases W')
          case Nil
          thus ?thesis
            using lb sz2 by simp
        next
          case lc: (Cons Lc W'')
          thus ?thesis
            by (metis distinct_length_2_or_more lb list.set_intros(1) list.set_intros(2) w_nw(1))
        qed
      qed
      then obtain La where la: "La \<noteq> L" "La \<in> set W"
        by blast
      then have "La \<in> uminus ` lits_of_l M"
        using cw(2)[unfolded cw_eq, simplified, folded M_def] \<open>La \<in> set W\<close> \<open>La \<noteq> L\<close> by auto
      then have nla: "-La \<in> lits_of_l M"
        by (auto simp: image_image)
      then show "-L' \<in> lits_of_l M"
      (*based on a proof generated by Sledgehammer in two iterations *)
      proof -
        have f1: "L' \<in> set (raw_clause C)"
          using l' by blast
        have f2: "L' \<notin> {L}"
          using l' by fastforce
        have "\<And>l L. - (l::'a literal) \<in> L \<or> l \<notin> uminus ` L"
          by force
        then show ?thesis
          using cw(1) cw_eq w_nw(3) raw_clause_def by (metis DiffI Un_iff cw(2) f1 f2 la(2) nla
            set_append twl_clause.sel(1) twl_clause.sel(2))
      qed
    qed
  qed
  then show "?Not"
    unfolding true_annots_def by (auto simp: image_image Ball_def CNot_def)

  show ?undef
    using cw(3) unfolding M_def by blast
qed

lemma wf_candidates_propagate_complete:
  assumes wf: "wf_twl_state S" and
    c_mem: "C \<in> set (twl.raw_clauses S)" and
    l_mem: "L \<in> set (raw_clause C)" and
    unsat: "trail S \<Turnstile>as CNot (mset_set (set (raw_clause C) - {L}))" and
    undef: "undefined_lit (raw_trail S) L"
  shows "(L, C) \<in> candidates_propagate S"
proof -
  def M \<equiv> "raw_trail S"
  def N \<equiv> "raw_init_clss S"
  def U \<equiv> "raw_learned_clss S"

  note MNU_defs [simp] = M_def N_def U_def

  obtain W UW where cw_eq: "C = TWL_Clause W UW"
    by (cases C, blast)

  have wf_c: "wf_twl_cls M C"
    using wf c_mem unfolding wf_twl_state_def by simp

  have w_nw:
    "distinct W"
    "length W < 2 \<Longrightarrow> set UW \<subseteq> set W"
    "\<And>L L'. L \<in> set W \<Longrightarrow> -L \<in> lits_of_l M \<Longrightarrow> L' \<in> set UW \<Longrightarrow> L' \<notin> set W \<Longrightarrow> -L' \<in> lits_of_l M"
   using wf_c unfolding cw_eq by (auto simp: image_image)

  have unit_set: "set W - (uminus ` lits_of_l M) = {L}" (is "?W = ?L")
  proof
    show "?W \<subseteq> {L}"
    proof
      fix L'
      assume l': "L' \<in> ?W"
      hence l'_mem_w: "L' \<in> set W"
        by (simp add: in_diffD)
      have "L' \<notin> uminus ` lits_of_l M"
        using l' by blast
      then have "\<not> M \<Turnstile>a {#-L'#}"
        by (auto simp: lits_of_def uminus_lit_swap image_image)
      moreover have "L' \<in> set (raw_clause C)"
        using c_mem cw_eq l'_mem_w by (auto simp: raw_clause_def)
      ultimately have "L' = L"
        using unsat[unfolded CNot_def true_annots_def, simplified]
        unfolding M_def by fastforce
      then show "L' \<in> {L}"
        by simp
    qed
  next
    show "{L} \<subseteq> ?W"
    proof clarify
      have "L \<in> set W"
      proof (cases W)
        case Nil
        thus ?thesis
          using w_nw(2) cw_eq l_mem by (auto simp: raw_clause_def)
      next
        case (Cons La W')
        thus ?thesis
        proof (cases "La = L")
          case True
          thus ?thesis
            using Cons by simp
        next
          case False
          have "-La \<in> lits_of_l M"
            using False Cons cw_eq unsat[unfolded CNot_def true_annots_def, simplified]
            by (fastforce simp: raw_clause_def)
          then show ?thesis
            using Cons cw_eq l_mem undef w_nw(3)
            by (auto simp: Decided_Propagated_in_iff_in_lits_of_l raw_clause_def)
        qed
      qed
      moreover have "L \<notin># mset_set (uminus ` lits_of_l M)"
        using undef by (auto simp: Decided_Propagated_in_iff_in_lits_of_l image_image)
      ultimately show "L \<in> ?W"
        by simp
    qed
  qed

  show ?thesis
    unfolding candidates_propagate_def using unit_set undef c_mem unfolding cw_eq M_def
    by (auto simp: image_image cw_eq intro!: exI[of _ C])
qed

lemma wf_candidates_conflict_sound:
  assumes wf: "wf_twl_state S" and
    cand: "C \<in> candidates_conflict S"
  shows "trail S \<Turnstile>as CNot (clause C) \<and> C \<in> set (twl.raw_clauses S)"
proof
  def M \<equiv> "raw_trail S"
  def N \<equiv> "raw_init_clss S"
  def U \<equiv> "raw_learned_clss S"

  note MNU_defs [simp] = M_def N_def U_def

  have cw:
    "C \<in> set (N @ U)"
    "set (watched C) \<subseteq> uminus ` lits_of_l (trail S)"
    using cand[unfolded candidates_conflict_def, simplified] unfolding twl.raw_clauses_def by auto

  obtain W UW where cw_eq: "C = TWL_Clause W UW"
    by (cases C, blast)

  have wf_c: "wf_twl_cls M C"
    using wf cw(1) unfolding wf_twl_state_def by (simp add: comp_def twl.raw_clauses_def)

  have w_nw:
    "distinct W"
    "length W < 2 \<Longrightarrow> set UW \<subseteq> set W"
    "\<And>L L'. L \<in> set W \<Longrightarrow> -L \<in> lits_of_l M \<Longrightarrow> L' \<in> set UW \<Longrightarrow> L' \<notin> set W \<Longrightarrow> -L' \<in> lits_of_l M"
   using wf_c unfolding cw_eq by (auto simp: image_image)

  have "\<forall>L \<in> set (raw_clause C). -L \<in> lits_of_l M"
  proof (cases W)
    case Nil
    then have "raw_clause C = []"
      using cw(1) cw_eq w_nw(2) by (auto simp: raw_clause_def)
    then show ?thesis
      by simp
  next
    case (Cons La W') note W' = this(1)
    show ?thesis
    proof
      fix L
      assume l: "L \<in> set (raw_clause C)"
      show "-L \<in> lits_of_l M"
      proof (cases "L \<in> set W")
        case True
        thus ?thesis
          using cw(2) cw_eq by fastforce
      next
        case False
        thus ?thesis
          using W' cw(2) cw_eq l w_nw(3) unfolding M_def raw_clause_def
          by (metis (no_types, lifting) UnE imageE list.set_intros(1)
            lits_of_mmset_of_mlit  rev_subsetD set_append set_map twl_clause.sel(1)
            twl_clause.sel(2) uminus_of_uminus_id)
      qed
    qed
  qed
  then show "trail S \<Turnstile>as CNot (clause C)"
    unfolding CNot_def true_annots_def clause_def by auto

  show "C \<in> set (twl.raw_clauses S)"
    using cw unfolding twl.raw_clauses_def by auto
qed

lemma wf_candidates_conflict_complete:
  assumes wf: "wf_twl_state S" and
    c_mem: "C \<in> set (twl.raw_clauses S)" and
    unsat: "trail S \<Turnstile>as CNot (clause C)"
  shows "C \<in> candidates_conflict S"
proof -
  def M \<equiv> "raw_trail S"
  def N \<equiv> "twl.init_clss S"
  def U \<equiv> "twl.learned_clss S"

  note MNU_defs [simp] = M_def N_def U_def

  obtain W UW where cw_eq: "C = TWL_Clause W UW"
    by (cases C, blast)

  have wf_c: "wf_twl_cls M C"
    using wf c_mem unfolding wf_twl_state_def by simp

  have w_nw:
    "distinct W"
    "length W < 2 \<Longrightarrow> set UW \<subseteq> set W"
    "\<And>L L'. L \<in> set W \<Longrightarrow> -L \<in> lits_of_l M \<Longrightarrow> L' \<in> set UW \<Longrightarrow> L' \<notin> set W \<Longrightarrow> -L' \<in> lits_of_l M"
   using wf_c unfolding cw_eq by (auto simp: image_image)

  have "\<And>L. L \<in> set (raw_clause C) \<Longrightarrow> -L \<in> lits_of_l M"
    unfolding M_def using unsat[unfolded CNot_def true_annots_def, simplified]
    by (auto simp: clause_def)
  then have "set (raw_clause C) \<subseteq> uminus ` lits_of_l M"
    by (metis imageI subsetI uminus_of_uminus_id)
  then have "set W \<subseteq> uminus ` lits_of_l M"
    using cw_eq by (auto simp: raw_clause_def)
  then have subset: "set W \<subseteq> uminus ` lits_of_l M"
    by (simp add: w_nw(1))

  have "W = watched C"
    using cw_eq twl_clause.sel(1) by simp
  then show ?thesis
    using MNU_defs c_mem subset candidates_conflict_def by blast
qed

typedef 'v wf_twl = "{S::'v twl_state. wf_twl_state S}"
morphisms rough_state_of_twl twl_of_rough_state
proof -
  have "TWL_State ([]::('v, 'v twl_clause) ann_lits)
    [] [] 0 None \<in> {S:: 'v twl_state. wf_twl_state S} "
    by (auto simp: wf_twl_state_def twl.raw_clauses_def)
  then show ?thesis by auto
qed

lemma [code abstype]:
  "twl_of_rough_state (rough_state_of_twl S) = S"
  by (fact CDCL_Two_Watched_Literals.wf_twl.rough_state_of_twl_inverse)

lemma wf_twl_state_rough_state_of_twl[simp]: "wf_twl_state (rough_state_of_twl S)"
  using rough_state_of_twl by auto

abbreviation candidates_conflict_twl :: "'v wf_twl \<Rightarrow> 'v twl_clause set" where
"candidates_conflict_twl S \<equiv> candidates_conflict (rough_state_of_twl S)"

abbreviation candidates_propagate_twl :: "'v wf_twl \<Rightarrow> ('v literal \<times> 'v twl_clause) set" where
"candidates_propagate_twl S \<equiv> candidates_propagate (rough_state_of_twl S)"

abbreviation raw_trail_twl :: "'a wf_twl \<Rightarrow> ('a, 'a twl_clause) ann_lits" where
"raw_trail_twl S \<equiv> raw_trail (rough_state_of_twl S)"

abbreviation trail_twl :: "'a wf_twl \<Rightarrow> ('a, 'a literal multiset) ann_lits" where
"trail_twl S \<equiv> trail (rough_state_of_twl S)"

abbreviation raw_clauses_twl :: "'a wf_twl \<Rightarrow> 'a twl_clause list" where
"raw_clauses_twl S \<equiv> twl.raw_clauses (rough_state_of_twl S)"

abbreviation raw_init_clss_twl :: "'a wf_twl \<Rightarrow> 'a twl_clause list" where
"raw_init_clss_twl S \<equiv> raw_init_clss (rough_state_of_twl S)"

abbreviation raw_learned_clss_twl :: "'a wf_twl \<Rightarrow> 'a twl_clause list" where
"raw_learned_clss_twl S \<equiv> raw_learned_clss (rough_state_of_twl S)"

abbreviation backtrack_lvl_twl where
"backtrack_lvl_twl S \<equiv> backtrack_lvl (rough_state_of_twl S)"

abbreviation raw_conflicting_twl where
"raw_conflicting_twl S \<equiv> raw_conflicting (rough_state_of_twl S)"

lemma wf_candidates_twl_conflict_complete:
  assumes
    c_mem: "C \<in> set (raw_clauses_twl S)" and
    unsat: "trail_twl S \<Turnstile>as CNot (clause C)"
  shows "C \<in> candidates_conflict_twl S"
  using c_mem unsat wf_candidates_conflict_complete wf_twl_state_rough_state_of_twl by blast

abbreviation update_backtrack_lvl where
  "update_backtrack_lvl k S \<equiv>
   TWL_State (raw_trail S) (raw_init_clss S) (raw_learned_clss S) k (raw_conflicting S)"

abbreviation update_conflicting where
  "update_conflicting C S \<equiv>
    TWL_State (raw_trail S) (raw_init_clss S) (raw_learned_clss S) (backtrack_lvl S) C"

subsubsection \<open>Abstract 2-WL\<close>

definition tl_trail where
  "tl_trail S =
   TWL_State (tl (raw_trail S)) (raw_init_clss S) (raw_learned_clss S) (backtrack_lvl S)
   (raw_conflicting S)"

locale abstract_twl =
  fixes
    watch :: "'v twl_state \<Rightarrow> 'v literal list \<Rightarrow> 'v twl_clause" and
    rewatch :: "'v literal \<Rightarrow> 'v twl_state \<Rightarrow>
      'v twl_clause \<Rightarrow> 'v twl_clause" and
    restart_learned :: "'v twl_state \<Rightarrow> 'v twl_clause list"
  assumes
    clause_watch: "no_dup (raw_trail S) \<Longrightarrow> clause (watch S C) = mset C" and
    wf_watch: "no_dup (raw_trail S) \<Longrightarrow> wf_twl_cls (raw_trail S) (watch S C)" and
    clause_rewatch: "clause (rewatch L' S C') = clause C'" and
    wf_rewatch:
      "no_dup (raw_trail S) \<Longrightarrow> undefined_lit (raw_trail S) (lit_of L) \<Longrightarrow>
        wf_twl_cls (raw_trail S) C' \<Longrightarrow>
        wf_twl_cls (L # raw_trail S) (rewatch (lit_of L) S C')"
      and
    restart_learned: "mset (restart_learned S) \<subseteq># mset (raw_learned_clss S)" -- \<open>We need
      @{term mset} and not @{term set} to take care of duplicates. \<close>
begin

definition
  cons_trail :: "('v, 'v twl_clause) ann_lit \<Rightarrow> 'v twl_state \<Rightarrow> 'v twl_state"
where
  "cons_trail L S =
   TWL_State (L # raw_trail S) (map (rewatch (lit_of L) S) (raw_init_clss S))
     (map (rewatch (lit_of L) S) (raw_learned_clss S)) (backtrack_lvl S) (raw_conflicting S)"

definition
  add_init_cls :: "'v literal list \<Rightarrow> 'v twl_state \<Rightarrow> 'v twl_state"
where
  "add_init_cls C S =
   TWL_State (raw_trail S) (watch S C # raw_init_clss S) (raw_learned_clss S) (backtrack_lvl S)
     (raw_conflicting S)"

definition
  add_learned_cls :: "'v literal list \<Rightarrow> 'v twl_state \<Rightarrow> 'v twl_state"
where
  "add_learned_cls C S =
   TWL_State (raw_trail S) (raw_init_clss S) (watch S C # raw_learned_clss S) (backtrack_lvl S)
     (raw_conflicting S)"

definition
  remove_cls :: "'v literal list \<Rightarrow> 'v twl_state \<Rightarrow> 'v twl_state"
where
  "remove_cls C S =
   TWL_State (raw_trail S)
     (removeAll_cond (\<lambda>D. clause D = mset C) (raw_init_clss S))
     (removeAll_cond (\<lambda>D. clause D = mset C) (raw_learned_clss S))
     (backtrack_lvl S)
     (raw_conflicting S)"

definition init_state :: "'v literal list list \<Rightarrow> 'v twl_state" where
  "init_state N = fold add_init_cls N (TWL_State [] [] [] 0 None)"

lemma unchanged_fold_add_init_cls:
  "raw_trail (fold add_init_cls Cs (TWL_State M N U k C)) = M"
  "raw_learned_clss (fold add_init_cls Cs (TWL_State M N U k C)) = U"
  "backtrack_lvl (fold add_init_cls Cs (TWL_State M N U k C)) = k"
  "raw_conflicting (fold add_init_cls Cs (TWL_State M N U k C)) = C"
  by (induct Cs arbitrary: N) (auto simp: add_init_cls_def)

lemma unchanged_init_state[simp]:
  "raw_trail (init_state N) = []"
  "raw_learned_clss (init_state N) = []"
  "backtrack_lvl (init_state N) = 0"
  "raw_conflicting (init_state N) = None"
  unfolding init_state_def by (rule unchanged_fold_add_init_cls)+

lemma clauses_init_fold_add_init:
  "no_dup M \<Longrightarrow>
   twl.init_clss (fold add_init_cls Cs (TWL_State M N U k C)) =
   clauses_of_l Cs + raw_clss_l N"
  by (induct Cs arbitrary: N) (auto simp: add_init_cls_def clause_watch comp_def ac_simps
    clause_def[symmetric])

lemma init_clss_init_state[simp]: "twl.init_clss (init_state N) = clauses_of_l N"
  unfolding init_state_def by (subst clauses_init_fold_add_init) simp_all

definition restart' where
  "restart' S = TWL_State [] (raw_init_clss S) (restart_learned S) 0 None"

end

subsubsection \<open>Instanciation of the previous locale\<close>

definition watch_nat :: "'v twl_state \<Rightarrow> 'v literal list \<Rightarrow> 'v twl_clause" where
  "watch_nat S C =
   (let
      C' = remdups C;
      neg_not_assigned = filter (\<lambda>L. -L \<notin> lits_of_l (raw_trail S)) C';
      neg_assigned_sorted_by_trail = filter (\<lambda>L. L \<in> set C) (map (\<lambda>L. -lit_of L) (raw_trail S));
      W = take 2 (neg_not_assigned @ neg_assigned_sorted_by_trail);
      UW = foldr remove1 W C
    in TWL_Clause W UW)"

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
  assumes n_d: "no_dup M" and H: "[L\<leftarrow>map (\<lambda>L. - lit_of L) M. L \<in> set C] = l"
  shows "distinct l"
  unfolding H[symmetric]
  apply (rule distinct_filter)
  using n_d by (induction M) auto

lemma watch_nat_lists_disjointD:
  assumes
    l: "[L\<leftarrow>remdups C. - L \<notin> lits_of_l (raw_trail S)] = l" and
    l': "[L\<leftarrow>map (\<lambda>L. - lit_of L) (raw_trail S) . L \<in> set C] = l'"
  shows "\<forall>x \<in> set l. \<forall>y \<in> set l'. x \<noteq> y"
  by (auto simp: l[symmetric] l'[symmetric] lits_of_def image_image)

lemma watch_nat_list_cases_witness[consumes 2, case_names Nil_Nil Nil_single Nil_other
  single_Nil single_other other]:
  fixes
    C :: "'v literal list" and
    S :: "'v twl_state"
  defines
    "xs \<equiv> [L\<leftarrow>remdups C. - L \<notin> lits_of_l (raw_trail S)]" and
    "ys \<equiv> [L\<leftarrow>map (\<lambda>L. - lit_of L) (raw_trail S) . L \<in> set C]"
  assumes
    n_d: "no_dup (raw_trail S)" and
    Nil_Nil: "xs = [] \<Longrightarrow> ys = [] \<Longrightarrow> P" and
    Nil_single:
      "\<And>a. xs = [] \<Longrightarrow> ys = [a] \<Longrightarrow> a \<in> set C \<Longrightarrow> P" and
    Nil_other: "\<And>a b ys'. xs = [] \<Longrightarrow> ys = a # b # ys' \<Longrightarrow> a \<noteq> b \<Longrightarrow> P" and
    single_Nil: "\<And>a. xs = [a] \<Longrightarrow> ys = [] \<Longrightarrow> P" and
    single_other: "\<And>a b ys'. xs = [a] \<Longrightarrow> ys = b # ys' \<Longrightarrow> a \<noteq> b \<Longrightarrow> P" and
    other: "\<And>a b xs'. xs = a # b # xs' \<Longrightarrow> a \<noteq> b \<Longrightarrow> P"
  shows P
proof -
  note xs_def[simp] and ys_def[simp]
  have dist: "\<And>P. distinct [L\<leftarrow>remdups C . P L]"
    by auto
  then have H: "\<And>a b P xs. [L\<leftarrow>remdups C . P L] = a # b # xs \<Longrightarrow> a \<noteq> b"
    by (metis distinct_length_2_or_more)
  show ?thesis
  apply (cases "[L\<leftarrow>remdups C. - L \<notin> lits_of_l (raw_trail S)]"
        rule: list_cases2;
      cases "[L\<leftarrow>map (\<lambda>L. - lit_of L) (raw_trail S) . L \<in> set C]" rule: list_cases2)
          using Nil_Nil apply simp
         using Nil_single apply (force dest: filter_in_list_prop_verifiedD)
        using Nil_other no_dup_filter_diff[OF n_d, of C]
        apply fastforce
       using single_Nil apply simp
      using single_other xs_def ys_def apply (metis list.set_intros(1) watch_nat_lists_disjointD)
     using single_other unfolding xs_def ys_def apply (metis list.set_intros(1)
       watch_nat_lists_disjointD)
    using other xs_def ys_def by (metis H)+
qed

lemma watch_nat_list_cases [consumes 1, case_names Nil_Nil Nil_single Nil_other single_Nil
  single_other other]:
  fixes
    C :: "'v literal list" and
    S :: "'v twl_state"
  defines
    "xs \<equiv> [L\<leftarrow>remdups C . - L \<notin> lits_of_l (raw_trail S)]" and
    "ys \<equiv> [L\<leftarrow>map (\<lambda>L. - lit_of L) (raw_trail S) . L \<in> set C]"
  assumes
    n_d: "no_dup (raw_trail S)" and
    Nil_Nil: "xs = [] \<Longrightarrow> ys = [] \<Longrightarrow> P" and
    Nil_single:
      "\<And>a. xs = [] \<Longrightarrow> ys = [a] \<Longrightarrow>  a \<in> set C \<Longrightarrow> P" and
    Nil_other: "\<And>a b ys'. xs = [] \<Longrightarrow> ys = a # b # ys' \<Longrightarrow> a \<noteq> b \<Longrightarrow> P" and
    single_Nil: "\<And>a. xs = [a] \<Longrightarrow> ys = [] \<Longrightarrow> P" and
    single_other: "\<And>a b ys'. xs = [a] \<Longrightarrow> ys = b # ys' \<Longrightarrow> a \<noteq> b \<Longrightarrow> P" and
    other: "\<And>a b xs'. xs = a # b # xs' \<Longrightarrow> a \<noteq> b \<Longrightarrow> P"
  shows P
  using watch_nat_list_cases_witness[OF n_d, of C P]
  Nil_Nil Nil_single Nil_other single_Nil single_other other
  unfolding xs_def[symmetric] ys_def[symmetric] by auto

lemma watch_nat_lists_set_union_witness:
  fixes
    C ::  "'v literal list" and
    S :: "'v twl_state"
  defines
    "xs \<equiv> [L\<leftarrow>remdups C. - L \<notin> lits_of_l (raw_trail S)]" and
    "ys \<equiv> [L\<leftarrow>map (\<lambda>L. - lit_of L) (raw_trail S) . L \<in> set C]"
  assumes n_d: "no_dup (raw_trail S)"
  shows "set C = set xs \<union> set ys"
  using n_d unfolding xs_def ys_def by (auto simp: lits_of_def comp_def uminus_lit_swap)

lemma mset_intersection_inclusion: "A + (B - A) = B \<longleftrightarrow> A \<subseteq># B"
  apply (rule iffI)
   apply (metis mset_le_add_left)
  by (auto simp: ac_simps multiset_eq_iff subseteq_mset_def)

lemma clause_watch_nat:
  assumes "no_dup (raw_trail S)"
  shows "clause (watch_nat S C) = mset C"
  using assms
  apply (cases rule: watch_nat_list_cases[OF assms(1), of C])
  by (auto dest: filter_in_list_prop_verifiedD simp: watch_nat_def multiset_eq_iff raw_clause_def
    clause_def)

lemma index_uminus_index_map_uminus:
  "-a \<in> set L \<Longrightarrow> index L (-a) = index (map uminus L) (a::'a literal)"
  by (induction L) auto

lemma index_filter:
  "a \<in> set L \<Longrightarrow> b \<in> set L \<Longrightarrow> P a \<Longrightarrow> P b \<Longrightarrow>
   index L a \<le> index L b \<longleftrightarrow> index (filter P L) a \<le> index (filter P L) b"
  by (induction L) auto

lemma foldr_remove1_W_Nil[simp]: "foldr remove1 W [] = []"
  by (induct W) auto

lemma image_lit_of_mmset_of_mlit[simp]:
  "lit_of ` mmset_of_mlit ` A = lit_of ` A"
  unfolding comp_def
  using [[simp_trace]]by (simp add: image_image comp_def)

lemma distinct_filter_eq:
  assumes "distinct xs"
  shows "[L\<leftarrow> xs. L = a] = (if a \<in> set xs then [a] else [])"
  using assms by (induction xs) auto

lemma no_dup_distinct_map_uminus_lit_of:
  "no_dup xs \<Longrightarrow> distinct (map (\<lambda>L. - lit_of L) xs)"
  by (induction xs) auto

lemma wf_watch_witness:
   fixes C :: "'v literal list" and
     S :: "'v twl_state"
   defines
     ass: "neg_not_assigned \<equiv> filter (\<lambda>L. -L \<notin> lits_of_l (raw_trail S)) (remdups C)" and
     tr: "neg_assigned_sorted_by_trail \<equiv> filter (\<lambda>L. L \<in> set C) (map (\<lambda>L. -lit_of L) (raw_trail S))"
   defines
      W: "W \<equiv> take 2 (neg_not_assigned @ neg_assigned_sorted_by_trail)"
  assumes
    n_d[simp]: "no_dup (raw_trail S)"
  shows "wf_twl_cls (raw_trail S) (TWL_Clause W (foldr remove1 W C))"
  unfolding wf_twl_cls.simps struct_wf_twl_cls.simps
proof (intro conjI, goal_cases)
  case 1
  then show ?case using n_d W unfolding ass tr
    apply (cases rule: watch_nat_list_cases_witness[of S C, OF n_d])
    by (auto simp: distinct_mset_add_single)
next
  case 2
  then show ?case unfolding W by simp
next
  case 3
  show ?case using n_d
    proof (cases rule: watch_nat_list_cases_witness[of S C])
      case Nil_Nil
      then have "set C = set [] \<union> set []"
        using watch_nat_lists_set_union_witness n_d by metis
      then show ?thesis
        by simp
    next
      case (Nil_single a)
      moreover have "\<And>x. set C = {a} \<Longrightarrow> - a \<in> lits_of_l (trail S) \<Longrightarrow> x \<in> set (remove1 a C) \<Longrightarrow>
        x = a"
        using notin_set_remove1 by auto
      ultimately show ?thesis
        using watch_nat_lists_set_union_witness[of S C] 3 by (auto simp: W ass tr comp_def)
    next
      case Nil_other
      then show ?thesis
       using 3 by (auto simp: W ass tr)
    next
      case (single_Nil a)
      show ?thesis
        using watch_nat_lists_set_union_witness[of S C] 3
        by (fastforce simp add: W ass tr single_Nil comp_def distinct_filter_eq
          no_dup_distinct_map_uminus_lit_of min_def)
    next
      case single_other
      then show ?thesis
        using 3 by (auto simp: W ass tr)
    next
      case other
      then show ?thesis
        using 3 by (auto simp: W ass tr)
    qed
next
  case 4 note _[simp] = this
  show ?case
    using n_d apply (cases rule: watch_nat_list_cases_witness[of S C])
      apply (auto dest: filter_in_list_prop_verifiedD
        simp: W ass tr lits_of_def  filter_empty_conv)[4]
    using watch_nat_lists_set_union_witness[of S C]
    by (force dest: filter_in_list_prop_verifiedD simp: W ass tr lits_of_def)+
next
  case 5
  from n_d show ?case
    proof (cases rule: watch_nat_list_cases_witness[of S C])
      case Nil_Nil
      then show ?thesis by (auto simp:  W ass tr)
    next
      case Nil_single
      then show ?thesis
        using watch_nat_lists_set_union_witness[of S C] tr by (fastforce simp: W ass)
    next
      case Nil_other
      then show ?thesis
        unfolding watched_only_lazy_updates.simps Ball_def
        apply (intro allI impI)
        apply (subst index_uminus_index_map_uminus,
          simp add: index_uminus_index_map_uminus lits_of_def o_def)
        apply (subst index_uminus_index_map_uminus,
          simp add: index_uminus_index_map_uminus lits_of_def o_def)

        apply (subst index_filter[of _ _ _ "\<lambda>L. L \<in> set C"])
        by (auto dest: filter_in_list_prop_verifiedD
          simp: uminus_lit_swap lits_of_def o_def W ass tr dest: in_diffD)
    next
      case single_Nil
      then show ?thesis
         using watch_nat_lists_set_union_witness[of S C] tr by (fastforce simp: W ass)
    next
      case single_other
      then show ?thesis
        unfolding watched_only_lazy_updates.simps Ball_def
        apply (clarify)
        apply (subst index_uminus_index_map_uminus,
          simp add: index_uminus_index_map_uminus lits_of_def image_image o_def)
        apply (subst index_uminus_index_map_uminus,
          simp add: index_uminus_index_map_uminus lits_of_def o_def)

        apply (subst index_filter[of _ _ _ "\<lambda>L. L \<in> set C"])
        by (auto dest: filter_in_list_prop_verifiedD
          simp: W ass tr uminus_lit_swap lits_of_def o_def dest: in_diffD)
    next
      case other
      then show ?thesis
        unfolding watched_only_lazy_updates.simps
        apply clarify
        apply (subst index_uminus_index_map_uminus,
          simp add: index_uminus_index_map_uminus lits_of_def o_def)[1]
        apply (subst index_uminus_index_map_uminus,
          simp add: index_uminus_index_map_uminus lits_of_def o_def)[1]

        apply (subst index_filter[of _ _ _ "\<lambda>L. L \<in> set C"])
        by (auto dest: filter_in_list_prop_verifiedD
          simp: index_uminus_index_map_uminus lits_of_def o_def uminus_lit_swap
           W ass tr)
    qed
qed

lemma wf_watch_nat: "no_dup (raw_trail S) \<Longrightarrow> wf_twl_cls (raw_trail S) (watch_nat S C)"
  using wf_watch_witness[of S C] watch_nat_def by metis

definition
  rewatch_nat ::
  "'v literal \<Rightarrow> 'v twl_state \<Rightarrow> 'v twl_clause \<Rightarrow> 'v twl_clause"
where
  "rewatch_nat L S C =
   (if - L \<in> set (watched C) then
      case filter (\<lambda>L'. L' \<notin> set (watched C) \<and> - L' \<notin> insert L (lits_of_l (trail S)))
         (unwatched C) of
        [] \<Rightarrow> C
      | L' # _ \<Rightarrow>
        TWL_Clause (L' # remove1 (-L) (watched C)) (-L # remove1 L' (unwatched C))
    else
      C)"

lemma clause_rewatch_nat:
  fixes UW :: "'v literal list" and
    S :: "'v twl_state" and
    L :: "'v literal" and C :: "'v twl_clause"
  shows "clause (rewatch_nat L S C) = clause C"
  using List.set_remove1_subset[of "-L" "watched C"]
  apply (cases C)
  by (auto simp: raw_clause_def rewatch_nat_def ac_simps multiset_eq_iff clause_def
    split: list.split
    dest: filter_in_list_prop_verifiedD)

lemma filter_sorted_list_of_multiset_Nil:
  "[x \<leftarrow> sorted_list_of_multiset M. p x] = [] \<longleftrightarrow> (\<forall>x \<in># M. \<not> p x)"
  by auto (metis empty_iff filter_set list.set(1) member_filter set_sorted_list_of_multiset)

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
proof -
  have "size W = 0 \<or> size W = 1 \<or> size W  = 2"
    using assms by linarith
  then show ?thesis
    using assms by (fastforce elim!: size_mset_SucE simp: Num.numeral_2_eq_2)
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

lemma clause_rewatch_witness':
  assumes
    wf: "wf_twl_cls (raw_trail S) C" and
    undef: "undefined_lit (raw_trail S) (lit_of L)"
  shows "wf_twl_cls (L # raw_trail S) (rewatch_nat (lit_of L) S C)"
proof (cases "- lit_of L \<in> set (watched C)")
  case False
  then show ?thesis
    apply (cases C)
    using wf undef unfolding rewatch_nat_def
    by (auto simp: uminus_lit_swap Decided_Propagated_in_iff_in_lits_of_l comp_def)
next
  case falsified: True

  let ?unwatched_nonfalsified =
    "[L'\<leftarrow> unwatched C. L' \<notin> set (watched C) \<and> - L' \<notin> insert (lit_of L) (lits_of_l (trail S))]"
  obtain W UW where C: "C = TWL_Clause W UW"
    by (cases C)

  show ?thesis
  proof (cases ?unwatched_nonfalsified)
    case Nil
    show ?thesis
      using falsified Nil
      apply (simp only: wf_twl_cls.simps if_True list.cases C rewatch_nat_def
        struct_wf_twl_cls.simps)
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
        have "\<And>p l. filter p (unwatched C) \<noteq> [] \<or> l \<notin> set UW \<or> \<not> p l"
          unfolding C by (metis (no_types) filter_empty_conv twl_clause.sel(2))
        then show ?case
          using 4(2) C by auto
      next
        case 5
        then show ?case
          using wf by (fastforce simp add: C comp_def uminus_lit_swap)
      qed
  next
    case (Cons L' Ls)
    show ?thesis
      unfolding rewatch_nat_def
      using falsified Cons
      apply (simp only: wf_twl_cls.simps if_True list.cases C struct_wf_twl_cls.simps)
      apply (intro conjI)
      proof goal_cases
        case 1
        have "distinct (watched (TWL_Clause W UW))"
          using wf unfolding C by auto
        moreover have "L' \<notin> set (remove1 (-lit_of L) (watched (TWL_Clause W UW)))"
          using "1"(2) not_gr0 by (fastforce dest: filter_in_list_prop_verifiedD in_diffD)
        ultimately show ?case
          by (auto simp: distinct_mset_single_add)
      next
        case 2
        have f2: "[l\<leftarrow>unwatched (TWL_Clause W UW) . l \<notin> set (watched (TWL_Clause W UW))
          \<and> - l \<notin> insert (lit_of L) (lits_of_l (trail S))] \<noteq> []"
          using "2"(2) by simp
        then have "\<not> set UW \<subseteq> set W"
           using 2 by (auto simp add: filter_empty_conv)
        then show ?case
          using wf C "2"(1) by (auto simp: length_remove1)
      next
        case 3
        have W: "length W \<le> Suc 0 \<longleftrightarrow> length W = 0 \<or> length W = Suc 0"
          by linarith
        show ?case
          using wf C 3 by (auto simp: length_remove1 W length_list_Suc_0 dest!: subset_singletonD)
      next
        case 4
        have H: "\<forall>L\<in> set W. - L \<in> lits_of_l (trail S) \<longrightarrow>
          (\<forall>L'\<in> set UW. L' \<notin> set W \<longrightarrow> - L' \<in> lits_of_l (trail S))"
          using wf by (auto simp: C)
        have W: "length W \<le> 2" and W_UW: "length W < 2 \<longrightarrow> set UW \<subseteq> set W"
          using wf by (auto simp: C)
        have distinct: "distinct W"
          using wf by (auto simp: C)
        show ?case
          using 4
          unfolding C watched_only_lazy_updates.simps Ball_def twl_clause.sel
            watched_wf_twl_cls.simps
          apply (intro allI impI)
          apply (rename_tac xW xUW)
          apply (case_tac "- lit_of L = xW"; case_tac "xW = xUW"; case_tac "L' = xW")
                  apply (auto simp: uminus_lit_swap)[2]
                apply (force dest: filter_in_list_prop_verifiedD)
               using H distinct apply (fastforce)
             using distinct apply (fastforce)
            using distinct apply (fastforce)
           apply (force dest: filter_in_list_prop_verifiedD)
          using H by (auto simp: uminus_lit_swap)
      next
        case 5
        have H: "\<forall>x. x \<in> set W \<longrightarrow> - x \<in> lits_of_l (trail S) \<longrightarrow> (\<forall>x. x \<in> set UW \<longrightarrow> x \<notin> set W
          \<longrightarrow> - x \<in> lits_of_l (trail S))"
          using wf by (auto simp: C)
        show ?case
          unfolding C watched_only_lazy_updates.simps Ball_def
          proof (intro allI impI conjI, goal_cases)
            case (1 xW x)
            show ?case
              proof (cases "- lit_of L = xW")
                case True
                then show ?thesis
                  by (cases "xW = x") (auto simp: uminus_lit_swap)
              next
                case False note LxW = this
                have f9: "L' \<in> set [l\<leftarrow>unwatched C. l \<notin> set (watched (TWL_Clause W UW))
                    \<and> - l \<notin> lits_of_l (L # raw_trail S)]"
                  using 1(2) 5 C by auto
                moreover then have f11: "- xW \<in> lits_of_l (trail S)"
                  using 1(3) LxW by (auto simp: uminus_lit_swap)
                moreover then have "xW \<notin> set W"
                  using f9 1(2) H by (auto simp: C)
                ultimately have False
                  using 1 by auto
                then show ?thesis
                  by fast
              qed
          qed
      qed
  qed
qed

(* implementation of watch etc. *)

interpretation twl: abstract_twl watch_nat rewatch_nat raw_learned_clss
  apply unfold_locales
  apply (rule clause_watch_nat; simp add: image_image comp_def)
  apply (rule wf_watch_nat; simp add: image_image comp_def)
  apply (rule clause_rewatch_nat)
  apply (rule clause_rewatch_witness'; simp add: image_image comp_def)
  apply (simp)
  done

interpretation twl2: abstract_twl watch_nat rewatch_nat "\<lambda>_. []"
  apply unfold_locales
  apply (rule clause_watch_nat; simp add: image_image comp_def)
  apply (rule wf_watch_nat; simp add: image_image comp_def)
  apply (rule clause_rewatch_nat)
  apply (rule clause_rewatch_witness'; simp add: image_image comp_def)
  apply (simp)
  done

end
