theory Propo_CDCL
imports Partial_Annotated_Clausal_Logic List_More

begin

section \<open>CDCL\<close>
subsection \<open>Auxiliary definitions\<close>
subsubsection \<open>Datatypes and access functions\<close>
datatype 'a conflicting_clause = C_True | C_Clause "'a"

type_synonym 'a cdcl_mark = "'a clause"
type_synonym cdcl_marked_level = "nat"

type_synonym 'a cdcl_marked_lit = "('a, cdcl_marked_level, 'a cdcl_mark) marked_lit"
type_synonym 'a cdcl_annoted_lits = "('a, cdcl_marked_level, 'a cdcl_mark) annoted_lits"
type_synonym 'v cdcl_state = "'v cdcl_annoted_lits \<times> 'v clauses \<times> 'v clauses \<times> nat \<times> 'v clause conflicting_clause"

abbreviation "trail \<equiv> (\<lambda>(M, N, U, k, D). M)"
abbreviation "clauses \<equiv> \<lambda>(M, N, U, k, D). N"
abbreviation "learned_clauses \<equiv> \<lambda>(M, N, U, k, D). U"
abbreviation "conflicting \<equiv> \<lambda>(M, N, U, k, D). D"
abbreviation "backtrack_level \<equiv> \<lambda>(M, N, U, k, D). k"
abbreviation "S0_cdcl (N :: 'a clauses) \<equiv> (([], N, {}, 0, C_True):: 'a cdcl_state)"

lemma trail_conv: "trail (M, N, U, k, D) = M" and
  clauses_conv: "clauses (M, N, U, k, D) = N" and
  learned_clauses_conv: "learned_clauses (M, N, U, k, D) = U" and
  conflicting_conv: "conflicting (M, N, U, k, D) = D" and
  backtrack_level_conv: "backtrack_level (M, N, U, k, D) = k"
  by auto

subsubsection \<open>Level of literals and clauses\<close>
text \<open>Getting the level of a variable, implies that the list has to be reversed. Here is the funtion after reversing.\<close>
fun get_rev_level :: "'v literal \<Rightarrow> cdcl_marked_level \<Rightarrow> ('v, cdcl_marked_level, 'a) annoted_lits \<Rightarrow> cdcl_marked_level" where
"get_rev_level _ _ [] = 0" |
"get_rev_level L n (Marked l level # Ls) = (if atm_of l = atm_of L then level else get_rev_level L level Ls)" |
"get_rev_level L n (Propagated l _ # Ls) =  (if atm_of l = atm_of L then n else get_rev_level L n Ls)"

abbreviation "get_level L M  \<equiv> get_rev_level L 0 (rev M)"

lemma get_rev_level_uminus[simp]: "get_rev_level (-L) n M = get_rev_level L n M"
  apply (induct M arbitrary: n, simp)
  by (case_tac a) auto

lemma atm_of_notin_get_rev_level_eq_0[simp]:
  assumes "atm_of L \<notin> atm_of ` lit_of `set M"
  shows "get_rev_level L n M = 0"
  using assms apply (induct M arbitrary: n, simp)
  by (case_tac a) auto

lemma get_rev_level_ge_0_atm_of_in:
  assumes  "get_rev_level L n M > n"
  shows "atm_of L \<in> atm_of ` lit_of `set M"
  using assms apply (induct M arbitrary: n, simp)
  by (case_tac a) fastforce+

text \<open>In @{const get_rev_level} (resp. @{const get_level}), the beginning (resp. the end) can be skipped if the literal is not in the beginning (resp. the end).\<close>
lemma get_rev_level_skip[simp]:
  assumes  "atm_of L \<notin> atm_of ` lit_of ` set M"
  shows "get_rev_level L n (M @ Marked K i # M') = get_rev_level L i (Marked K i # M')"
  using assms apply (induct M arbitrary: n i, simp)
  by (case_tac a) auto

lemma get_rev_level_notin_end[simp]:
  assumes  "atm_of L \<notin> atm_of ` lit_of ` set M'"
  shows "get_rev_level L n (M @ M') = get_rev_level L n M"
  using assms apply (induct M arbitrary: n, simp)
  by (case_tac a) auto

text \<open>If the literal is at the beginning, then the end can be skipped\<close>
lemma get_rev_level_skip_end[simp]:
  assumes  "atm_of L \<in> atm_of ` lit_of ` set M"
  shows "get_rev_level L n (M @ M') = get_rev_level L n M"
  using assms apply (induct M arbitrary: n, simp)
  by (case_tac a) auto

lemma get_level_skip_beginning:
  assumes "atm_of L' \<noteq> atm_of (lit_of K)"
  shows "get_level L' (K # M) = get_level L' M"
  using assms by auto


abbreviation "MMax M \<equiv> Max (set_mset M)"

text \<open>the @{term "{#0#}"}  is there to ensures that the set is not empty.\<close>
definition get_maximum_level :: "'a literal multiset \<Rightarrow> ('a, nat, 'b) marked_lit list \<Rightarrow> nat"  where
"get_maximum_level D M = MMax ({#0#} + image_mset (\<lambda>L. get_rev_level L 0 (rev M)) D)"

lemma get_maximum_level_ge_get_level:
  "L \<in># D \<Longrightarrow> get_maximum_level D M \<ge> get_level L M"
  unfolding get_maximum_level_def by auto

lemma get_maximum_level_empty[simp]:
  "get_maximum_level {#} M = 0"
  unfolding get_maximum_level_def by auto

lemma get_maximum_level_exists_lit_of_max_level:
  "D \<noteq> {#} \<Longrightarrow> \<exists>L\<in># D. get_level L M = get_maximum_level D M"
  unfolding get_maximum_level_def
  apply (induct D)
   apply simp
  by (case_tac "D = {#}") (auto simp add: max_def)


lemma get_maximum_level_empty_list[simp]:
  "get_maximum_level D [] = 0"
  unfolding get_maximum_level_def by (simp add: image_constant_conv)

lemma get_maximum_level_single[simp]:
  "get_maximum_level {#L#} M = get_level L M"
  unfolding get_maximum_level_def by simp

lemma get_maximum_level_plus:
  "get_maximum_level (D + D') M = max (get_maximum_level D M) (get_maximum_level D' M)"
  by (induct D) (auto simp add: get_maximum_level_def)


lemma get_maximum_level_exists_lit:
  assumes n: "n > 0"
  and max: "get_maximum_level D M = n"
  shows "\<exists>L \<in>#D. get_level L M = n"
proof -
  have f: "finite (insert 0 ((\<lambda>L. get_level L M) ` set_mset D))" by auto
  hence "n \<in> ((\<lambda>L. get_level L M) ` set_mset D)"
    using n max Max_in[OF f] unfolding get_maximum_level_def by auto
  thus "\<exists>L \<in># D. get_level L M = n" by auto
qed

lemma get_maximum_level_skip_first[simp]:
  assumes "atm_of L \<notin> atms_of D"
  shows "get_maximum_level D (Propagated L C # M) = get_maximum_level D M"
  using assms unfolding get_maximum_level_def
  by (metis (lifting) atm_of_lit_in_atms_of get_level_skip_beginning marked_lit.sel(2) mem_set_mset_iff multiset.map_cong0)

lemma get_maximum_level_skip_beginning:
  assumes DH: "atms_of D \<subseteq> atm_of `lits_of H"
  shows "get_maximum_level D (c @ Marked Kh i # H) = get_maximum_level D H"
proof -
  have "(\<lambda>L. get_rev_level L 0 (rev H @ Marked Kh i # rev c)) ` set_mset D
      = (\<lambda>L. get_rev_level L 0 (rev H)) ` set_mset D"
    using DH unfolding lits_of_def atms_of_def by (auto intro!: image_cong)
  thus ?thesis using DH unfolding get_maximum_level_def by auto
qed
lemma get_maximum_level_D_single_propagated:
  "get_maximum_level D [Propagated x21 x22] = 0"
proof -
  have A: "insert 0 ((\<lambda>L. 0) ` (set_mset D \<inter> {L. atm_of x21 = atm_of L})
      \<union> (\<lambda>L. 0) ` (set_mset D \<inter> {L. atm_of x21 \<noteq> atm_of L})) = {0}"
    by auto
  show ?thesis unfolding get_maximum_level_def by (simp add: A)
qed

lemma get_maximum_level_skip_notin:
  assumes D: "\<forall>L\<in>#D. atm_of L \<in> atm_of `lits_of M"
  shows "get_maximum_level D M = get_maximum_level D (Propagated x21 x22 # M)"
proof -
  have A: "(\<lambda>L. get_rev_level L 0 (rev M @ [Propagated x21 x22])) ` set_mset D
      = (\<lambda>L. get_rev_level L 0 (rev M)) ` set_mset D"
    using D by (auto intro!: image_cong simp add:  lits_of_def)
  show ?thesis unfolding get_maximum_level_def by (auto simp add: A)
qed

lemma get_maximum_level_skip_un_marked_not_present:
  assumes "\<forall>L\<in>#D. atm_of L \<in> atm_of ` lits_of aa " and
  "\<forall>m\<in>set M. \<not> is_marked m"
  shows " get_maximum_level D aa = get_maximum_level D (M @ aa)"
  using assms apply (induction M)
   apply simp
  by (case_tac a) (auto intro!: get_maximum_level_skip_notin[of D "_ @ aa"] simp add: image_Un)

fun get_maximum_possible_level :: "'v cdcl_annoted_lits \<Rightarrow> cdcl_marked_level" where
"get_maximum_possible_level [] = 0" |
"get_maximum_possible_level (Marked K i # l) = max i (get_maximum_possible_level l)" |
"get_maximum_possible_level (Propagated _ _ # l) = get_maximum_possible_level l"

lemma get_maximum_possible_level_append[simp]:
  "get_maximum_possible_level (M@M')
    = max (get_maximum_possible_level M) (get_maximum_possible_level M')"
  apply (induct M, simp) by (case_tac a, auto)

lemma get_maximum_possible_level_rev[simp]:
  "get_maximum_possible_level (rev M) = get_maximum_possible_level M"
  apply (induct M, simp) by (case_tac a, auto)

lemma get_maximum_possible_level_ge_get_rev_level:
  "max (get_maximum_possible_level M) i \<ge> get_rev_level L i M"
  apply (induct M arbitrary: i)
    apply simp
  by (case_tac a) (auto simp add: le_max_iff_disj)

lemma get_maximum_possible_level_ge_get_level[simp]:
  "get_maximum_possible_level M \<ge> get_level L M"
  using get_maximum_possible_level_ge_get_rev_level[of _ 0 "rev _"] by auto

lemma get_maximum_possible_level_ge_get_maximum_level[simp]:
  "get_maximum_possible_level M \<ge> get_maximum_level D M"
  using get_maximum_level_exists_lit_of_max_level unfolding Bex_mset_def
  by (metis get_maximum_level_empty get_maximum_possible_level_ge_get_level le0)

fun get_all_mark_of_propagated where
"get_all_mark_of_propagated [] = []" |
"get_all_mark_of_propagated (Marked _ _ # L) = get_all_mark_of_propagated L" |
"get_all_mark_of_propagated (Propagated _ mark # L) = mark # get_all_mark_of_propagated L"

lemma get_all_mark_of_propagated_append[simp]:  "get_all_mark_of_propagated (A @ B) = get_all_mark_of_propagated A @ get_all_mark_of_propagated B"
  apply (induct A, simp)
  by (case_tac a) auto

subsection \<open>CDCL Rules\<close>
text \<open>Because of the strategy we will later use, we distinguish propagate, conflict from the other rules\<close>
inductive propagate :: "'v cdcl_state \<Rightarrow> 'v cdcl_state \<Rightarrow> bool" where
propagate_rule[intro]: "S = (M, N, U, k, C_True) \<Longrightarrow>  C + {#L#} \<in> N \<union> U \<Longrightarrow> M \<Turnstile>as CNot C \<Longrightarrow> undefined_lit L (trail S) \<Longrightarrow> propagate S (Propagated L (C + {#L#}) # M, N, U, k, C_True)"
  
inductive_cases propagateE[elim]: "propagate S T"

inductive conflict ::  "'v cdcl_state \<Rightarrow> 'v cdcl_state \<Rightarrow> bool" where
conflict_rule: "S = (M, N, U, k, C_True) \<Longrightarrow> D \<in> N \<union> U \<Longrightarrow> M \<Turnstile>as CNot D \<Longrightarrow> conflict S (M, N, U, k, C_Clause D)"

inductive_cases conflictE[elim]: "conflict S S'"

inductive backtrack ::  "'v cdcl_state \<Rightarrow> 'v cdcl_state \<Rightarrow> bool" where
backtracking[intro]: "S = (M, N, U, k, C_Clause (D + {#L#})) \<Longrightarrow> (Marked K (i+1) # M1, M2) \<in> set (get_all_marked_decomposition M) \<Longrightarrow> get_level L M = k \<Longrightarrow> get_level L M = get_maximum_level (D+{#L#}) M \<Longrightarrow> get_maximum_level D M = i \<Longrightarrow> backtrack S (Propagated L (D+{#L#}) # M1 , N, U \<union> {D + {#L#}}, i, C_True)"
inductive_cases backtrackE: "backtrack S S'"

inductive decided ::  "'v cdcl_state \<Rightarrow> 'v cdcl_state \<Rightarrow> bool" where
deciding[intro]: "S = (M, N, U, k, C_True) \<Longrightarrow> undefined_lit L M \<Longrightarrow> atm_of L \<in> atms_of_m N \<Longrightarrow> decided S (Marked L (k+1) # M, N, U, k + 1, C_True)"

inductive_cases decidedE: "decided S S'"

inductive skip :: "'v cdcl_state \<Rightarrow> 'v cdcl_state \<Rightarrow> bool" where
skipping[intro]: "S = (Propagated L C' # M, N, U, k, C_Clause D) \<Longrightarrow>  -L \<notin># D \<Longrightarrow> D \<noteq> {#} \<Longrightarrow> skip S (M, N, U, k, C_Clause D)"

inductive_cases skipE: "skip S S'"

inductive resolve :: "'v cdcl_state \<Rightarrow> 'v cdcl_state \<Rightarrow> bool" where
resolving[intro]: "S = (Propagated L (C + {#L#}) # M, N, U, k, C_Clause (D + {#-L#})) \<Longrightarrow> (get_maximum_level D (Propagated L (C + {#L#}) # M) = k \<or> k= 0) \<Longrightarrow> resolve S (M, N, U, k, C_Clause (remdups_mset (D + C)))"

inductive_cases resolveE: "resolve S S'"

inductive cdcl_rf :: "'v cdcl_state \<Rightarrow> 'v cdcl_state \<Rightarrow> bool" where
restart: "S = (M, N, U, k, C_True) \<Longrightarrow> \<not>M \<Turnstile>as N \<Longrightarrow> cdcl_rf S ([], N, U, 0, C_True)" |
forget: "S = (M, N, U \<union> {C}, k, C_True) \<Longrightarrow> \<not>M \<Turnstile>as N \<Longrightarrow> cdcl_rf S ([], N, U, 0, C_True)"

inductive cdcl_o:: "'v cdcl_state \<Rightarrow> 'v cdcl_state \<Rightarrow> bool" where
decided[intro]: "decided S S' \<Longrightarrow> cdcl_o S S'" |
skip[intro]: "skip S S' \<Longrightarrow> cdcl_o S S'" |
resolve[intro]: "resolve S S' \<Longrightarrow> cdcl_o S S'" |
backtrack[intro]: "backtrack S S' \<Longrightarrow> cdcl_o S S'"

inductive_cases btE: "backtrack S S'"

inductive cdcl :: "'v cdcl_state \<Rightarrow> 'v cdcl_state \<Rightarrow> bool" where
propagate: "propagate S S' \<Longrightarrow> cdcl S S'" |
conflict: "conflict S S' \<Longrightarrow> cdcl S S'" |
other: "cdcl_o S S' \<Longrightarrow> cdcl S S'"|
rf: "cdcl_rf S S' \<Longrightarrow> cdcl S S'"

lemma rtranclp_propagate_is_rtranclp_cdcl:
  "propagate\<^sup>*\<^sup>* S S' \<Longrightarrow> cdcl\<^sup>*\<^sup>* S S'"
  by (induction rule: rtranclp.induct) (fastforce dest!: propagate)+

lemma cdcl_all_induct[consumes 1, case_names propagate conflict forget restart decided skip resolve backtrack]:
  fixes S  :: "'v cdcl_state"
  assumes cdcl: "cdcl S S'"
  and propagate: "\<And>M N U k C L. C + {#L#} \<in> N \<union> U \<Longrightarrow> M \<Turnstile>as CNot C \<Longrightarrow> undefined_lit L M
    \<Longrightarrow> P (M, N, U, k, C_True) (Propagated L (C + {#L#}) # M, N, U, k, C_True)"
  and conflict: "\<And>M N U k D. D \<in> N \<union> U \<Longrightarrow> M \<Turnstile>as CNot D
    \<Longrightarrow> P (M, N, U, k, C_True) (M, N, U, k, C_Clause D)"
  and forget: "\<And>M N U C k. \<not>M \<Turnstile>as N \<Longrightarrow> P (M, N, U \<union> {C}, k, C_True) ([], N, U, 0, C_True)"
  and restart: "\<And>M N U k. \<not>M \<Turnstile>as N \<Longrightarrow> P (M, N, U, k, C_True) ([], N, U, 0, C_True)"
  and decide: "\<And>M N U k L.  undefined_lit L M \<Longrightarrow> atm_of L \<in> atms_of_m N
    \<Longrightarrow> P (M, N, U, k, C_True)  (Marked L (k+1) # M, N, U, k + 1, C_True)"
  and skip: "\<And>M N L C' D k U. -L \<notin># D \<Longrightarrow> D \<noteq> {#}
    \<Longrightarrow> P (Propagated L C' # M, N, U, k, C_Clause D) (M, N, U, k, C_Clause D)"
  and resolve: "\<And>M N L D k U C. (get_maximum_level D (Propagated L (C + {#L#}) # M) = k \<or> k= 0)
    \<Longrightarrow> P (Propagated L (C + {#L#}) # M, N, U, k, C_Clause (D + {#-L#}))
      (M, N, U, k, C_Clause (remdups_mset (D + C)))"
  and backtrack: "\<And>M N U k D L K i M1 M2.
    (Marked K (i+1) # M1, M2) \<in> set (get_all_marked_decomposition M) \<Longrightarrow> get_level L M = k
    \<Longrightarrow> get_level L M = get_maximum_level (D+{#L#}) M \<Longrightarrow> get_maximum_level D M = i
    \<Longrightarrow> P (M, N, U, k, C_Clause (D + {#L#}))
      (Propagated L (D+{#L#}) # M1, N, U \<union> {D +  {#L#}}, i, C_True)"
  shows "P S S'"
  using cdcl
proof (induct rule: cdcl.induct)
  case (propagate S S') note propagate = this(1)
  thus ?case using assms(2) by (auto)
next
  case (conflict S S')
  thus ?case using assms(3) by fast
next
  case (other S S')
  thus ?case
    proof (induct rule: cdcl_o.induct)
      case (decided T U)
      show ?case
        apply (rule decidedE[OF decided])
        using decide by auto
    next
      case (skip S S')
      thus ?case using assms(7) by (auto elim!: skipE)
    next
      case (resolve S S')
      thus ?case using assms(8) by (auto elim!: resolveE)
    next
      case backtrack
      thus ?case using assms(9) by (auto elim: backtrackE)
    qed
next
  case (rf S S')
  thus ?case by (induct rule: cdcl_rf.induct) (fast dest: forget restart)+
qed

lemma cdcl_o_induct[consumes 1, case_names decided skip resolve backtrack]:
  fixes S  :: "'v cdcl_state"
  assumes cdcl: "cdcl_o S S'"
  and decide: "\<And>M N U k L.  undefined_lit L M \<Longrightarrow> atm_of L \<in> atms_of_m N
    \<Longrightarrow> P (M, N, U, k, C_True)  (Marked L (k+1) # M, N, U, k + 1, C_True)"
  and skip: "\<And>M N L C' D k U. -L \<notin># D \<Longrightarrow> D \<noteq> {#}
    \<Longrightarrow> P (Propagated L C' # M, N, U, k, C_Clause D) (M, N, U, k, C_Clause D)"
  and resolve: "\<And>M N L D k U C. (get_maximum_level D (Propagated L (C + {#L#}) # M) = k \<or> k= 0)
    \<Longrightarrow> P (Propagated L (C + {#L#}) # M, N, U, k, C_Clause (D + {#-L#}))
      (M, N, U, k, C_Clause (remdups_mset (D + C)))"
  and backtrack: "\<And>M N U k D L K i M1 M2.
    (Marked K (i+1) # M1, M2) \<in> set (get_all_marked_decomposition M)
    \<Longrightarrow> get_level L M = k \<Longrightarrow> get_level L M = get_maximum_level (D+{#L#}) M
    \<Longrightarrow> get_maximum_level D M = i
    \<Longrightarrow> P (M, N, U, k, C_Clause (D + {#L#}))
      (Propagated L (D+{#L#}) # M1, N, U \<union> {D +  {#L#}}, i, C_True)"
  shows "P S S'"
  using cdcl
  apply (induction rule: cdcl_o.induct)
  using assms(2,3,4,5) by (auto elim: btE decidedE skipE resolveE)

lemma level_of_marked_ge_1:
  assumes "cdcl S S'"
  and "\<forall>L l. Marked L l \<in> set (trail S) \<longrightarrow> l > 0"
  shows "\<forall>L l. Marked L l \<in> set (trail S') \<longrightarrow> l > 0"
  using assms by (induct rule: cdcl_all_induct)
    (auto dest!: union_in_get_all_marked_decomposition_is_subset)

subsection \<open>Invariants\<close>
(*TODO Move to first section*)
subsubsection \<open>Properties about the levels\<close>
fun get_all_levels_of_marked :: "('b, 'a, 'c) marked_lit list \<Rightarrow> 'a list"  where
"get_all_levels_of_marked [] = []" |
"get_all_levels_of_marked (Marked l level # Ls) = level # get_all_levels_of_marked Ls" |
"get_all_levels_of_marked (Propagated _ _ # Ls) = get_all_levels_of_marked Ls"

lemma get_all_levels_of_marked_cons:
  "get_all_levels_of_marked (a # b) = (if is_marked a then [level_of a] else []) @ get_all_levels_of_marked b"
  by (case_tac a) simp_all

lemma get_all_levels_of_marked_append[simp]:
  "get_all_levels_of_marked (a @ b) = get_all_levels_of_marked a @ get_all_levels_of_marked b"
  by (induct a) (simp_all add: get_all_levels_of_marked_cons)

lemma get_rev_level_less_max_get_all_levels_of_marked:
  "get_rev_level L n M \<le> Max (set (n # get_all_levels_of_marked M))"
  apply (induct M arbitrary: n, simp)
  by (case_tac a) (simp_all add: max.coboundedI2)

lemma get_rev_level_ge_min_get_all_levels_of_marked:
  assumes "atm_of L \<in> atm_of ` lits_of M"
  shows "get_rev_level L n M \<ge> Min (set (n # get_all_levels_of_marked M))"
  using assms apply (induct M arbitrary: n, simp)
  by (case_tac a, auto simp add: min_le_iff_disj)

lemma get_all_levels_of_marked_rev_eq_rev_get_all_levels_of_marked[simp]:
  "get_all_levels_of_marked (rev M) = rev (get_all_levels_of_marked M)"
  apply (induct M, simp)
  by (case_tac a, simp_all add: max.coboundedI2)

lemma get_maximum_possible_level_max_get_all_levels_of_marked:
  "get_maximum_possible_level M = Max (insert 0 (set (get_all_levels_of_marked M)))"
  apply (induct M, simp)
  by (case_tac a) (case_tac "set (get_all_levels_of_marked M) = {}", auto)

lemma get_rev_level_in_levels_of_marked:
  "get_rev_level L n M \<in> {0, n} \<union> set (get_all_levels_of_marked M)"
  apply (induction M arbitrary: n)
   apply auto[1]
  by (case_tac a)
    (force simp add: atm_of_eq_atm_of)+

lemma get_rev_level_in_atms_in_levels_of_marked:
  "atm_of L \<in> atm_of ` (lits_of M) \<Longrightarrow> get_rev_level L n M \<in> {n} \<union> set (get_all_levels_of_marked M)"
  apply (induction M arbitrary: n)
   apply auto[1]
  apply (case_tac a)
   apply (force simp add: atm_of_eq_atm_of)
  apply auto
  done

lemma get_all_levels_of_marked_no_marked:
  "(\<forall>l\<in>set Ls. \<not> is_marked l) \<longleftrightarrow> get_all_levels_of_marked Ls = []"
  by (induction Ls) (auto simp add: get_all_levels_of_marked_cons)

lemma get_level_in_levels_of_marked:
  "get_level L M \<in> {0} \<union> set (get_all_levels_of_marked M)"
  using get_rev_level_in_levels_of_marked[of L 0 "rev M"] by auto

text \<open>The zero is here to avoid empty-list issues with @{term last}:\<close>
lemma get_level_get_rev_level_get_all_levels_of_marked:
  assumes "atm_of L \<notin> atm_of ` (lit_of ` set M)"
  shows "get_level L (K @ M) = get_rev_level L (last (0 # get_all_levels_of_marked (rev M)))
    (rev K)"
  using assms
proof (induct M arbitrary: K)
  case Nil
  thus ?case by auto
next
  case (Cons a M)
  hence H: "\<And>K. get_level L (K @ M) = get_rev_level L (last (0 # get_all_levels_of_marked (rev M))) (rev K)"
    by auto
  have "get_level L ((K @ [a])@ M) = get_rev_level L (last (0 # get_all_levels_of_marked (rev M))) (a # rev K)"
    using H[of "K @ [a]"] by simp
  thus ?case using Cons(2) by (case_tac a) auto
qed

lemma cdcl_o_bt:
  assumes "cdcl_o S S'"
  and "backtrack_level S = length (get_all_levels_of_marked (trail S))"
  and "get_all_levels_of_marked (trail S) = rev ([1..<(1+length (get_all_levels_of_marked (trail S)))])"
  shows "backtrack_level S' = length (get_all_levels_of_marked (trail S'))"
  using assms
proof (induct rule: cdcl_o_induct)
  case (backtrack M N U k D L K i M1 M2)
  then obtain c where M: "M = c @ M2 @ Marked K (i + 1) # M1"
    using get_all_marked_decomposition_exists_prepend by blast
  have "rev (get_all_levels_of_marked M) = [1..<1+ (length (get_all_levels_of_marked M))]"
    using local.backtrack(6) by (auto simp add: rev_swap[symmetric])
  thus ?case unfolding M by (auto dest: append_cons_eq_upt_length simp del: upt.simps)
qed auto

lemma cdcl_rf_bt:
  assumes "cdcl_rf S S'"
  and "backtrack_level S = length (get_all_levels_of_marked (trail S))"
  and "get_all_levels_of_marked (trail S) = rev ([1..<(1+length (get_all_levels_of_marked (trail S)))])"
  shows "backtrack_level S' = length (get_all_levels_of_marked (trail S'))"
  using assms by (induct rule: cdcl_rf.induct) auto

lemma cdcl_bt:
  assumes "cdcl S S'"
  and "backtrack_level S = length (get_all_levels_of_marked (trail S))"
  and "get_all_levels_of_marked (trail S) = rev ([1..<(1+length (get_all_levels_of_marked (trail S)))])"
  shows "backtrack_level S' = length (get_all_levels_of_marked (trail S'))"
  using assms by (induct rule: cdcl.induct) (auto simp add: cdcl_o_bt cdcl_rf_bt)


value "backtrack_level (S0_cdcl N) = length (get_all_levels_of_marked (fst (S0_cdcl N)))"
value "get_all_levels_of_marked (fst (S0_cdcl N)) = rev ([1..<(1+length (get_all_levels_of_marked (fst (S0_cdcl N))))])"

lemma cdcl_bt_level':
  assumes "cdcl S S'"
  and "backtrack_level S = length (get_all_levels_of_marked (trail S))"
  and "get_all_levels_of_marked (trail S) = rev ([1..<(1+length (get_all_levels_of_marked (trail S)))])"
  shows "get_all_levels_of_marked (trail S') = rev ([1..<(1+length (get_all_levels_of_marked (trail S')))])"
  using assms
proof (induct rule: cdcl_all_induct)
  case (decided M N U k L)
  let ?M' = "Marked L (k + 1) # M"
  have H: "get_all_levels_of_marked M = rev [Suc 0..<1+length (get_all_levels_of_marked M)]"
    using decided.prems by simp
  have k: "k = length (get_all_levels_of_marked M)"
    using decided.prems by auto
  have "get_all_levels_of_marked ?M' = Suc k # get_all_levels_of_marked M" by simp
  hence "get_all_levels_of_marked ?M' = Suc k # rev [Suc 0..<1+length (get_all_levels_of_marked M)]"
    using H by auto
  also have "\<dots> = rev [Suc 0..< Suc (1+length (get_all_levels_of_marked M))]"
    unfolding k by simp
  finally show ?case by simp
next
  case (backtrack M N U k D L K i M1 M2)
  then obtain c where M: "M = c @ M2 @ Marked K (i + 1) # M1" using get_all_marked_decomposition_exists_prepend by metis
  have "rev (get_all_levels_of_marked M1) @ Suc i # rev (get_all_levels_of_marked M2) @ rev (get_all_levels_of_marked c) =  [Suc 0..<2+length (get_all_levels_of_marked c) + (length (get_all_levels_of_marked M2) + length (get_all_levels_of_marked M1))]"
    using backtrack.prems(2) backtrack.hyps(1) unfolding M backtrack.hyps(1)
    by (auto simp add: rev_swap[symmetric] simp del: upt.simps)
  thus ?case by (auto simp add: rev_swap dest!: append_cons_eq_upt(1) simp del: upt.simps)
qed auto

lemma backtrack_lit_skiped:
  assumes L: "get_level L (trail S) = backtrack_level S"
  and M1: "(Marked K (i + 1) # M1, M2) \<in> set (get_all_marked_decomposition (trail S))"
  and no_dup: "no_dup (trail S)"
  and bt_l: "backtrack_level S = length (get_all_levels_of_marked (trail S))"
  and order: "get_all_levels_of_marked (trail S) = rev ([1..<(1+length (get_all_levels_of_marked (trail S)))])"
  shows "atm_of L \<notin> atm_of ` lits_of M1"
proof
  let ?M = "trail S"
  assume L_in_M1: "atm_of L \<in> atm_of ` lits_of M1"
  obtain c where Mc: "trail S = c @ M2 @ Marked K (i + 1) # M1"
    using M1 get_all_marked_decomposition_exists_prepend by blast
  have "atm_of L \<notin> atm_of ` lit_of ` set c"
    using L_in_M1 no_dup mk_disjoint_insert unfolding Mc lits_of_def by force
  have g_M_eq_g_M1: "get_level L ?M = get_level L M1"
    using L_in_M1 unfolding Mc lits_of_def by auto
  have g: "get_all_levels_of_marked M1 = rev [1..<Suc i]"
    using order unfolding Mc
    by (auto simp del: upt.simps dest!: append_cons_eq_upt_length_i
      simp add: rev_swap[symmetric])
  hence "Max (set (0 # get_all_levels_of_marked (rev M1))) < Suc i" by auto
  hence "get_level L M1 < Suc i"
    using get_rev_level_less_max_get_all_levels_of_marked[of L 0 "rev M1"] by linarith
  also have "Suc i \<le> backtrack_level S" using bt_l by (simp add: Mc g)
  ultimately show False using L g_M_eq_g_M1 by auto
qed

lemma cdcl_distinctinv_1:
  assumes "cdcl S S'"
  and "no_dup (trail S)"
  and "backtrack_level S = length (get_all_levels_of_marked (trail S))"
  and "get_all_levels_of_marked (trail S) = rev ([1..<(1+length (get_all_levels_of_marked (trail S)))])"
  shows "no_dup (trail S')"
  using assms
proof (induct rule: cdcl_all_induct)
  case (backtrack M N U k D L K i M1 M2) note M1 = this(1) and L = this(2)
  obtain c where Mc: "M = c @ M2 @ Marked K (i + 1) # M1"
    using M1 get_all_marked_decomposition_exists_prepend by blast
  have "no_dup (M2 @ Marked K (i + 1) # M1)"
    using M1 backtrack.prems(1) get_all_marked_decomposition_exists_prepend by fastforce
  also have "atm_of L \<notin> (\<lambda>l. atm_of (lit_of l)) ` set M1"
    using backtrack_lit_skiped[of L "(M, N, U, k, C_Clause (D + {#L#}))" K i M1 M2] L M1 backtrack.prems by (fastforce simp add: lits_of_def)
  ultimately show ?case by simp
qed (auto simp add: undefined_in_M_implies_not_in_M)


lemma cdcl_consistent_inv_2:
  assumes "cdcl S S'"
  and "consistent_interp (lits_of (trail S))"
  and "no_dup (trail S)"
  and "backtrack_level S = length (get_all_levels_of_marked (trail S))"
  and "get_all_levels_of_marked (trail S) = rev ([1..<(1+length (get_all_levels_of_marked (trail S)))])"
  shows "consistent_interp (lits_of (trail S'))"
  using assms
proof (induct rule: cdcl_all_induct)
  case (backtrack M N U k C L K i M1 M2) note M1 = this(1) and L = this(2)
  obtain c where Mc: "M = c @ M2 @ Marked K (i + 1) # M1" using M1 get_all_marked_decomposition_exists_prepend by blast
  hence "consistent_interp (lit_of ` set M1)"
    using consistent_interp_subset[of "lit_of ` set M1" "lits_of M"] backtrack.prems(1)
    unfolding lits_of_def by auto
  also have "atm_of L \<notin> atm_of ` lits_of M1"
    using backtrack_lit_skiped[of L "(M, N, U, k, C_True)" K i M1 M2] L backtrack by simp
  hence "L \<notin> lits_of M1" and "-L \<notin> lits_of M1" using image_iff by fastforce+
  ultimately show ?case unfolding lits_of_def by simp
qed (auto | (metis consistent_interp_def insert_iff))+

lemma cdcl_no_more_clauses:
  assumes "cdcl S S'"
  shows "clauses S = clauses S'"
  using assms by (induct rule: cdcl_all_induct) auto

lemma rtranclp_cdcl_no_more_clauses:
  assumes "cdcl\<^sup>*\<^sup>* S S'"
  shows "clauses S = clauses S'"
  using assms by (induct rule: rtranclp.induct) (auto dest: cdcl_no_more_clauses)

definition "cdcl_M_level_inv (S:: 'v cdcl_state) \<longleftrightarrow>
  consistent_interp (lits_of (trail S))
  \<and> no_dup (trail S)
  \<and> backtrack_level S = length (get_all_levels_of_marked (trail S))
  \<and> get_all_levels_of_marked (trail S) = rev ([1..<(1+length (get_all_levels_of_marked (trail S)))])"

lemma cdcl_M_level_inv_decomp[dest]:
  assumes "cdcl_M_level_inv S"
  shows "consistent_interp (lits_of (trail S))"
  and "no_dup (trail S)"
  and "length (get_all_levels_of_marked (trail S)) = backtrack_level S"
  and "get_all_levels_of_marked (trail S) = rev ([Suc 0..< Suc 0+backtrack_level S])"
  using assms unfolding cdcl_M_level_inv_def by fastforce+

lemma cdcl_consistent_inv:
  fixes S S' :: "'v cdcl_state"
  assumes "cdcl S S'"
  and "cdcl_M_level_inv S"
  shows "cdcl_M_level_inv S'"
  using assms cdcl_consistent_inv_2 cdcl_distinctinv_1 cdcl_bt cdcl_bt_level' unfolding cdcl_M_level_inv_def by blast+

lemma rtranclp_cdcl_consistent_inv:
  assumes "cdcl\<^sup>*\<^sup>* S S'"
  and "cdcl_M_level_inv S"
  shows "cdcl_M_level_inv S'"
  using assms apply (induct rule: rtranclp.induct)
  using cdcl_consistent_inv by auto

lemma cdcl_M_level_inv_S0_cdcl[simp]:
    "cdcl_M_level_inv (S0_cdcl N)"
  unfolding cdcl_M_level_inv_def  by auto

subsubsection \<open>Learned Clause\<close>
text \<open>This invariant shows that:
  * the learned clauses are entailed by the initial set of clauses.
  * the conflicting clause is entailed by the initial set of clauses.
  * the marks are entailed by the clauses. A more precise version would be to show that either these marked are learned or are in the set of clauses\<close>
(*TODO uncomment last + remove the previous + adapt*)
definition "cdcl_learned_clause (S::'v cdcl_state) \<equiv> (clauses S \<Turnstile>ps learned_clauses S
  \<and> (\<forall>T. conflicting S = C_Clause T \<longrightarrow> clauses S \<Turnstile>p T)
  \<and> (clauses S \<Turnstile>ps set (get_all_mark_of_propagated (trail S)))
  (*\<and> set (get_all_mark_of_propagated (trail S)) \<subseteq> clauses S \<union> learned_clauses S*))"

lemma cdcl_learned_clause_decomp[dest]:
  assumes "cdcl_learned_clause (S::'v cdcl_state)"
  shows "clauses S \<Turnstile>ps learned_clauses S"
  and "\<forall>T. conflicting S = C_Clause T \<longrightarrow> clauses S \<Turnstile>p T"
  and "clauses S \<Turnstile>ps set (get_all_mark_of_propagated (trail S))"
  using assms unfolding cdcl_learned_clause_def by blast+

(*propo 2.10.5.2*)
lemma cdcl_learned_clause_S0_cdcl[simp]:
   "cdcl_learned_clause (S0_cdcl N)"
  unfolding cdcl_learned_clause_def by auto

lemma cdcl_learned_clauses:
  assumes "cdcl S S'"
  and "cdcl_learned_clause S"
  shows "cdcl_learned_clause S'"
  using assms
proof (induct rule: cdcl_all_induct)
  case (backtrack M N U k D L K i M1 M2)
  show ?case
    using backtrack.prems backtrack.hyps(1) unfolding cdcl_learned_clause_def
    by (force dest: get_all_marked_decomposition_exists_prepend)
qed (auto dest: mk_disjoint_insert
      simp add: cdcl_learned_clause_def 
      intro: true_clss_cls_or_true_clss_cls_or_not_true_clss_cls_or)

lemma rtranclp_cdcl_learned_clauses:
  assumes "cdcl\<^sup>*\<^sup>* S S'"
  and "cdcl_learned_clause S"
  shows "cdcl_learned_clause S'"
  using assms by (induction) (auto dest: cdcl_learned_clauses)

(*TODO Move*)
lemma in_implies_atm_of_on_atms_of_m[simp]:
  assumes "C + {#L#} \<in> N"
  shows "atm_of L \<in> atms_of_m N"
  using atms_of_atms_of_m_mono[OF assms] by auto

subsubsection \<open>No alien atom in the state\<close>
text \<open>This invariant means that all the literals are in the set of clauses.\<close>
definition "no_strange_atm S' \<longleftrightarrow> (
   (\<forall>T. conflicting S' = C_Clause T \<longrightarrow> atms_of T \<subseteq> atms_of_m (clauses S')) \<and>
   (\<forall>L mark. Propagated L mark \<in> set (trail S') \<longrightarrow> atms_of mark \<subseteq> atms_of_m (clauses S')) \<and>
   atms_of_m (learned_clauses S') \<subseteq> atms_of_m (clauses S') \<and>
   atm_of ` (lits_of (trail S')) \<subseteq> atms_of_m (clauses S'))"

lemma no_strange_atm_decomp[dest]:
  assumes "no_strange_atm S"
  shows "conflicting S = C_Clause T \<Longrightarrow> atms_of T \<subseteq> atms_of_m (clauses S)"
  and "(\<forall>L mark. Propagated L mark \<in> set (trail S) \<longrightarrow> atms_of mark \<subseteq> atms_of_m (clauses S))"
  and "atms_of_m (learned_clauses S) \<subseteq> atms_of_m (clauses S)"
  and "atm_of ` (lits_of (trail S)) \<subseteq> atms_of_m (clauses S)"
  using assms unfolding no_strange_atm_def by blast+

lemma no_strange_atm_decomp_2[dest!]:
  assumes "no_strange_atm (M, N, U, k, C_Clause D)"
  shows "atms_of D \<subseteq> atms_of_m N"
  using assms by auto

lemma no_strange_atm_S0 [simp]: "no_strange_atm (S0_cdcl N)"
  unfolding no_strange_atm_def by auto

lemma cdcl_no_strange_atm_explicit:
  assumes "cdcl S S'"
  and "\<forall>T. conflicting S = C_Clause T \<longrightarrow> atms_of T \<subseteq> atms_of_m (clauses S)"
  and "\<forall>L mark. Propagated L mark \<in> set (trail S) \<longrightarrow> atms_of mark \<subseteq> atms_of_m (clauses S)"
  and "atms_of_m (learned_clauses S) \<subseteq> atms_of_m (clauses S)"
  and "atm_of ` (lits_of (trail S)) \<subseteq> atms_of_m (clauses S)"
  shows "(\<forall>T. conflicting S' = C_Clause T \<longrightarrow> atms_of T \<subseteq> atms_of_m (clauses S')) \<and>
   (\<forall>L mark. Propagated L mark \<in> set (trail S') \<longrightarrow> atms_of mark \<subseteq> atms_of_m (clauses S')) \<and>
   atms_of_m (learned_clauses S') \<subseteq> atms_of_m (clauses S') \<and>
   atm_of ` (lits_of (trail S')) \<subseteq> atms_of_m (clauses S')" (is "?C S' \<and> ?M S' \<and> ?U S' \<and> ?V S'")
  using assms
proof (induct rule: cdcl_all_induct)
  case (propagate M N U k C L)
  have "?C (Propagated L (C + {#L#}) # M, N, U, k, C_True)"  by auto
  also have "?M (Propagated L (C + {#L#}) # M, N, U, k, C_True)"
    using propagate.prems(2,3) `C + {#L#} \<in> N \<union> U ` by (fastforce simp add: atms_of_m_def)
  moreover have "?U (Propagated L (C + {#L#}) # M, N, U, k, C_True)" 
    using propagate.prems(3) by auto
  moreover have "?V (Propagated L (C + {#L#}) # M, N, U, k, C_True)"
    using `C + {#L#} \<in> N \<union> U` propagate.prems(3,4) unfolding lits_of_def by auto
  ultimately show ?case by blast
next
  case (decided M N U k L)
  thus ?case by auto
next
  case (skip L C' M N U k D)
  thus ?case by auto
next
  case (conflict M N U k D)
  have "atm_of ` set_mset D \<subseteq> \<Union>(atms_of ` N)"
    using `D \<in> N \<union> U` conflict.prems(3) by (auto simp add: atms_of_def atms_of_m_def)
  thus ?case using conflict.prems unfolding atms_of_def atms_of_m_def by force
next
  case (restart M N U k)
  thus ?case by auto
next
  case (forget M N U k)
  thus ?case by auto
next
  case (backtrack M N U k D L K i M1 M2) note S = this(1)
  have "?C (Propagated L (D+{#L#}) # M1 , N, U \<union> {D +  {#L#}}, i, C_True)"
    using backtrack.prems(3) unfolding S by simp
  also have "set M1 \<subseteq> set M"
    using backtrack.hyps(1) by (auto dest: get_all_marked_decomposition_exists_prepend)
  hence M: "?M (Propagated L (D+{#L#}) # M1 , N, U \<union> {D +  {#L#}}, i, C_True)"
    using backtrack.prems(1,2) by (fastforce simp add: image_subset_iff S)
  moreover have "?U (Propagated L (D+{#L#}) # M1 , N, U \<union> {D +  {#L#}}, i, C_True)"
    using backtrack.prems(1,3) unfolding S by auto
  moreover have "?V (Propagated L (D+{#L#}) # M1 , N, U \<union> {D +  {#L#}}, i, C_True)"
    using M backtrack.prems(4) backtrack.hyps(1)
    by (fastforce dest: get_all_marked_decomposition_exists_prepend)
  ultimately show ?case by blast
next
  case (resolve M N L D k U C)
  have "?C (M, N, U, k, C_Clause (remdups_mset (D + C)))"
    using resolve.prems(1,2) by simp
  also have  "?M (M, N, U, k, C_Clause (remdups_mset (D + C)))"
    using resolve.prems(2) resolve.prems(1) by auto
  moreover have "?U (M, N, U, k, C_Clause (remdups_mset (D + C)))"
    using resolve.prems(1,3) by auto
  moreover have "?V (M, N, U, k, C_Clause (remdups_mset (D + C)))"
    using resolve.prems(4) by auto
  ultimately show ?case by blast
qed

lemma cdcl_no_strange_atm_inv:
  assumes "cdcl S S'"
  and "no_strange_atm S"
  shows "no_strange_atm S'"
  using assms(2) cdcl_no_strange_atm_explicit[OF assms(1)] unfolding no_strange_atm_def by fast

lemma rtranclp_cdcl_no_strange_atm_inv:
  assumes "cdcl\<^sup>*\<^sup>* S S'"
  and "no_strange_atm S"
  shows "no_strange_atm S'"
  using assms by induction (auto intro: cdcl_no_strange_atm_inv)

subsubsection \<open>No duplicates all around\<close>
text \<open>This invariant shows that there is no duplicate (no literal appearing twice in the formula). The last part could be proven using the previous invariant also.\<close>
definition "distinct_cdcl_state (S::'v cdcl_state) 
  \<longleftrightarrow> ((\<forall>T. conflicting S = C_Clause T \<longrightarrow> distinct_mset T) 
    \<and> distinct_mset_set (learned_clauses S) 
    \<and> distinct_mset_set (clauses S) 
    \<and> (\<forall>L mark. (Propagated L mark \<in> set (trail S) \<longrightarrow> distinct_mset mark)))"

lemma distinct_cdcl_state_decomp[dest]:
  assumes "distinct_cdcl_state (S::'v cdcl_state)"
  shows "\<forall>T. conflicting S = C_Clause T \<longrightarrow> distinct_mset T"
  and "distinct_mset_set (learned_clauses S)"
  and "distinct_mset_set (clauses S)"
  and "\<forall>L mark. (Propagated L mark \<in> set (trail S) \<longrightarrow> distinct_mset mark)"
  using assms unfolding distinct_cdcl_state_def by blast+

lemma distinct_cdcl_state_decomp_2[dest]:
  assumes "distinct_cdcl_state (S::'v cdcl_state)"
  shows "conflicting S = C_Clause T \<Longrightarrow> distinct_mset T"
  using assms by auto

lemma distinct_cdcl_state_S0_cdcl[simp]: "distinct_mset_set N \<Longrightarrow> distinct_cdcl_state (S0_cdcl N)"
  unfolding distinct_cdcl_state_def by auto

lemma distinct_cdcl_state_inv:
  assumes "cdcl S S'"
  and "distinct_cdcl_state S"
  shows "distinct_cdcl_state S'"
  using assms
proof (induct rule: cdcl_all_induct)
  case (backtrack M N U k D L K i M1 M2)
  thus ?case using get_all_marked_decomposition_incl unfolding distinct_cdcl_state_def by fastforce
qed (auto simp add: distinct_cdcl_state_def distinct_mset_set_def)

lemma rtanclp_distinct_cdcl_state_inv:
  assumes "cdcl\<^sup>*\<^sup>* S S'"
  and "distinct_cdcl_state S"
  shows "distinct_cdcl_state S'"
  using assms apply (induct rule: rtranclp.induct)
  using distinct_cdcl_state_inv by blast+

subsubsection \<open>Conflicts and co\<close>
text \<open>This invariant shows that each mark contains a contradiction only related to the previously defined variable.\<close>
abbreviation every_mark_is_a_conflict :: "'v cdcl_state \<Rightarrow> bool" where
"every_mark_is_a_conflict S \<equiv>
 \<forall>L mark a b. a @ Propagated L mark # b = (trail S) \<longrightarrow> (b \<Turnstile>as CNot (mark - {#L#}) \<and> L \<in># mark)"

lemma backtrack_atms_of_D_in_M1:
  assumes bt: "backtrack S (Propagated L (D+{#L#}) # M1 , N, U \<union> {D + {#L#}}, i, C_True)"
  and confl: "\<forall>T. conflicting S = C_Clause T \<longrightarrow> trail S \<Turnstile>as CNot T"
  and lev: "cdcl_M_level_inv S"
  shows "atms_of D \<subseteq> atm_of ` lit_of ` set M1"
proof (rule ccontr)
  obtain M N U K M2 where
    S: "S = (M, N, U, get_maximum_level (D + {#L#}) M, C_Clause (D + {#L#}))" and
    i: "i= get_maximum_level D M" and
    decomp: "(Marked K (get_maximum_level D M +1) # M1, M2) \<in> set (get_all_marked_decomposition M)" and
    level_L: "get_level L M = get_maximum_level (D + {#L#}) M"
      using bt by (auto elim: btE)
  let ?k = "get_maximum_level (D + {#L#}) M"
  have "M \<Turnstile>as CNot D" using S confl by auto
  hence vars_of_D: "atms_of D \<subseteq> atm_of ` lit_of ` set M" unfolding lits_of_def atms_of_def
    by (meson image_subsetI mem_set_mset_iff true_annots_CNot_all_atms_defined)

  obtain M0 where M: "M = M0 @ M2 @ Marked K (i+1) # M1"
    using decomp get_all_marked_decomposition_exists_prepend i by blast

  assume a: "\<not> ?thesis"
  then obtain L where
    L: "L \<in> atms_of D" and
    L_notin_M1: "L \<notin> atm_of ` lit_of ` set M1" by auto
  then have L_in: "L \<in> atm_of ` lit_of ` set (M0 @ M2 @ Marked K (i + 1) # [])"
    using vars_of_D unfolding M by force
  then obtain L' where
    "L' \<in># D" and
    L': "L = atm_of L'"
    using L L_notin_M1 unfolding atms_of_def by auto
  have "get_level L' M = get_rev_level L' (Suc i) (Marked K (Suc i) # rev M2 @ rev M0)"
    using L_notin_M1 L' M by (auto simp del: get_rev_level.simps)
  then have "get_all_levels_of_marked M = rev [1..<(1+?k)]"
    using lev unfolding S by (auto simp del: upt.simps)
  then have M: "get_all_levels_of_marked M0 @ get_all_levels_of_marked M2 = rev [Suc (Suc i)..<Suc (Suc (length (get_all_levels_of_marked M0) + (length (get_all_levels_of_marked M2) + length (get_all_levels_of_marked M1))))]"
    using lev rev_swap unfolding S M
    by (auto simp del: upt.simps dest!: append_cons_eq_upt_length_i_end
      simp add: rev_swap[symmetric])

  have "get_rev_level L' (Suc i) (Marked K (Suc i) # rev (M0 @ M2)) \<ge> Min (set ((Suc i) # get_all_levels_of_marked (Marked K (Suc i) # rev (M0 @ M2))))"
    using get_rev_level_ge_min_get_all_levels_of_marked[of L' "rev (M0 @ M2 @ [Marked K (i + 1)])" "Suc i"] L_in unfolding L' by (fastforce simp add: lits_of_def)
  also have "Min (set ((Suc i) # get_all_levels_of_marked (Marked K (Suc i) # rev (M0 @ M2)))) = Min (set ((Suc i) # get_all_levels_of_marked (rev (M0 @ M2))))" by auto
  also have "\<dots> = Min (set ((Suc i) # get_all_levels_of_marked M0 @ get_all_levels_of_marked M2))"
    by (simp add: Un_commute)
  also have "\<dots> =  Min (set ((Suc i) # [Suc (Suc i)..<Suc (Suc (length (get_all_levels_of_marked M0) + (length (get_all_levels_of_marked M2) + length (get_all_levels_of_marked M1))))]))"
    unfolding M by (auto simp add: Un_commute)
  also have "\<dots> = Suc i" by (auto intro: Min_eqI)
  finally have "get_rev_level L' (Suc i) (Marked K (Suc i) # rev (M0 @ M2)) \<ge> Suc i" .
  hence "get_level L' M \<ge> i + 1" using `get_level L' M = get_rev_level L' (Suc i) (Marked K (Suc i) # rev M2 @ rev M0)` by simp
  hence "get_maximum_level D M \<ge> i + 1"
    using get_maximum_level_ge_get_level[OF `L' \<in># D`, of M] by auto
  thus False using i by auto
qed

lemma distinct_atms_of_incl_not_in_other:
    assumes "no_dup (M @ M')"
    and "atms_of D \<subseteq> atm_of ` lit_of ` set M'"
    shows"\<forall>x\<in>atms_of D. x \<notin> atm_of ` lit_of ` set M"
   using assms by force

lemma cdcl_propagate_is_conclusion:
  assumes "cdcl S S'"
  and "all_decomposition_implies (clauses S) (get_all_marked_decomposition (trail S))"
  and "cdcl_learned_clause S"
  and "\<forall>T. conflicting S = C_Clause T \<longrightarrow> trail S \<Turnstile>as CNot T"
  and "cdcl_M_level_inv S"
  and "no_strange_atm S"
  shows "all_decomposition_implies (clauses S') (get_all_marked_decomposition (trail S'))"
  using assms
proof (induct rule: cdcl_all_induct)
  case restart
  thus ?case by auto
next
  case forget
  thus ?case by auto
next
  case conflict
  thus ?case by auto
next
  case (resolve M N L D k U C)
  have M: "set (get_all_marked_decomposition M) = insert (hd (get_all_marked_decomposition M)) (set (tl (get_all_marked_decomposition M)))"
    by (cases "get_all_marked_decomposition M") auto
  show ?case
    using resolve.prems(1) unfolding all_decomposition_implies_def
    by (cases "(hd (get_all_marked_decomposition M))")
       (auto simp add: M)
next
  case (skip M N L C' D k U)
  have M: "set (get_all_marked_decomposition M) = insert (hd (get_all_marked_decomposition M)) (set (tl (get_all_marked_decomposition M)))"
    by (cases "get_all_marked_decomposition M") auto
  show ?case
    using skip.prems(1) unfolding all_decomposition_implies_def
    by (case_tac "(hd (get_all_marked_decomposition M))")
       (auto simp add: M)
next
  case decided note S = this(1)
  show ?case using decided.prems(1) unfolding S all_decomposition_implies_def by auto
next
  case (propagate M N U k C L) note propa = this(1) and decomp = this(4) and alien = this(8)
  obtain a y where ay: "hd (get_all_marked_decomposition M) = (a, y)"
    by (cases "hd (get_all_marked_decomposition M)")
  hence M': "M = y @ a" using get_all_marked_decomposition_decomp by blast
  have M: "set (get_all_marked_decomposition M) = insert (a, y) (set (tl (get_all_marked_decomposition M)))"
    using ay by (cases "get_all_marked_decomposition M") auto
  have "(\<lambda>a. {#lit_of a#}) ` set a \<union> N \<Turnstile>ps (\<lambda>a. {#lit_of a#}) ` set y"
    using decomp ay unfolding all_decomposition_implies_def
    by (cases "get_all_marked_decomposition M") fastforce+
  hence a_Un_N_M: "(\<lambda>a. {#lit_of a#}) ` set a \<union> N \<Turnstile>ps (\<lambda>a. {#lit_of a#}) ` set M"
    unfolding M' by (auto simp add: all_in_true_clss_clss image_Un)

  have "(\<lambda>a. {#lit_of a#}) ` set a \<union> N \<Turnstile>p {#L#}"
    proof (rule true_clss_cls_plus_CNot')
      show "(\<lambda>a. {#lit_of a#}) ` set a \<union> N \<Turnstile>p C + {#L#}"
        using propa propagate.prems(2) by (auto dest!: true_clss_clss_in_imp_true_clss_cls)
    next
      have "atm_of L \<notin> atms_of_m N \<Longrightarrow> atm_of L \<in> atm_of ` lit_of ` set a"
        using alien propa unfolding no_strange_atm_def
        by (auto dest: in_implies_atm_of_on_atms_of_m)
      also have "\<And>x. x \<in> atms_of C \<Longrightarrow> x \<notin> atms_of_m N \<Longrightarrow> x \<in> atm_of ` lit_of ` set a"
        using alien `C + {#L#} \<in> N \<union> U` unfolding no_strange_atm_def
        by (auto dest!: atms_of_atms_of_m_mono)
      ultimately show "atms_of (C + {#L#}) \<subseteq> atms_of_m ((\<lambda>a. {#lit_of a#}) ` set a \<union> N)"
        by auto
    next
      have "(\<lambda>m. {#lit_of m#}) ` set M \<Turnstile>ps CNot C"
        using `M \<Turnstile>as CNot C` true_annots_true_clss_clss by blast
      thus "(\<lambda>a. {#lit_of a#}) ` set a \<union> N \<Turnstile>ps CNot C"
        using a_Un_N_M true_clss_clss_left_right true_clss_clss_union_l_r by blast
    qed
  thus ?case
    using decomp unfolding ay all_decomposition_implies_def by (auto simp add: ay M)
next
  case (backtrack M N U k D L K i M1 M2)
  have "\<forall>l \<in> set M2. \<not>is_marked l" using get_all_marked_decomposition_snd_not_marked backtrack.hyps(1) by blast
  obtain M0 where M: "M = M0 @ M2 @ Marked K (i + 1) # M1" using backtrack.hyps(1) get_all_marked_decomposition_exists_prepend by blast
  show ?case unfolding all_decomposition_implies_def
    proof
      fix x
      assume "x \<in> set (get_all_marked_decomposition (trail (Propagated L (D + {#L#}) # M1, N, U \<union> {D + {#L#}}, i, C_True)))"
      hence x: "x \<in> set (get_all_marked_decomposition (Propagated L (D + {#L#}) # M1))" by simp
      let ?m = "get_all_marked_decomposition (Propagated L (D + {#L#}) # M1)"
      let ?hd = "hd ?m"
      let ?tl = "tl ?m"
      have "x = ?hd \<or> x \<in> set ?tl"
        using x by (case_tac "?m")  auto
      also {
        assume "x \<in> set ?tl"
        hence "x \<in> set (get_all_marked_decomposition M)"
          using tl_get_all_marked_decomposition_skip_some[of x] by (simp add: list.set_sel(2) M)
        hence "case x of (Ls, seen) \<Rightarrow> (\<lambda>a. {#lit_of a#}) ` set Ls \<union> clauses (Propagated L (D + {#L#}) # M1, N, U \<union> {D + {#L#}}, i, C_True) \<Turnstile>ps (\<lambda>a. {#lit_of a#}) ` set seen"
          using `x \<in> set ?m` backtrack.prems(1) unfolding all_decomposition_implies_def M by simp
      }
      moreover {
        assume "x = ?hd"
        obtain M1' M1'' where M1: "hd (get_all_marked_decomposition M1) = (M1', M1'')" by (case_tac "hd (get_all_marked_decomposition M1)")
        hence x': "x = (M1', Propagated L (D + {#L#}) # M1'')" using `x= ?hd` by auto
        have "(M1', M1'') \<in> set (get_all_marked_decomposition M)"
          using M1[symmetric] hd_get_all_marked_decomposition_skip_some[OF M1[symmetric], of "M0 @ M2" _ "i+1"] unfolding M by fastforce
        hence 1: "(\<lambda>a. {#lit_of a#}) ` set M1' \<union> N \<Turnstile>ps (\<lambda>a. {#lit_of a#}) ` set M1''"
          using backtrack.prems(1) unfolding all_decomposition_implies_def by auto
        also
        have "M \<Turnstile>as CNot D" using backtrack.prems(3) by auto
        hence vars_of_D: "atms_of D \<subseteq> atm_of ` lit_of ` set M"
          unfolding lits_of_def atms_of_def
          by (meson image_subsetI mem_set_mset_iff true_annots_CNot_all_atms_defined)
        have vars_of_D: "atms_of D \<subseteq> atm_of ` lit_of ` set M1"
          using backtrack_atms_of_D_in_M1[OF backtracking[OF _ backtrack.hyps] backtrack.prems(3) backtrack.prems(4)] by auto
        have "no_dup M" using backtrack.prems(4) by auto
        hence vars_in_M1: "\<forall>x \<in> atms_of D. x \<notin> atm_of ` lit_of ` set (M0 @ M2 @ Marked K (i + 1) # [])"
          using vars_of_D distinct_atms_of_incl_not_in_other[of "M0 @M2 @ Marked K (i + 1) # []" M1]
          unfolding M by auto
        have "M1 \<Turnstile>as CNot D"
          using vars_in_M1 true_annots_remove_if_notin_vars[of "M0 @ M2 @ Marked K (i + 1) # []" M1 "CNot D"] `M \<Turnstile>as CNot D` unfolding M lits_of_def by simp
        have "M1 = M1'' @ M1'" by (simp add: M1 get_all_marked_decomposition_decomp)
        have TT: "(\<lambda>a. {#lit_of a#}) ` set M1' \<union> N \<Turnstile>ps CNot D"
          using true_annots_true_clss_cls[OF `M1 \<Turnstile>as CNot D`] true_clss_clss_left_right[OF 1, of "CNot D"] unfolding `M1 = M1'' @ M1'` by (auto simp add: inf_sup_aci(5,7))
        have "N \<Turnstile>p D + {#L#}"
          using cdcl.other[OF cdcl_o.backtrack]  backtrack.hyps backtrack.prems(2) by auto
        hence T: "(\<lambda>a. {#lit_of a#}) ` set M1' \<union> N \<Turnstile>p D + {#L#}" by auto
        have "atms_of (D + {#L#}) \<subseteq> atms_of_m N" using backtrack.prems(5) by auto
        hence "(\<lambda>a. {#lit_of a#}) ` set M1' \<union> N \<Turnstile>p {#L#}"
          using true_clss_cls_plus_CNot'[OF T TT] by auto
        ultimately
          have "case x of (Ls, seen) \<Rightarrow>(\<lambda>a. {#lit_of a#}) ` set Ls \<union> clauses (Propagated L (D + {#L#}) # M1, N, U \<union> {D + {#L#}}, i, C_True) \<Turnstile>ps (\<lambda>a. {#lit_of a#}) ` set seen" unfolding x' by simp
      }
      ultimately show "case x of (Ls, seen) \<Rightarrow> (\<lambda>a. {#lit_of a#}) ` set Ls \<union> clauses (Propagated L (D + {#L#}) # M1, N, U \<union> {D + {#L#}}, i, C_True) \<Turnstile>ps (\<lambda>a. {#lit_of a#}) ` set seen" by blast
    qed
qed



lemma cdcl_propagate_is_false:
  assumes "cdcl S S'"
  and "all_decomposition_implies (clauses S) (get_all_marked_decomposition (trail S))"
  and "cdcl_learned_clause S"
  and "\<forall>T. conflicting S = C_Clause T \<longrightarrow> trail S \<Turnstile>as CNot T"
  and "cdcl_M_level_inv S"
  and "no_strange_atm S"
  and "every_mark_is_a_conflict S "
  shows "every_mark_is_a_conflict S'"
  using assms
proof (induct rule: cdcl_all_induct)
  case (propagate M N U k C L)
  show ?case
    proof (intro allI impI)
      fix L' mark a b
      assume "a @ Propagated L' mark # b = trail (Propagated L (C + {#L#}) # M, N, U, k, C_True)"
      hence "(a=[] \<and> L = L' \<and> mark = C + {#L#} \<and> b = M) \<or> tl a @ Propagated L' mark # b = M"
        by (cases a) fastforce+
      also {
        assume "tl a @ Propagated L' mark # b = M"
        hence "b \<Turnstile>as CNot (mark - {#L'#}) \<and> L' \<in># mark" using propagate.prems(6) by auto
      }
      moreover {
        assume "a=[]" and "L = L'" and "mark = C + {#L#}" and "b = M"
        hence "b \<Turnstile>as CNot (mark - {#L#}) \<and> L \<in># mark" using `M \<Turnstile>as CNot C` by auto
      }
      ultimately show "b \<Turnstile>as CNot (mark - {#L'#}) \<and> L' \<in># mark" by blast
    qed
next
  case (decided M N U k L)
  have "\<And>a La mark b. a @ Propagated La mark # b = Marked L (k+1) # M  \<Longrightarrow> tl a @ Propagated La mark # b = M" by (case_tac a, auto)
  thus ?case using decided.prems(6) unfolding decided.hyps(1) by fastforce
next
  case (skip M N L C' D k U)
  show ?case
    proof (intro allI impI)
      fix L' mark a b
      assume "a @ Propagated L' mark # b = trail (M, N, U, k, C_Clause D)"
      hence "a @ Propagated L' mark # b = M" by simp
      hence "(Propagated L C' # a) @ Propagated L' mark # b = Propagated L C' # M" by auto
      also have "\<forall>La mark a b. a @ Propagated La mark # b = Propagated L C' # M \<longrightarrow> b \<Turnstile>as CNot (mark - {#La#}) \<and> La \<in># mark"
        using skip.prems(6) unfolding skip.hyps(1) by simp
      ultimately show "b \<Turnstile>as CNot (mark - {#L'#}) \<and> L' \<in># mark" by blast
    qed
next
  case (conflict M N U k D)
  thus ?case by simp
next
  case (resolve M N L D k U C)
  show ?case unfolding resolve.hyps(1) trail_conv
    proof (intro allI impI)
      fix  L' mark a b
      assume "a @ Propagated L' mark # b = M"
      hence "Propagated L (C + {#L#}) # M = (Propagated L (C + {#L#}) # a) @ Propagated L' mark # b"
        by auto
      thus "b \<Turnstile>as CNot (mark - {#L'#}) \<and> L' \<in># mark"
        using resolve.prems(6) unfolding resolve.hyps(1) trail_conv by presburger
    qed
next
  case (restart M N U k)
  thus ?case by auto
next
  case (forget M N U C k)
  thus ?case by auto
next
  case (backtrack M N U k D L K i M1 M2)
  have "\<forall>l \<in> set M2. \<not>is_marked l"
    using get_all_marked_decomposition_snd_not_marked backtrack.hyps(1) by blast
  obtain M0 where M: "M = M0 @ M2 @ Marked K (i + 1) # M1"
    using backtrack.hyps(1) get_all_marked_decomposition_exists_prepend by blast
  show ?case unfolding trail_conv
    proof (intro allI impI)
      fix La mark a b
      assume "a @ Propagated La mark # b = Propagated L (D + {#L#}) # M1"
      hence "(a = [] \<and> Propagated La mark = Propagated L (D + {#L#}) \<and> b = M1) \<or> tl a @ Propagated La mark # b = M1" by (case_tac a, auto)
      also {
        assume A: "a = []" and P: "Propagated La mark = Propagated L (D + {#L#})" and b: "b = M1"
        have "M \<Turnstile>as CNot D" using backtrack.prems(3) by auto
        hence vars_of_D: "atms_of D \<subseteq> atm_of ` lit_of ` set M"
          unfolding lits_of_def atms_of_def
          by (meson image_subsetI mem_set_mset_iff true_annots_CNot_all_atms_defined)
        have vars_of_D: "atms_of D \<subseteq> atm_of ` lit_of ` set M1"
          using backtrack_atms_of_D_in_M1[OF backtracking[OF _ backtrack.hyps] backtrack.prems(3) backtrack.prems(4)] by auto
        have "no_dup M" using backtrack.prems(4) by auto
        hence vars_in_M1: "\<forall>x \<in> atms_of D. x \<notin> atm_of ` lit_of ` set (M0 @ M2 @ Marked K (i + 1) # [])"
          using vars_of_D distinct_atms_of_incl_not_in_other[of "M0 @ M2 @ Marked K (i + 1) # []" M1] unfolding M by auto
        have "M1 \<Turnstile>as CNot D"
          using vars_in_M1 true_annots_remove_if_notin_vars[of "M0 @ M2 @ Marked K (i + 1) # []" M1 "CNot D"] `M \<Turnstile>as CNot D` unfolding M lits_of_def by simp
        hence "b \<Turnstile>as CNot (mark - {#La#}) \<and> La \<in># mark" using P b by auto
      }
      moreover {
        assume "tl a @ Propagated La mark # b = M1"
        then obtain c' where "c' @ Propagated La mark # b = M" unfolding M by auto
        hence "b \<Turnstile>as CNot (mark - {#La#}) \<and> La \<in># mark"
          using backtrack.prems(6) unfolding backtrack.hyps(1) trail_conv by blast
      }
      ultimately show "b \<Turnstile>as CNot (mark - {#La#}) \<and> La \<in># mark" by fast
    qed
qed

lemma cdcl_conflicting_is_false:
  assumes "cdcl S S'"
  and "all_decomposition_implies (clauses S) (get_all_marked_decomposition (trail S))"
  and "cdcl_learned_clause S"
  and "\<forall>T. conflicting S = C_Clause T \<longrightarrow> trail S \<Turnstile>as CNot T"
  and "cdcl_M_level_inv S"
  and "no_strange_atm S"
  and "\<forall>L mark a b. a @ Propagated L mark # b = (trail S) \<longrightarrow> (b \<Turnstile>as CNot (mark - {#L#}) \<and> L \<in># mark) "
  and "distinct_cdcl_state S"
  shows "\<forall>T. conflicting S' = C_Clause T \<longrightarrow> trail S' \<Turnstile>as CNot T"
  using assms
proof (induct rule: cdcl_all_induct)
  case (skip M N L C' D k U)
  hence "Propagated L C' # M \<Turnstile>as CNot D" by auto
  also have "L \<notin>#D"
    proof (rule ccontr)
      assume "~ ?thesis"
      hence "- L \<in> lits_of M" using `Propagated L C' # M \<Turnstile>as CNot D` using in_CNot_implies_uminus(2)[of D L "Propagated L C' # M"] by simp
      thus False
        using skip.prems(4) unfolding consistent_interp_def cdcl_M_level_inv_def by auto
    qed
  ultimately show ?case using skip.hyps(1) by (auto intro: true_annots_CNot_lit_of_notin_skip)
next
  case (resolve M N L D k U C)
  show ?case unfolding trail_conv
    proof (intro allI impI)
      fix T
      have "M \<Turnstile>as CNot C" using resolve.prems(6) by fastforce
      also
        have "distinct_mset (D + {#- L#})" using resolve.prems(7) by auto
        hence "-L \<notin># D" unfolding distinct_mset_def by auto
        have "M \<Turnstile>as CNot D"
          proof -
            have a1: "Propagated L (C + {#L#}) # M \<Turnstile>as CNot D"
              using resolve.prems(3) unfolding resolve.hyps(1) by simp
            have f2: "\<forall>l. {#L#} \<noteq> {#- l#} \<or> l \<notin># D"
              using `- L \<notin># D` by force
            obtain mm :: "'a literal multiset set \<Rightarrow> ('a, nat, 'a literal multiset) marked_lit list \<Rightarrow> 'a literal multiset" where
              f3: "\<forall>x0 x1. (\<exists>v2 \<in> x0. \<not> x1 \<Turnstile>a v2) = (mm x0 x1 \<in> x0 \<and> \<not> x1 \<Turnstile>a mm x0 x1)"
              by moura
            have "(\<exists>l. mm (CNot D) M = {#- l#} \<and> l \<in># D) \<longrightarrow> mm (CNot D) M \<notin> CNot D \<or> M \<Turnstile>a mm (CNot D) M"
              using f2 a1 by (metis (no_types) count_single less_not_refl2 marked_lit.sel(2) true_annot_lit_of_notin_skip true_annots_def)
            hence "mm (CNot D) M \<notin> CNot D \<or> M \<Turnstile>a mm (CNot D) M"
              using CNot_def by auto
            thus ?thesis
              using f3 unfolding true_annots_def by metis
          qed
      moreover assume "conflicting (M, N, U, k, C_Clause (remdups_mset (D + C))) = C_Clause T"
      ultimately show "M \<Turnstile>as CNot T" by auto
    qed
qed auto

definition "cdcl_conflicting S \<equiv> (\<forall>T. conflicting S = C_Clause T \<longrightarrow> trail S \<Turnstile>as CNot T) \<and> (\<forall>L mark a b. a @ Propagated L mark # b = (trail S) \<longrightarrow> (b \<Turnstile>as CNot (mark - {#L#}) \<and> L \<in># mark))"

lemma cdcl_conflicting_decomp[dest]:
  assumes "cdcl_conflicting S"
  shows "\<forall>T. conflicting S = C_Clause T \<longrightarrow> trail S \<Turnstile>as CNot T"
  and "\<forall>L mark a b. a @ Propagated L mark # b = (trail S) \<longrightarrow> (b \<Turnstile>as CNot (mark - {#L#}) \<and> L \<in># mark)"
  using assms unfolding cdcl_conflicting_def by blast+

lemma cdcl_conflicting_decomp2[dest]:
  assumes "cdcl_conflicting S"
  shows "conflicting S = C_Clause T \<Longrightarrow> trail S \<Turnstile>as CNot T"
  using assms unfolding cdcl_conflicting_def by blast+

lemma cdcl_conflicting_decomp2'[dest]:
  assumes "cdcl_conflicting (M, N, U, k, C_Clause D)"
  shows "M \<Turnstile>as CNot D"
  using assms unfolding cdcl_conflicting_def by auto

lemma cdcl_conflicting_S0_cdcl[simp]:
  "cdcl_conflicting (S0_cdcl N)"
  unfolding cdcl_conflicting_def by auto
(* includes: lemma 2.10.5.3*)
(*lemma cdcl_all_inv:
  assumes cdcl: "cdcl S S'"
  and 1: "all_decomposition_implies (clauses S) (get_all_marked_decomposition (trail S))"
  and 2: "cdcl_learned_clause S"
  and 3: "\<forall>T. conflicting S = C_Clause T \<longrightarrow> trail S \<Turnstile>as CNot T"
  and 4: "cdcl_M_level_inv S"
  and 5: "no_strange_atm S"
  and 6: "\<forall>L mark a b. a @ Propagated L mark # b = (trail S) \<longrightarrow> (b \<Turnstile>as CNot (mark - {#L#}) \<and> L \<in># mark) "
  and 7: "distinct_cdcl_state S"
  shows "all_decomposition_implies (clauses S') (get_all_marked_decomposition (trail S'))"
  and "cdcl_learned_clause S'"
  and "\<forall>T. conflicting S' = C_Clause T \<longrightarrow> trail S' \<Turnstile>as CNot T"
  and "cdcl_M_level_inv S'"
  and "no_strange_atm S'"
  and "\<forall>L mark a b. a @ Propagated L mark # b = (trail S') \<longrightarrow> (b \<Turnstile>as CNot (mark - {#L#}) \<and> L \<in># mark)"
  and "distinct_cdcl_state S'"
proof -
  show 1: "all_decomposition_implies (clauses S') (get_all_marked_decomposition (trail S'))" using cdcl_propagate_is_conclusion[OF assms(1-6)] .
  show 2: "cdcl_learned_clause S'" using cdcl_learned_clauses[OF assms(1,3)] .
  show 3: "\<forall>T. conflicting S' = C_Clause T \<longrightarrow> trail S' \<Turnstile>as CNot T" using cdcl_conflicting_is_false[OF assms(1-8)] .
  show 4: "cdcl_M_level_inv S'" using cdcl_consistent_inv[OF assms(1,5)] .
  show 5: "no_strange_atm S'"  using  cdcl_no_strange_atm_inv[OF assms(1,6)] .
  show 6: "\<forall>L mark a b. a @ Propagated L mark # b = trail S' \<longrightarrow> b \<Turnstile>as CNot (mark - {#L#}) \<and> L \<in># mark" using cdcl_propagate_is_false[OF assms(1-7)] .
  show 7: "distinct_cdcl_state S'" using distinct_cdcl_state_inv[OF assms(1,8)] .
qed
*)

lemma cdcl_all_inv:
  assumes cdcl: "cdcl S S'"
  and 1: "all_decomposition_implies (clauses S) (get_all_marked_decomposition (trail S))"
  and 2: "cdcl_learned_clause S"
  and 4: "cdcl_M_level_inv S"
  and 5: "no_strange_atm S"
  and 7: "distinct_cdcl_state S"
  and 8: "cdcl_conflicting S"
  shows "all_decomposition_implies (clauses S') (get_all_marked_decomposition (trail S'))"
  and "cdcl_learned_clause S'"
  and "cdcl_M_level_inv S'"
  and "no_strange_atm S'"
  and "distinct_cdcl_state S'"
  and "cdcl_conflicting S'"
proof -
  show S1: "all_decomposition_implies (clauses S') (get_all_marked_decomposition (trail S'))" using cdcl_propagate_is_conclusion[OF cdcl 1 2 _ 4 5] 8 unfolding cdcl_conflicting_def by blast
  show S2: "cdcl_learned_clause S'" using cdcl_learned_clauses[OF assms(1,3)] .
  show S4: "cdcl_M_level_inv S'" using cdcl_consistent_inv[OF assms(1,4)] .
  show S5: "no_strange_atm S'"  using  cdcl_no_strange_atm_inv[OF assms(1,5)] .
  show S7: "distinct_cdcl_state S'" using distinct_cdcl_state_inv[OF assms(1,6)] .
  show S8: "cdcl_conflicting S'" using cdcl_conflicting_is_false[OF cdcl 1 2 _ 4 5 _ 7] 8 cdcl_propagate_is_false[OF cdcl 1 2 _ 4 5] unfolding cdcl_conflicting_def by fast
qed

lemma rtranclp_cdcl_all_inv:
  assumes cdcl: "rtranclp cdcl S S'"
  and 1: "all_decomposition_implies (clauses S) (get_all_marked_decomposition (trail S))"
  and 2: "cdcl_learned_clause S"
  and 4: "cdcl_M_level_inv S"
  and 5: "no_strange_atm S"
  and 7: "distinct_cdcl_state S"
  and 8: "cdcl_conflicting S"
  shows "all_decomposition_implies (clauses S') (get_all_marked_decomposition (trail S'))"
  and "cdcl_learned_clause S'"
  and "cdcl_M_level_inv S'"
  and "no_strange_atm S'"
  and "distinct_cdcl_state S'"
  and "cdcl_conflicting S'"
   using assms
proof (induct rule: rtranclp.induct)
  case (rtrancl_refl S)
    case 1 thus ?case by blast
    case 2 thus ?case by blast
    case 3 thus ?case by blast
    case 4 thus ?case by blast
    case 5 thus ?case by blast
    case 6 thus ?case by blast
next
  case (rtrancl_into_rtrancl S S' S'') note H = this
    case 1 with H(2-7)[OF this(1-6)] show ?case using cdcl_all_inv[OF H(8)] by fast
    case 2 with H(2-7)[OF this(1-6)] show ?case using cdcl_all_inv[OF H(8)] by fast
    case 3 with H(2-7)[OF this(1-6)] show ?case using cdcl_all_inv[OF H(8)] by fast
    case 4 with H(2-7)[OF this(1-6)] show ?case using cdcl_all_inv[OF H(8)] by fast
    case 5 with H(2-7)[OF this(1-6)] show ?case using cdcl_all_inv[OF H(8)] by fast
    case 6 with H(2-7)[OF this(1-6)] show ?case using cdcl_all_inv[OF H(8)] by fast
qed

lemma
  assumes "distinct_mset_set N"
  shows "all_decomposition_implies (clauses (S0_cdcl N)) (get_all_marked_decomposition (fst (S0_cdcl N)))"
  and "cdcl_learned_clause (S0_cdcl N)"
  and "\<forall>T. conflicting (S0_cdcl N) = C_Clause T \<longrightarrow> fst (S0_cdcl N) \<Turnstile>as CNot T"
  and "no_strange_atm (S0_cdcl N)"
  and "consistent_interp (lits_of (fst (S0_cdcl N)))"
  and "\<forall>L mark a b. a @ Propagated L mark # b = (fst (S0_cdcl N)) \<longrightarrow> (b \<Turnstile>as CNot (mark - {#L#}) \<and> L \<in># mark)"
  and "distinct_cdcl_state (S0_cdcl N)"
  and "\<forall>T. conflicting (S0_cdcl N) = C_Clause T \<longrightarrow> atms_of T \<subseteq> atm_of ` lits_of (fst (S0_cdcl N))"
  using assms by auto

  (*prop 2.10.5.5*)
lemma cdcl_only_propagated_vars_unsat:
  assumes marked: "\<forall>x \<in> set M. \<not> is_marked x"
  and DN: "D \<in> N \<union> U" and D: "M \<Turnstile>as CNot D"
  and inv: "all_decomposition_implies N (get_all_marked_decomposition M)"
  and learned_cl: "cdcl_learned_clause (M, N, U, k, C)"
  and atm_incl: "no_strange_atm (M, N, U, k, C)"
  shows "unsatisfiable N"
proof (rule ccontr)
  assume "\<not> unsatisfiable N"
  then obtain I where I: "I \<Turnstile>s N" and cons: "consistent_interp I" and tot: "total_over_m I N" unfolding satisfiable_def by auto
  have "atms_of_m N \<union> atms_of_m U = atms_of_m N"  using atm_incl unfolding total_over_m_def by auto
  hence "total_over_m I (N \<union> U)" using tot unfolding total_over_m_def by auto
  also have "N \<Turnstile>ps U" using learned_cl by auto

  ultimately have I_D: "I \<Turnstile> D"
    using I DN cons unfolding true_clss_clss_def true_clss_def Ball_def by blast

  have l0: "{{#lit_of L#} |L. is_marked L \<and> L \<in> set M} = {}" using marked by auto
  have "atms_of_m (N \<union> (\<lambda>a. {#lit_of a#}) ` set M) = atms_of_m N"
    using atm_incl unfolding lits_of_def no_strange_atm_def by force

  hence "total_over_m I (N \<union> (\<lambda>a. {#lit_of a#}) ` (set M))"
    using tot unfolding total_over_m_def by auto
  hence "I \<Turnstile>s (\<lambda>a. {#lit_of a#}) ` (set M)"
    using all_decomposition_implies_propagated_lits_are_implied[OF inv] cons I
    unfolding true_clss_clss_def l0 by auto
  hence IM: "I \<Turnstile>s (\<lambda>a. {#lit_of a#}) ` set M" by auto
  {
    fix K
    assume "K \<in># D"
    hence "-K \<in> lits_of M"
      using D unfolding true_annots_def Ball_def CNot_def true_annot_def true_cls_def true_lit_def by (metis (mono_tags, lifting) count_single less_not_refl mem_Collect_eq)
    hence " -K \<in> I" using IM true_clss_singleton_lit_of_implies_incl lits_of_def by fastforce
  }
  hence "\<not> I \<Turnstile> D" using cons unfolding true_cls_def true_lit_def consistent_interp_def by auto
  thus False using I_D by blast
qed

(*prop 2.10.5.4*)
text \<open>We have actually a much stronger theorem, namely @{thm all_decomposition_implies_propagated_lits_are_implied}, that show that the only choices we made are marked in the formula\<close>
lemma
  assumes "all_decomposition_implies N (get_all_marked_decomposition M)"
  and "\<forall>m \<in> set M. \<not>is_marked m"
  shows "N \<Turnstile>ps (\<lambda>a. {#lit_of a#}) ` set M"
proof -
  have T: "{{#lit_of L#} |L. is_marked L \<and> L \<in> set M} = {}" using assms(2) by auto
  thus ?thesis
    using all_decomposition_implies_propagated_lits_are_implied[OF assms(1)] unfolding T by simp
qed

(*prop 2.10.5.6*)
lemma conflict_with_false_implies_unsat:
  assumes "cdcl S S'"
  and "conflicting S' = C_Clause {#}"
  and "cdcl_learned_clause S"
  shows "unsatisfiable (clauses S)"
  using assms
proof -
  have "cdcl_learned_clause S'" using cdcl_learned_clauses assms(1,3) by blast
  hence "clauses S' \<Turnstile>p {#}" using assms(2) by auto
  hence "clauses S \<Turnstile>p {#}"
    using cdcl_no_more_clauses[OF assms(1)] by (case_tac S, case_tac S') auto
  thus ?thesis unfolding satisfiable_def true_clss_cls_def by auto
qed

lemma conflict_with_false_implies_terminated:
  assumes "cdcl S S'"
  and "conflicting S = C_Clause {#}"
  shows "False"
  using assms by (induct rule: cdcl_all_induct) auto

subsubsection \<open>No tautology is learned\<close>

lemma learned_clauses_are_not_tautologies:
  assumes "cdcl S S'"
  and "\<forall>s \<in> learned_clauses S. \<not>tautology s"
  and "cdcl_conflicting S"
  and "cdcl_M_level_inv S"
  shows "\<forall>s \<in> learned_clauses S'. \<not>tautology s"
  using assms
proof (induct rule: cdcl_all_induct)
  case (backtrack M N U k D L K i M1 M2)
  have "consistent_interp (lits_of M)" using backtrack.prems(3) by auto
  also have "M \<Turnstile>as CNot (D + {#L#})" using backtrack.prems(2) by auto
  hence "lits_of M \<Turnstile>s CNot (D + {#L#})" using true_annots_true_cls by blast
  ultimately have "\<not>tautology (D + {#L#})" using consistent_CNot_not_tautology by blast
  thus ?case using backtrack(1,5) by simp
qed auto

lemma cdcl_state_decom:
  "S = (trail S, clauses S, learned_clauses S, backtrack_level S, conflicting S)"
  by (case_tac S) auto

definition "final_cdcl_state (S:: 'v cdcl_state)
  \<longleftrightarrow> (trail S \<Turnstile>as clauses S
    \<or> ((\<forall>L \<in> set (trail S). \<not>is_marked L) \<and>
       (\<exists>C \<in> clauses S. trail S \<Turnstile>as CNot C)))"

definition "termination_cdcl_state (S:: 'v cdcl_state) \<longleftrightarrow> (trail S \<Turnstile>as clauses S \<or> ((\<forall>L \<in> atms_of_m (clauses S). L \<in> atm_of ` lits_of (trail S)) \<and> (\<exists>C \<in> clauses S. trail S \<Turnstile>as CNot C)))"

subsection \<open>CDCL Strong Completeness\<close>
fun mapi :: "('a \<Rightarrow> nat \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'b list" where
"mapi _ _ [] = []" |
"mapi f n (x # xs) = f x n # mapi f (n - 1) xs"

lemma mark_not_in_set_mapi[simp]: "L \<notin> set M \<Longrightarrow> Marked L k \<notin> set (mapi Marked i M)"
  by (induct M arbitrary: i) auto

lemma propagated_not_in_set_mapi[simp]: "L \<notin> set M \<Longrightarrow> Propagated L k \<notin> set (mapi Marked i M)"
  by (induct M arbitrary: i) auto

lemma cdcl_can_do_step:
  assumes "consistent_interp (set M)"
  and "distinct M"
  and "atm_of ` (set M) \<subseteq> atms_of_m N"
  shows "rtranclp cdcl (S0_cdcl N) (mapi Marked (length M) M, N, {}, length M, C_True)"
  using assms
proof (induct M)
  case Nil
  thus ?case by auto
next
  case (Cons L M)
  let ?S = "(mapi Marked (length M) M, N, {}, length M, C_True)"
  let ?S' = "(mapi Marked (length (L#M)) (L # M), N, {}, length (L#M), C_True)"
  have "undefined_lit L (mapi Marked (length M) M)"
    using Cons.prems(1,2) unfolding defined_lit_def consistent_interp_def by fastforce
  also have "atm_of L \<in> atms_of_m N" using Cons.prems(3) by auto
  ultimately have "cdcl ?S ?S'" using cdcl.other[OF cdcl_o.decided[OF deciding[of "?S" "mapi Marked (length M) M" N "{}" "length M" L]]] by auto
  also have "consistent_interp (set M)" and "distinct M" and "atm_of ` set M \<subseteq> atms_of_m N"
    using Cons.prems(1-3) unfolding consistent_interp_def by auto
  ultimately show ?case using Cons.hyps(1) by auto
qed

lemma cdcl_strong_completeness:
  assumes "set M \<Turnstile>s N"
  and "consistent_interp (set M)"
  and "distinct M"
  and "atm_of ` (set M) \<subseteq> atms_of_m N"
  shows "rtranclp cdcl (S0_cdcl N) (mapi Marked (length M) M, N, {}, length M, C_True)"
  and "final_cdcl_state (mapi Marked (length M) M, N, {}, length M, C_True)"
proof -
  show "rtranclp cdcl (S0_cdcl N) (mapi Marked (length M) M, N, {}, length M, C_True)" using cdcl_can_do_step assms by auto
  have "lits_of (mapi Marked (length M) M) = set M"
    by (induct M, auto)
  hence "mapi Marked (length M) M \<Turnstile>as N" using assms(1) true_annots_true_cls by metis
  thus "final_cdcl_state (mapi Marked (length M) M, N, {}, length M, C_True)" unfolding final_cdcl_state_def by auto
qed

subsection \<open>Higher level strategy\<close>
subsubsection \<open>Definition\<close>
(*TODO should be common to the CNF transformation*)
definition full :: "('v cdcl_state \<Rightarrow> 'v cdcl_state \<Rightarrow> bool) \<Rightarrow> 'v cdcl_state \<Rightarrow> 'v cdcl_state \<Rightarrow> bool" ("_\<^sup>+\<^sup>\<down>") where
"full transf = (\<lambda>S S'. tranclp transf S S' \<and> (\<forall>S''. \<not> transf S' S''))"

definition full0 :: "('v cdcl_state \<Rightarrow> 'v cdcl_state \<Rightarrow> bool) \<Rightarrow> 'v cdcl_state \<Rightarrow> 'v cdcl_state \<Rightarrow> bool"  ("_\<^sup>\<down>") where
"full0 transf = (\<lambda>S S'. rtranclp transf S S' \<and> (\<forall>S''. \<not> transf S' S''))"

lemma full0_unfold:
  "full0 r S S' \<longleftrightarrow> ((S = S' \<and> (\<forall>S''. \<not> r S' S'')) \<or> full r S S')"
  unfolding full0_def full_def by (auto simp add: Nitpick.rtranclp_unfold)

lemma tranclp_conflict_iff[iff]:
  "full conflict S S' \<longleftrightarrow> (((\<forall>S''. \<not>conflict S' S'') \<and> conflict S S'))"
proof -
  have "tranclp conflict S S' \<Longrightarrow> conflict S S'"
    unfolding full_def by (induct rule: tranclp.induct) force+
  hence "tranclp conflict S S' \<Longrightarrow> conflict S S'" by (meson rtranclpD)
  thus ?thesis unfolding full_def by (meson tranclp.r_into_trancl)
qed

text \<open>We are interested in the stated after applying conflict and propagate\<close>
abbreviation "no_step step S \<equiv> (\<forall>S'. \<not>step S S')"

inductive cdcl_cp :: "'v cdcl_state \<Rightarrow> 'v cdcl_state \<Rightarrow> bool" where
(*TODO intro, not simp*)
conflict'[simp]: "conflict S S' \<Longrightarrow> cdcl_cp S S'" |
propagate_conf': "propagate S S' \<Longrightarrow> no_step conflict S \<Longrightarrow> conflict S' S'' \<Longrightarrow> cdcl_cp S S''" |
propagate_no_conf': "propagate S S' \<Longrightarrow> no_step conflict S \<Longrightarrow>  no_step conflict S' \<Longrightarrow> cdcl_cp S S'"

lemma cdcl_cp_conflicting_not_empty[simp]: "conflicting S = C_Clause D  \<Longrightarrow> \<not>cdcl_cp S S'"
proof
  assume "cdcl_cp S S'" and "conflicting S = C_Clause D"
  thus False by (induct rule: cdcl_cp.induct) auto
qed

(*TODO Mark as [dest]?*)
lemma no_step_cdcl_cp_no_conflict_no_propagate:
  assumes "no_step cdcl_cp S"
  shows "no_step conflict S" and "no_step propagate S"
  using assms conflict' apply blast
  by (meson assms conflict' propagate_conf' propagate_no_conf')

text \<open>CDCL with the reasonable strategy: we fully propagate the conflict and propagate, then we apply any other possible rule @{term "cdcl_o S S'"} and re-apply conflict and propagate @{term "full0 cdcl_cp S' S''"}\<close>
inductive cdcl_s :: "'v cdcl_state \<Rightarrow> 'v cdcl_state \<Rightarrow> bool" where
conflict': "full cdcl_cp S S' \<Longrightarrow> cdcl_s S S'" |
(*TODO replace no_step propagate S \<Longrightarrow> no_step conflict S by no_step cdcl_cp S*)
other': "cdcl_o S S'  \<Longrightarrow> no_step propagate S \<Longrightarrow> no_step conflict S \<Longrightarrow> full0 cdcl_cp S' S'' \<Longrightarrow> cdcl_s S S''"

subsubsection \<open>Invariants\<close>
text \<open>These are the same invariants as before, but lifted\<close>
lemma cdcl_cp_learned_clause_inv:
  assumes "cdcl_cp S S'"
  shows "learned_clauses S = learned_clauses S'"
  using assms by (induct rule: cdcl_cp.induct) fastforce+

lemma rtranclp_cdcl_cp_learned_clause_inv:
  assumes "cdcl_cp\<^sup>*\<^sup>* S S'"
  shows "learned_clauses S = learned_clauses S'"
  using assms by (induct rule: rtranclp.induct) (fastforce dest: cdcl_cp_learned_clause_inv)+

lemma tranclp_cdcl_cp_learned_clause_inv:
  assumes "cdcl_cp\<^sup>+\<^sup>+ S S'"
  shows "learned_clauses S = learned_clauses S'"
  using assms by (simp add: rtranclp_cdcl_cp_learned_clause_inv tranclp_into_rtranclp)

lemma cdcl_cp_consistent_inv:
  assumes "cdcl_cp S S'"
  and "cdcl_M_level_inv S"
  shows "cdcl_M_level_inv S'"
  using assms
proof (induct rule: cdcl_cp.induct)
  case (conflict')
  thus ?case using cdcl_consistent_inv cdcl.conflict by blast
next
  case (propagate_conf' S S' S'')
  have "cdcl S' S''"
    using propagate_conf'.hyps(3) conflict by blast
  thus "cdcl_M_level_inv S''"
    using propagate_conf'.prems(1) propagate_conf'.hyps(1)  cdcl_consistent_inv propagate by blast
next
  case (propagate_no_conf' S S')
  thus ?case  using cdcl_consistent_inv propagate by blast
qed

lemma full_cdcl_cp_consistent_inv:
  assumes "full cdcl_cp S S'"
  and "cdcl_M_level_inv S"
  shows "cdcl_M_level_inv S'"
  using assms unfolding full_def
proof -
  have "cdcl_cp\<^sup>+\<^sup>+ S S'" and "cdcl_M_level_inv S" using assms unfolding full_def by auto
  thus ?thesis by (induct rule: tranclp.induct) (blast intro: cdcl_cp_consistent_inv)+
qed

lemma rtranclp_cdcl_cp_consistent_inv:
  assumes "rtranclp cdcl_cp S S'"
  and "cdcl_M_level_inv S"
  shows "cdcl_M_level_inv S'"
  using assms unfolding full_def
  by (induction rule: rtranclp_induct) (blast intro: cdcl_cp_consistent_inv)+

lemma cdcl_s_consistent_inv:
  assumes "cdcl_s S S'"
  and "cdcl_M_level_inv S"
  shows "cdcl_M_level_inv S'"
  using assms apply (induct rule: cdcl_s.induct)
  unfolding full0_unfold by (blast intro: cdcl_consistent_inv full_cdcl_cp_consistent_inv cdcl.other)+

lemma rtranclp_cdcl_s_consistent_inv:
  assumes "cdcl_s\<^sup>*\<^sup>* S S'"
  and "cdcl_M_level_inv S"
  shows "cdcl_M_level_inv S'"
  using assms by (induction) (auto dest!: cdcl_s_consistent_inv)

lemma cdcl_o_no_more_clauses:
  assumes "cdcl_o S S'"
  shows "clauses S = clauses S'"
  using assms by (induct rule: cdcl_o_induct) auto

lemma tranclp_cdcl_o_no_more_clauses:
  assumes "cdcl_o\<^sup>+\<^sup>+ S S'"
  shows "clauses S = clauses S'"
  using assms by (induct rule: tranclp.induct) (auto dest: cdcl_o_no_more_clauses)

lemma rtranclp_cdcl_o_no_more_clauses:
  assumes "cdcl_o\<^sup>*\<^sup>* S S'"
  shows "clauses S = clauses S'"
  using assms by (induct rule: rtranclp.induct) (auto dest: cdcl_o_no_more_clauses)

lemma cdcl_cp_no_more_clauses:
  assumes "cdcl_cp S S'"
  shows "clauses S = clauses S'"
  using assms by (induct rule: cdcl_cp.induct) auto

lemma tranclp_cdcl_cp_no_more_clauses:
  assumes "cdcl_cp\<^sup>+\<^sup>+ S S'"
  shows "clauses S = clauses S'"
  using assms by (induct rule: tranclp.induct) (auto dest: cdcl_cp_no_more_clauses)

lemma cdcl_s_no_more_clauses:
  assumes "cdcl_s S S'"
  shows "clauses S = clauses S'"
  using assms
  apply (induct rule: cdcl_s.induct)
  unfolding full_def full0_def apply (blast dest: tranclp_cdcl_cp_no_more_clauses tranclp_cdcl_o_no_more_clauses)
  by (metis cdcl_o_no_more_clauses rtranclp_unfold tranclp_cdcl_cp_no_more_clauses)

lemma rtranclp_cdcl_s_no_more_clauses:
  assumes "cdcl_s\<^sup>*\<^sup>* S S'"
  shows "clauses S = clauses S'"
  using assms
  apply (induct rule: rtranclp.induct, simp)
  using cdcl_s_no_more_clauses by fast

text \<open>This theorem can be seen a a termination theorem for @{term cdcl_cp}.\<close>
lemma always_exists_full_cdcl_cp_step:
  assumes "finite (clauses S)"
  and "no_strange_atm S"
  shows "\<exists>S''. full0 cdcl_cp S S''"
  using assms
proof (induct "card (atms_of_m (clauses S) - atm_of `lits_of (trail S))" arbitrary: S)
  case 0 note card = this(1) and finite = this(2) and alien = this(3)
  hence atm: "atms_of_m (clauses S) = atm_of ` lits_of (trail S)"
    unfolding no_strange_atm_def by (metis (no_types, lifting) atms_of_m_finite card_Diff_subset
      card_seteq diff_is_0_eq finite_subset)
  { assume a: "\<exists>S'. conflict S S'"
    then obtain S' where S': "conflict S S'" by metis
    hence "\<forall>S''. \<not>cdcl_cp S' S''" by auto
    hence ?case using a S' cdcl_cp.conflict' unfolding full0_def by blast
  }
  also {
    assume a: "\<exists>S'. propagate S S'"
    then obtain S' where "propagate S S'" by blast
    then obtain M N U k C L where S: "S = (M, N, U, k, C_True)"
    and S': "S' = (Propagated L (C + {#L#}) # M, N, U, k, C_True)"
    and "C + {#L#} \<in> N \<union> U"
    and "M \<Turnstile>as CNot C"
    and "undefined_lit L M"
    using propagate by (auto)
    have "atms_of_m U \<subseteq> atms_of_m N" using alien unfolding S by auto
    hence "atm_of L \<in> atms_of_m (clauses S)"
      using `C + {#L#} \<in> N \<union> U` image_Un unfolding S atms_of_m_def by (fastforce simp add: atms_of_def)
    hence False using `undefined_lit L M` unfolding atm unfolding S lits_of_def by (auto simp add: defined_lit_map)
  }
  ultimately show ?case by (metis cdcl_cp.cases full0_def rtranclp.rtrancl_refl)
next
  case (Suc n) note IH = this(1) and card = this(2) and finite = this(3) and alien = this(4)
  { assume a: "\<exists>S'. conflict S S'"
    then obtain S' where S': "conflict S S'" by metis
    hence "\<forall>S''. \<not>cdcl_cp S' S''" by auto
    hence ?case  unfolding full0_def Ex_def using S' cdcl_cp.conflict' by blast
  }
  moreover {
    assume a: "\<exists>S'. propagate S S'" and no_confl: "no_step conflict S"
    then obtain S' where propagate: "propagate S S'" by blast
    then obtain M N U k C L where S: "S = (M, N, U, k, C_True)"
    and S': "S' = (Propagated L (C + {#L#}) # M, N, U, k, C_True)"
    and "C + {#L#} \<in> N \<union> U"
    and "M \<Turnstile>as CNot C"
    and "undefined_lit L M" by auto
    hence "atm_of L \<notin> atm_of ` lits_of M" unfolding lits_of_def by (auto simp add:  defined_lit_map)
    (*TODO clean also for not-finally*)
    moreover 
      have "no_strange_atm S'" using alien propagate
        by (meson cdcl.propagate cdcl_no_strange_atm_inv)
      hence "atm_of L \<in> atms_of_m N" unfolding S' by auto
      hence "\<And>A. {atm_of L} \<subseteq> atms_of_m N - A \<or> atm_of L \<in> A" by force
    moreover have "Suc n - card {atm_of L} = n" by simp
    moreover have "card (atms_of_m N - atm_of ` lits_of M) = Suc n"
     using card unfolding S S' trail_conv  by simp
    ultimately 
      have "card (atms_of_m N - atm_of ` insert L (lits_of M)) = n"
        by (metis (no_types) Diff_insert card_Diff_subset finite.emptyI finite.insertI image_insert)
      hence "n = card (atms_of_m (clauses S') - atm_of ` lits_of (trail S'))" 
        using card unfolding S S' trail_conv by simp

    moreover have "finite (clauses S')" using finite unfolding S S' by auto
    ultimately have a1: "Ex (full0 cdcl_cp S')" using IH `no_strange_atm S'` by blast
    have ?case
      proof -
        obtain S'' :: "'a cdcl_state" where
          ff1: "cdcl_cp\<^sup>*\<^sup>* S' S'' \<and> no_step cdcl_cp S''"
          using a1 unfolding full0_def by blast
        have "cdcl_cp\<^sup>*\<^sup>* S S''"
          using ff1 cdcl_cp.intros(2)[OF propagate no_confl] cdcl_cp.intros(3)[OF propagate no_confl] by (metis (no_types) cdcl_cp.simps converse_rtranclpE converse_rtranclp_into_rtranclp)
        hence "\<exists>S''. cdcl_cp\<^sup>*\<^sup>* S S'' \<and> (\<forall>S'''. \<not> cdcl_cp S'' S''')"
          using ff1 by blast
        thus ?thesis unfolding full0_def
          by meson
      qed

    }
  ultimately show ?case unfolding full0_def by (metis cdcl_cp.cases rtranclp.rtrancl_refl)
qed

subsubsection \<open>Literal of highest level in conflicting clauses\<close>
text \<open>One important property of the cdcl with strategy is that, whenever a conflict takes place, there is at least a literal of level k involved (except if we have derived the false clause). The reason is that we apply conflicts as soon as possible\<close>
abbreviation no_clause_is_false :: "'v cdcl_state \<Rightarrow> bool" where
"no_clause_is_false \<equiv> \<lambda>S. (conflicting S = C_True \<longrightarrow> (\<forall>D \<in> clauses S \<union> learned_clauses S. \<not>trail S \<Turnstile>as CNot D))"

abbreviation conflict_is_false_with_level :: "'v cdcl_state \<Rightarrow> bool" where
"conflict_is_false_with_level S' \<equiv> \<forall>D. conflicting S' = C_Clause D \<longrightarrow> D \<noteq> {#} \<longrightarrow> (\<exists>L \<in># D. get_level L (trail S') = backtrack_level S')"

lemma not_conflict_not_any_negated_clauses:
  assumes "\<forall> S'. \<not>conflict S S'"
  shows "no_clause_is_false S"
  using assms by (fastforce simp add: conflict.simps)

lemma cdcl_cp_not_any_negated_clauses:
  assumes "cdcl_cp S S'"
  shows "no_clause_is_false S'"
  using assms
  by (induct rule: cdcl_cp.induct)
     (fastforce simp add: not_conflict_not_any_negated_clauses conflict.simps)+

lemma tranclp_cdcl_cp_not_any_negated_clauses:
  assumes "tranclp cdcl_cp S S'"
  shows "no_clause_is_false S'"
  using assms apply (induct rule: tranclp.induct)
  using cdcl_cp_not_any_negated_clauses by fast+

lemma rtranclp_cdcl_cp_not_any_negated_clauses:
  assumes "rtranclp cdcl_cp S S'"
  and "no_clause_is_false S"
  shows "no_clause_is_false S'"
  using rtranclp_unfold[of cdcl_cp S] assms tranclp_cdcl_cp_not_any_negated_clauses[of S S'] by fastforce

lemma full_cdcl_cp_not_any_negated_clauses:
  assumes "full cdcl_cp S S'"
  shows "no_clause_is_false S'"
  by (metis (mono_tags, lifting) assms full_def tranclp_cdcl_cp_not_any_negated_clauses)


lemma full0_cdcl_cp_not_any_negated_clauses:
  assumes "full0 cdcl_cp S S'"
  shows "no_clause_is_false S'"
  using assms unfolding full0_def
  by (metis (mono_tags, lifting) cdcl_cp.conflict' not_conflict_not_any_negated_clauses)

lemma cdcl_s_not_non_negated_clauses:
  assumes "cdcl_s S S'"
  shows "no_clause_is_false S'"
  using assms apply (induct rule: cdcl_s.induct)
  using full_cdcl_cp_not_any_negated_clauses full0_cdcl_cp_not_any_negated_clauses by metis+


(*TODO Move*)
lemma get_rev_level_can_skip_correctly_ordered:
  assumes "no_dup M"
  and "atm_of L \<notin> atm_of ` (lits_of M)"
  and "get_all_levels_of_marked M = rev [Suc 0..<Suc (length (get_all_levels_of_marked M))]"
  shows "get_rev_level L 0 (rev M @ K) = get_rev_level L (length (get_all_levels_of_marked M)) K"
  using assms
proof (induct M arbitrary: K)
  case Nil
  thus ?case by simp
next
  case (Cons a M K)
  show ?case
    proof (case_tac a)
      fix L' i
      assume a: "a = Marked L' i"
      have i: "i = Suc (length (get_all_levels_of_marked M))"
      and "get_all_levels_of_marked M = rev [Suc 0..<Suc (length (get_all_levels_of_marked M))]"
        using Cons.prems(3) unfolding a by auto
      hence "get_rev_level L 0 (rev M @ (a # K)) = get_rev_level L (length (get_all_levels_of_marked M)) (a # K)" using Cons.hyps Cons.prems by auto
      thus ?case using Cons.prems(2) unfolding a i by auto
    next
      fix L' D
      assume a: "a = Propagated L' D"
      have "get_all_levels_of_marked M = rev [Suc 0..<Suc (length (get_all_levels_of_marked M))]"
        using Cons.prems(3) unfolding a by auto
      hence "get_rev_level L 0 (rev M @ (a # K)) = get_rev_level L (length (get_all_levels_of_marked M)) (a # K)" using Cons by auto
      thus ?case using Cons.prems(2) unfolding a by auto
    qed
qed

lemma cdcl_s_conflict_ex_lit_of_max_level:
  assumes "cdcl_cp S S'"
  and "no_clause_is_false S"
  and "cdcl_M_level_inv S"
  shows "conflict_is_false_with_level S'"
  using assms
proof (induct rule: cdcl_cp.induct)
  case conflict'
  thus ?case by auto
next
  case propagate_no_conf'
  thus ?case by auto
next
  case (propagate_conf' S S' S'') note propagate = this(1)
  obtain M N U k C L where S: "S = (M, N, U, k, C_True)"
  and S': "S' = (Propagated L (C + {#L#}) # M, N, U, k, C_True)"
  and "C + {#L#} \<in> N \<union> U"
  and "M \<Turnstile>as CNot C"
  and undef: "undefined_lit L M"
    using propagate by auto
  let ?M = "Propagated L (C + {#L#}) # M"
  have "atm_of L \<notin> atm_of ` (lits_of M)"
    using undef by (auto simp add: Marked_Propagated_in_iff_in_lits_of atm_of_eq_atm_of)
  hence 1: "get_level L (Propagated L (C + {#L#}) # M) = backtrack_level S'"
    using propagate_conf'.prems(2) unfolding S' S
    by (auto simp add: get_rev_level_can_skip_correctly_ordered cdcl_M_level_inv_def)
  obtain D'' where
    D'': "D'' \<in> N \<union> U"
    and MD'': "?M \<Turnstile>as CNot D''"
    and S'': "S'' = (Propagated L (C + {#L#}) # M, N, U, k, C_Clause D'')" using propagate_conf'.hyps unfolding S' by (auto simp add: conflict.simps)
  have "\<not>M \<Turnstile>as CNot D''" using propagate_conf'.prems(1) MD'' D'' unfolding S by simp
  hence 2: "-L \<in># D''"
    using cdcl_consistent_inv[OF cdcl.propagate[OF propagate] propagate_conf'.prems(2)]
    true_annots_lit_of_notin_skip[OF MD''] unfolding S' by fastforce
  show ?case using propagate_conf'.hyps(2) 1 2 unfolding S S' S'' by auto
qed

lemma no_chained_conflict:
  assumes "conflict S S'"
  and "conflict S' S''"
  shows False
  using assms by auto

lemma rtranclp_cdcl_co_conflict_ex_lit_of_max_level:
  assumes "rtranclp cdcl_cp S S'"
  and "no_clause_is_false S"
  and "conflict_is_false_with_level S"
  and "cdcl_M_level_inv S"
  shows "conflict_is_false_with_level S'"
  using assms
proof (induct rule: rtranclp.induct)
  case rtrancl_refl
  thus ?case by fast
next
  case (rtrancl_into_rtrancl S S' S'')
  hence "\<forall>T. conflicting S' = C_True \<longrightarrow> (\<forall>D \<in> clauses S' \<union> learned_clauses S'. \<not>trail S' \<Turnstile>as CNot D)"
    using rtranclp_cdcl_cp_not_any_negated_clauses[OF rtrancl_into_rtrancl.hyps(1)] by presburger
  also have "cdcl_M_level_inv S'"
    using rtranclp_cdcl_cp_consistent_inv rtrancl_into_rtrancl.hyps(1) rtrancl_into_rtrancl.prems(3)
    by blast
  ultimately show ?case
    using cdcl_s_conflict_ex_lit_of_max_level[OF rtrancl_into_rtrancl.hyps(3)] by meson
qed

lemma tranclp_cdcl_co_conflict_ex_lit_of_max_level:
  assumes "cdcl_cp\<^sup>+\<^sup>+ S S'"
  and "no_clause_is_false S"
  and "cdcl_M_level_inv S"
  shows "conflict_is_false_with_level S'"
  using assms
proof (induct rule: tranclp.induct)
  case r_into_trancl
  thus ?case using cdcl_s_conflict_ex_lit_of_max_level by blast
next
  case (trancl_into_trancl S S' S'')
  hence "\<forall>T. conflicting S' = C_True \<longrightarrow> (\<forall>D \<in> clauses S' \<union> learned_clauses S'. \<not>trail S' \<Turnstile>as CNot D)"
    using tranclp_cdcl_cp_not_any_negated_clauses[OF trancl_into_trancl.hyps(1)] by presburger
  also have "cdcl_M_level_inv S'"
    using rtranclp_cdcl_cp_consistent_inv[of S S'] trancl_into_trancl.hyps(1) trancl_into_trancl.prems(2) rtranclp_unfold[of cdcl_cp S S'] by auto
  ultimately show ?case
    using cdcl_s_conflict_ex_lit_of_max_level[OF trancl_into_trancl.hyps(3)] by meson
qed

subsubsection \<open>Literal of highest level in marked literals\<close>
definition mark_is_false_with_level :: "'v cdcl_state \<Rightarrow> nat \<Rightarrow> bool" where
"mark_is_false_with_level S' n \<equiv> \<forall>D M1 M2 L. get_maximum_possible_level M1 < n \<longrightarrow> M1 @ Propagated L D # M2 = trail S' \<longrightarrow> D - {#L#} \<noteq> {#} \<longrightarrow> (\<exists>L. L \<in># D \<and> get_level L (trail S') = get_maximum_possible_level M1)"

definition no_more_propagation_to_do:: "'v cdcl_state \<Rightarrow> bool" where
"no_more_propagation_to_do S \<equiv> \<forall>D M M' L. D + {#L#} \<in> clauses S \<union> learned_clauses S \<longrightarrow> trail S = M' @ M \<longrightarrow> M \<Turnstile>as CNot D \<longrightarrow> undefined_lit L M \<longrightarrow> get_maximum_possible_level M < backtrack_level S \<longrightarrow> (\<exists>L. L \<in># D \<and> get_level L (trail S) = get_maximum_possible_level M)"

lemma propagate_no_more_propagation_to_do:
  assumes propagate: "propagate S S'"
  and H: "no_more_propagation_to_do S"
  and M: "cdcl_M_level_inv S"
  shows "no_more_propagation_to_do S'"
  using assms
proof -
  obtain M N U k C L where S: "S = (M, N, U, k, C_True)"
  and S': "S' = (Propagated L (C + {#L#}) # M, N, U, k, C_True)"
  and "C + {#L#} \<in> N \<union> U"
  and "M \<Turnstile>as CNot C"
  and "undefined_lit L M"
    using propagate by auto
  let ?M' = "Propagated L (C + {#L#}) # M"
  show ?thesis unfolding no_more_propagation_to_do_def
    proof (intro allI impI)
      fix D M1 M2 L'
      assume D_L: "D + {#L'#} \<in> clauses S' \<union> learned_clauses S'"
      and "trail S' = M2 @ M1"
      and get_max: "get_maximum_possible_level M1 < backtrack_level S'"
      and "M1 \<Turnstile>as CNot D"
      and undef: "undefined_lit L' M1"
      have "tl M2 @ M1 = trail S \<or> (M2 = [] \<and> M1 = Propagated L (C + {#L#}) # M)" using `trail S' = M2 @ M1` unfolding S' S by auto (metis list.sel(3) tl_append2)
      also {
        assume "tl M2 @ M1 = trail S"
        also have "D + {#L'#} \<in> clauses S \<union> learned_clauses S" using D_L unfolding S S' by auto
        moreover have "get_maximum_possible_level M1 < backtrack_level S"
          using get_max unfolding S S' by auto
        ultimately obtain L' where "L' \<in># D" and
          "get_level L' (trail S) = get_maximum_possible_level M1"
          using H `M1 \<Turnstile>as CNot D` undef unfolding no_more_propagation_to_do_def by metis
        also
          { have "cdcl_M_level_inv S'"
              using cdcl_consistent_inv[OF _ M] cdcl.propagate[OF propagate] by blast
            hence "no_dup ?M'" unfolding S' by auto
            also have "atm_of L' \<in> atm_of ` (lits_of M1)"
              using `L' \<in># D` `M1 \<Turnstile>as CNot D` by (metis atm_of_uminus image_eqI in_CNot_implies_uminus(2))
            hence "atm_of L' \<in> atm_of ` (lits_of M)"
              using `tl M2 @ M1 = trail S`[symmetric] unfolding S by auto
            ultimately have "atm_of L \<noteq> atm_of L'" unfolding lits_of_def by auto
        }
        ultimately have "\<exists>L' \<in># D. get_level L' (trail S') = get_maximum_possible_level M1"
          unfolding S S' trail_conv by auto
      }
      moreover {
        assume "M2 = []" and M1: "M1 = Propagated L (C + {#L#}) # M"
        have "cdcl_M_level_inv S'"
          using cdcl_consistent_inv[OF _ M] cdcl.propagate[OF propagate] by blast
        hence "get_all_levels_of_marked (trail S') = rev ([Suc 0..<(Suc 0+k)])" unfolding S' by auto
        hence "get_maximum_possible_level M1 = backtrack_level S'"
          using get_maximum_possible_level_max_get_all_levels_of_marked[of M1]
          unfolding S' M1 by (auto intro: Max_eqI)
        hence False using get_max by auto
      }
      ultimately show "\<exists>L. L \<in># D \<and> get_level L (trail S') = get_maximum_possible_level M1" by fast
   qed
qed

lemma conflict_no_more_propagation_to_do:
  assumes conflict: "conflict S S'"
  and H: "no_more_propagation_to_do S"
  and M: "cdcl_M_level_inv S"
  shows "no_more_propagation_to_do S'"
  using assms unfolding no_more_propagation_to_do_def conflict.simps by fast

lemma cdcl_cp_no_more_propagation_to_do:
  assumes conflict: "cdcl_cp S S'"
  and H: "no_more_propagation_to_do S"
  and M: "cdcl_M_level_inv S"
  shows "no_more_propagation_to_do S'"
  using assms
  proof (induct rule: cdcl_cp.induct)
  case (conflict' S S')
  thus ?case using conflict_no_more_propagation_to_do[of S S'] by blast
next
  case (propagate_conf' S S' S'') note S = this
  have 1: "no_more_propagation_to_do S'"  "cdcl_M_level_inv S'"
    using propagate_no_more_propagation_to_do[of S S'] cdcl_consistent_inv[OF cdcl.propagate[of S S']] S(1,4,5) by blast+
  show ?case
    apply (rule conflict_no_more_propagation_to_do[of S' S''])
    using S(3) conflict_no_more_propagation_to_do[of S' S''] cdcl_consistent_inv[OF cdcl.conflict[of S' S'']] 1 by metis+
next
  case (propagate_no_conf' S S')
  thus ?case
    using propagate_no_more_propagation_to_do[of S S'] cdcl_consistent_inv[OF cdcl.propagate[of S S']] by blast+
qed

lemma cdcl_cp_no_moreste_no_more_propagation_to_do:
  fixes S :: "'a cdcl_state"
  assumes termi: "\<forall>S'. \<not>cdcl_cp S S'"
  and H: "no_more_propagation_to_do S"
  and M: "cdcl_M_level_inv S"
  shows "no_more_propagation_to_do S"
  using assms unfolding no_more_propagation_to_do_def by blast

lemma cdcl_then_exists_cdcl_s_step:
  assumes o: "cdcl_o S S'"
  and alien: "no_strange_atm S"
  and finite: "finite (clauses S)"
  shows "\<exists>S'. cdcl_s S S'"
proof -
  obtain pp :: "('a, nat, 'a literal multiset) marked_lit list \<times> 'a literal multiset set \<times> 'a literal multiset set \<times> nat \<times> 'a literal multiset conflicting_clause \<Rightarrow> ('a, nat, 'a literal multiset) marked_lit list \<times> 'a literal multiset set \<times> 'a literal multiset set \<times> nat \<times> 'a literal multiset conflicting_clause" where
    f4: "\<And>p. \<not> finite (clauses p) \<or> \<not> no_strange_atm p \<or> full0 cdcl_cp p (pp p)"
    by (metis (no_types) always_exists_full_cdcl_cp_step) (* 166 ms *)
  hence "full0 cdcl_cp S' (pp S')"
    using assms by (metis (no_types) cdcl_no_more_clauses cdcl_no_strange_atm_inv other) (* 90 ms *)
  thus ?thesis
    using f4 assms by (metis (no_types) cdcl_cp.conflict' cdcl_s.conflict' full0_unfold other' propagate_conf' propagate_no_conf') (* 590 ms *)
qed

(*TODO Move*)
lemma Max_n_upt: "Max (insert 0 {Suc 0..<n}) = n - Suc 0"
proof (induct n)
  case 0
  thus ?case by simp
next
  case (Suc n) note IH = this
  have i: "insert 0 {Suc 0..<Suc n} = insert 0 {Suc 0..< n} \<union> {n}" by auto
  show ?case using IH unfolding i by auto
qed

lemma backtrack_ex_decomp:
  assumes M_l: "cdcl_M_level_inv S"
  and i_S: "i < backtrack_level S"
  shows "\<exists>K M1 M2. (Marked K (i + 1) # M1, M2) \<in> set (get_all_marked_decomposition (trail S))"
proof -
  let ?M = "trail S"
  obtain c c' K where M: "?M = c @ Marked K (i+1) # c'"
    proof (rule ccontr)
      assume "\<And>c K M2. ?M = c @ Marked K (i + 1) # M2 \<Longrightarrow> thesis"
      and "\<not> thesis"
      hence "\<And>c K M2. ?M \<noteq> c @ Marked K (i + 1) # M2" by auto
      hence i: "i + 1 \<notin> set (get_all_levels_of_marked ?M)"
        apply (induction "?M" arbitrary: S)
          apply auto[1]
        apply (case_tac a, auto)
           apply (fast intro: append_Cons)
        by (metis append_Cons)+
      have g: "get_all_levels_of_marked (trail S) = rev [Suc 0..<Suc (backtrack_level S)]" using M_l unfolding cdcl_M_level_inv_def by (simp del: upt.simps)
      show False using i i_S unfolding g by (simp del: upt.simps)
    qed
  obtain M1 M2 where "(Marked K (i + 1) # M1, M2) \<in> set (get_all_marked_decomposition (trail S))"
    unfolding M apply (induct c)
      apply simp
      apply blast
    apply (case_tac a, auto)
    by (metis apsnd_conv get_all_marked_decomposition_never_empty list.collapse set_ConsD)
  thus ?thesis by blast
qed

lemma backtrack_no_decomp:
  assumes S: "S = (M, N, U, k, C_Clause (D + {#L#}))"
  and L: "get_level L M = k"
  and D: "get_maximum_level D M < k"
  and M_L: "cdcl_M_level_inv S"
  shows "\<exists>S'. cdcl_o S S'"
proof -
  have L_D: "get_level L M = get_maximum_level (D + {#L#}) M" using L D by (simp add: get_maximum_level_plus)
  let ?i = "get_maximum_level D M"
  obtain K M1 M2 where K: "(Marked K (?i + 1) # M1, M2) \<in> set (get_all_marked_decomposition M)" using backtrack_ex_decomp[OF M_L, of ?i] D unfolding S by auto
  show ?thesis using cdcl_o.backtrack[OF backtracking[OF S K L L_D]] by blast
qed


lemma cdcl_s_normal_forms:
  assumes termi: "\<forall>S'. \<not>cdcl_s S S'"
  and decomp: "all_decomposition_implies (clauses S) (get_all_marked_decomposition (trail S))"
  and learned: "cdcl_learned_clause S"
  and level_inv: "cdcl_M_level_inv S"
  and alien: "no_strange_atm S"
  and no_dup: "distinct_cdcl_state S"
  and confl: "cdcl_conflicting S"
  and finite: "finite (clauses S)"
  and confl_k: "conflict_is_false_with_level S"
  shows "(conflicting S = C_Clause {#} \<and> unsatisfiable (clauses S)) \<or> (conflicting S = C_True \<and> trail S \<Turnstile>as clauses S)"
proof -
  let ?M = "trail S"
  let ?N = "clauses S"
  let ?k = "backtrack_level S"
  let ?U = "learned_clauses S"
  have "conflicting S = C_Clause {#} \<or> conflicting S = C_True \<or> (\<exists>D L. conflicting S = C_Clause (D + {#L#}))"
    apply (case_tac "conflicting S", auto)
    by (case_tac x2, auto)
  also {
    assume "conflicting S = C_Clause {#}"
    hence "unsatisfiable (clauses S)" using assms(3) unfolding cdcl_learned_clause_def by (metis (no_types, lifting) Un_insert_right atms_of_empty satisfiable_def sup_bot.right_neutral total_over_m_insert total_over_set_empty true_cls_empty true_clss_cls_def)
  }
  moreover {
    assume "conflicting S = C_True"
    { assume "\<not>?M \<Turnstile>as ?N"
      have "atm_of ` (lits_of ?M) = atms_of_m ?N" (is "?A = ?B")
        proof
          show "?A \<subseteq> ?B" using alien by auto
          show "?B \<subseteq> ?A"
            proof (rule ccontr)
              assume "\<not>?B \<subseteq> ?A"
              then obtain l where "l \<in> ?B" and "l \<notin> ?A" by auto
              hence "undefined_lit (Pos l) ?M" using `l \<notin> ?A` unfolding lits_of_def by (auto simp add: defined_lit_map)
              hence "\<exists>S'. cdcl_o S S'" using cdcl_o.decided decided.intros `l \<in> ?B` by (metis `conflicting S = C_True` cdcl_state_decom literal.sel(1))
              thus False using termi cdcl_then_exists_cdcl_s_step[OF _ alien finite] by metis
            qed
          qed
        obtain D where "\<not> ?M \<Turnstile>a D" and "D \<in> ?N"
           using `~?M \<Turnstile>as ?N` unfolding lits_of_def true_annots_def Ball_def by auto
        have "atms_of D \<subseteq> atm_of ` (lits_of ?M)"
          using `D \<in> ?N` unfolding `atm_of \` (lits_of ?M) = atms_of_m ?N` atms_of_m_def by (auto simp add: atms_of_def)
        hence a1: "atm_of ` set_mset D \<subseteq> atm_of ` lit_of ` set (trail S)"
          by (auto simp add: atms_of_def lits_of_def)
        have "?M \<Turnstile>as CNot D"
        (*TODO Try to find a better proof*)
          proof -
            { fix mm :: "'a literal multiset"
              have ff1: "\<And>l la. (l::'a literal) \<noteq> la \<or> count {#l#} la = Suc 0"
                by simp (* 3 ms *)
              have ff2: "\<And>a. a \<notin> atm_of ` set_mset D \<or> a \<in> atm_of ` lit_of ` set (trail S)"
                using a1 by (meson subsetCE) (* 6 ms *)
              have ff3: "\<And>l. l \<notin> lit_of ` set (trail S) \<or> l \<notin># D"
                using `\<not> ?M \<Turnstile>a D` unfolding true_annot_def Ball_def lits_of_def true_cls_def by (meson true_lit_def) (* 6 ms *)
              have ff4: "\<And>l. is_pos l \<or> Pos (atm_of l::'a) = - l"
                by (metis Neg_atm_of_iff uminus_Neg) (* 6 ms *)
              have "\<And>l. is_neg l \<or> Neg (atm_of l::'a) = - l"
                by (metis Pos_atm_of_iff uminus_Pos) (* 13 ms *)
              hence ff5: "\<And>l. - l \<notin># D \<or> l \<in> lit_of ` set (trail S)"
                using ff4 ff3 ff2 by (metis (no_types) Neg_atm_of_iff Pos_atm_of_iff atms_of_s_def in_atms_of_s_decomp mem_set_mset_iff) (* 236 ms *)
              have "\<And>l. - (- (l::'a literal)) = l"
                by simp (* 0.0 ms *)
              hence "(\<exists>l. mm \<notin> {{#- l#} |l. l \<in># D} \<or> l \<in># mm \<and> lit_of ` set (trail S) \<Turnstile>l l) \<or> (\<forall>l. mm \<noteq> {#- l#} \<or> l \<notin># D)"
                using ff5 ff1 by (metis (no_types, lifting) true_lit_def zero_less_Suc)
              hence "\<exists>l. mm \<notin> {{#- l#} |l. l \<in># D} \<or> l \<in># mm \<and> lit_of ` set (trail S) \<Turnstile>l l"
                by blast (* 6 ms *) }
              thus ?thesis unfolding CNot_def true_annots_def true_annot_def Ball_def lits_of_def true_cls_def atms_of_def
                by presburger (* 6 ms *)
          qed
        hence False
          proof -
            obtain pp :: "('a, nat, 'a literal multiset) marked_lit list \<times> 'a literal multiset set \<times> 'a literal multiset set \<times> nat \<times> 'a literal multiset conflicting_clause \<Rightarrow> ('a, nat, 'a literal multiset) marked_lit list \<times> 'a literal multiset set \<times> 'a literal multiset set \<times> nat \<times> 'a literal multiset conflicting_clause" where
              f2: "full0 cdcl_cp S (pp S)"
              by (meson alien always_exists_full_cdcl_cp_step local.finite)
            hence "pp S = S"
              using cdcl_s.conflict'[of S] by (metis (no_types) full0_unfold termi)
            thus ?thesis
              using f2 by (metis (no_types) UnCI `D \<in> clauses S` `conflicting S = C_True` `trail S \<Turnstile>as CNot D` full0_cdcl_cp_not_any_negated_clauses)
          qed
    }
    hence "?M \<Turnstile>as ?N" by blast
  }
  moreover {
    assume "\<exists>D L. conflicting S = C_Clause (D + {#L#})"
    obtain D L where LD: "conflicting S = C_Clause (D + {#L#})"
      and "get_level L ?M = ?k"
      proof -
        obtain mm :: "'a literal multiset" and ll :: "'a literal" where
          f2: "conflicting S = C_Clause (mm + {#ll#})"
          using `\<exists>D L. conflicting S = C_Clause (D + {#L#})` by force
        have "\<forall>m. (conflicting S \<noteq> C_Clause m \<or> m = {#}) \<or> (\<exists>l. l \<in># m \<and> get_level l (trail S) = backtrack_level S)"
          using confl_k by blast
        thus ?thesis
          using f2 that by (metis (no_types) multi_member_split single_not_empty union_eq_empty)
      qed
    let ?D = "D + {#L#}"
    have "?D \<noteq> {#}" by auto
    have "?M \<Turnstile>as CNot ?D" using confl LD unfolding cdcl_conflicting_def by auto
    hence "?M \<noteq> []" unfolding true_annots_def Ball_def true_annot_def true_cls_def by force
    { have M: "?M = hd ?M # tl ?M" using `?M \<noteq> []` list.collapse by fastforce
      assume marked: "is_marked (hd ?M)"
      then obtain k' where k': "k' + 1 = ?k"
        using level_inv M unfolding cdcl_M_level_inv_def
        by (cases "hd (trail S)"; cases "trail S") (auto simp del: upt.simps)
      obtain L' l' where L': "hd ?M = Marked L' l'" using marked by (case_tac "hd ?M") auto
      have "get_all_levels_of_marked (hd (trail S) # tl (trail S)) = rev [1..<1 + length (get_all_levels_of_marked ?M)]"
        using level_inv `get_level L ?M = ?k` M unfolding cdcl_M_level_inv_def M[symmetric] by blast
      hence "l' # get_all_levels_of_marked (tl ?M) = rev [1..<1 + length (get_all_levels_of_marked ?M)]" unfolding L' by (simp del: upt.simps)
      also have "\<dots> = length (get_all_levels_of_marked ?M) # rev [1..<length (get_all_levels_of_marked ?M)]"
        using M Suc_le_mono calculation by fastforce
      finally have "l' = ?k" and g_r: "get_all_levels_of_marked (tl (trail S)) = rev [1..<length (get_all_levels_of_marked (trail S))]"
        using level_inv `get_level L ?M = ?k` M unfolding cdcl_M_level_inv_def by auto
      have *: "\<And>list. no_dup list \<Longrightarrow>
            - L \<in> lits_of list \<Longrightarrow> atm_of L \<in> atm_of ` lits_of list"
        by (metis atm_of_uminus imageI)
      have "L' = -L"
        proof (rule ccontr)
          assume "\<not> ?thesis"
          also have "-L \<in> lits_of ?M" using confl LD unfolding cdcl_conflicting_def by auto
          ultimately have "get_level L (hd (trail S) # tl (trail S)) = get_level L (tl ?M)"
            using cdcl_M_level_inv_decomp(1)[OF level_inv] unfolding L' consistent_interp_def
            by (metis (no_types, lifting) L' M atm_of_eq_atm_of get_level_skip_beginning insert_iff lits_of_cons marked_lit.sel(1))

          also
            have "length (get_all_levels_of_marked (trail S)) = ?k" using level_inv unfolding cdcl_M_level_inv_def by auto
            hence "Max (set (0#get_all_levels_of_marked (tl (trail S)))) = ?k - 1" unfolding g_r by (auto simp add: Max_n_upt)
            hence "get_level L (tl ?M) < ?k"
              using get_maximum_possible_level_ge_get_level[of L "tl ?M"]
              by (metis One_nat_def add.right_neutral add_Suc_right diff_add_inverse2 get_maximum_possible_level_max_get_all_levels_of_marked k' le_imp_less_Suc list.simps(15))
          finally show False using `get_level L ?M = ?k` M by auto
        qed
      have L: "hd ?M = Marked (-L) ?k"  using `l' = ?k` `L' = -L` L' by auto

      have g_a_l: "get_all_levels_of_marked ?M = rev [1..<1 + ?k]" using level_inv `get_level L ?M = ?k` M unfolding cdcl_M_level_inv_def by auto
      have g_k: "get_maximum_level D (trail S) \<le> ?k"
        using get_maximum_possible_level_ge_get_maximum_level[of D ?M] get_maximum_possible_level_max_get_all_levels_of_marked[of ?M]
        by (auto simp del:upt.simps simp add: Max_n_upt g_a_l)
      have "get_maximum_level D (trail S) < ?k"
        proof (rule ccontr)
          assume "\<not> ?thesis"
          hence "get_maximum_level D (trail S) = ?k" using M g_k unfolding L by auto
          then obtain L' where "L' \<in># D" and L_k: "get_level L' ?M = ?k" using get_maximum_level_exists_lit[of ?k D ?M] unfolding k'[symmetric] by auto
          have "L \<noteq> L'" using no_dup  `L' \<in># D` unfolding distinct_cdcl_state_def LD by (metis add.commute add_eq_self_zero count_single count_union less_not_refl3 distinct_mset_def union_single_eq_member)
          have "L' = -L"
            proof (rule ccontr)
              assume "\<not> ?thesis"
              hence "get_level L' ?M = get_level L' (tl ?M)" using M `L \<noteq> L'` get_level_skip_beginning[of L' "hd ?M" "tl ?M"] unfolding L by (auto simp add: atm_of_eq_atm_of)
              also have "\<dots> < ?k" using level_inv g_r get_rev_level_less_max_get_all_levels_of_marked[of L' 0 "rev (tl ?M)"] L_k `l' # get_all_levels_of_marked (tl (trail S)) = rev [1..<1 + length (get_all_levels_of_marked (trail S))]` calculation g_a_l by (auto simp add: Max_n_upt cdcl_M_level_inv_def)
              finally show False using L_k by simp
            qed
          hence taut: "tautology (D + {#L#})" using `L' \<in># D` by (metis add.commute mset_leD mset_le_add_left multi_member_this tautology_minus)
          have "consistent_interp (lits_of ?M)" using level_inv by auto
          hence "\<not>?M \<Turnstile>as CNot ?D" using taut by (metis (no_types) `L' = - L` `L' \<in># D` add.commute consistent_interp_def in_CNot_implies_uminus(2) mset_leD mset_le_add_left multi_member_this)
          also have "?M \<Turnstile>as CNot ?D" using confl no_dup LD unfolding cdcl_conflicting_def by auto
          ultimately show False by blast
        qed
      hence False
        using backtrack_no_decomp[OF _ `get_level L (trail S) = backtrack_level S` _ level_inv]  LD  alien local.finite termi by (metis cdcl_state_decom cdcl_then_exists_cdcl_s_step)
    }
    also {
      assume "\<not>is_marked (hd ?M)"
      then obtain L' C where L'C: "hd ?M = Propagated L' C" by (case_tac "hd ?M", auto)
      hence M: "?M = Propagated L' C # tl ?M" using `?M \<noteq> []`  list.collapse by fastforce
      then obtain C' where C': "C = C' + {#L'#}"
        using confl unfolding cdcl_conflicting_def by (metis append_Nil diff_single_eq_union)
      { assume "-L' \<notin># ?D"
        hence False using cdcl_o.skip[OF skipping[OF _ `-L' \<notin># ?D` `?D \<noteq> {#}`, of S C "tl (trail S)" _ ]] termi cdcl_state_decom[of S] M by (metis LD alien cdcl_then_exists_cdcl_s_step local.finite)
      }
      also {
        assume "-L' \<in># ?D"
        then obtain D' where D': "?D = D' + {#-L'#}" by (metis insert_DiffM2)
        have g_r: "get_all_levels_of_marked (Propagated L' C # tl (trail S)) = rev [Suc 0..<Suc (length (get_all_levels_of_marked (trail S)))]"
          using level_inv M unfolding cdcl_M_level_inv_def by auto
        have "Max (insert 0 (set (get_all_levels_of_marked (Propagated L' C # tl (trail S))))) = ?k"
          using level_inv M unfolding g_r by (auto simp add:Max_n_upt simp del: upt.simps)
        hence "get_maximum_level D' (Propagated L' C # tl ?M) \<le> ?k" using get_maximum_possible_level_ge_get_maximum_level[of D' "Propagated L' C # tl ?M"] unfolding get_maximum_possible_level_max_get_all_levels_of_marked by auto
        have "get_maximum_level D' (Propagated L' C # tl ?M) = ?k \<or> get_maximum_level D' (Propagated L' C # tl ?M) < ?k" using `get_maximum_level D' (Propagated L' C # tl (trail S)) \<le> backtrack_level S` le_neq_implies_less by blast
        also {
          assume g_D'_k: "get_maximum_level D' (Propagated L' C # tl ?M) = ?k"
          have False
            proof -
              have f1: "get_maximum_level D' (trail S) = backtrack_level S"
                using M g_D'_k by auto
              have "(trail S, clauses S, learned_clauses S, backtrack_level S, C_Clause (D + {#L#})) = S"
                by (metis (no_types) LD cdcl_state_decom[of S])
              hence "cdcl_o S (tl (trail S), clauses S, learned_clauses S, backtrack_level S, C_Clause (remdups_mset (D' + C')))"
                using f1 by (metis (lifting) C' D' M cdcl_o.resolve[OF resolving[of S L' C' "tl ?M" ?N ?U ?k D']])
              thus ?thesis
                by (meson alien cdcl_then_exists_cdcl_s_step local.finite termi)
            qed
        }
        moreover {
          assume "get_maximum_level D' (Propagated L' C # tl ?M) < ?k"
          hence False
            proof -
              assume a1: "get_maximum_level D' (Propagated L' C # tl (trail S)) < backtrack_level S"
              obtain mm :: "'a literal multiset" and ll :: "'a literal" where
                f2: "conflicting S = C_Clause (mm + {#ll#}) \<and> get_level ll (trail S) = backtrack_level S"
                using LD `get_level L (trail S) = backtrack_level S` by blast
              hence f3: "get_maximum_level D' (trail S) \<le> get_level ll (trail S)"
                using M a1 by force
              have "get_level ll (trail S) \<noteq> get_maximum_level D' (trail S)"
                using f2 M calculation(2) by presburger (* 1 ms *)
              have f1: "trail S = Propagated L' C # tl (trail S)"
                  "conflicting S = C_Clause (D' + {#- L'#})"
                using D' LD M by force+
              have f2: "conflicting S = C_Clause (mm + {#ll#}) \<and> get_level ll (trail S) = backtrack_level S"
                using f2 by force
              have "ll = - L'"
                by (metis (no_types) D' LD `get_level ll (trail S) \<noteq> get_maximum_level D' (trail S)` conflicting_clause.inject f2 f3 get_maximum_level_ge_get_level insert_noteq_member le_antisym)
              thus ?thesis
                using f2 f1 M backtrack_no_decomp[OF cdcl_state_decom[of S, unfolded f1(2)]]
                by (metis (no_types) a1 alien cdcl_then_exists_cdcl_s_step level_inv local.finite
                  termi)
            qed
        }
        ultimately have False by blast
      }
      ultimately have False by blast
    }
    ultimately have False by blast
  }
  ultimately show ?thesis by blast
qed

lemma cdcl_cp_tranclp_cdcl:
   "cdcl_cp S S' \<Longrightarrow> cdcl\<^sup>+\<^sup>+ S S'"
   apply (induct rule: cdcl_cp.induct)
   by (meson cdcl.conflict cdcl.propagate tranclp.r_into_trancl tranclp.trancl_into_trancl)+

lemma tranclp_cdcl_cp_tranclp_cdcl:
   "cdcl_cp\<^sup>+\<^sup>+ S S' \<Longrightarrow> cdcl\<^sup>+\<^sup>+ S S'"
   apply (induct rule: tranclp.induct)
    apply (simp add: cdcl_cp_tranclp_cdcl)
    by (meson cdcl_cp_tranclp_cdcl tranclp_trans)

lemma cdcl_s_tranclp_cdcl:
   "cdcl_s S S' \<Longrightarrow> cdcl\<^sup>+\<^sup>+ S S'"
   apply (induct rule: cdcl_s.induct)
   unfolding full_def apply (simp add: tranclp_cdcl_cp_tranclp_cdcl)
   unfolding full0_def by (metis (no_types, lifting) other rtranclp_tranclp_tranclp rtranclp_unfold tranclp.simps tranclp_cdcl_cp_tranclp_cdcl)

lemma tranclp_cdcl_s_tranclp_cdcl:
   "cdcl_s\<^sup>+\<^sup>+ S S' \<Longrightarrow> cdcl\<^sup>+\<^sup>+ S S'"
   apply (induct rule: tranclp.induct)
   using cdcl_s_tranclp_cdcl apply blast
   by (meson cdcl_s_tranclp_cdcl tranclp_trans)

lemma rtranclp_cdcl_s_rtranclp_cdcl:
   "cdcl_s\<^sup>*\<^sup>* S S' \<Longrightarrow> cdcl\<^sup>*\<^sup>* S S'"
  using rtranclp_unfold[of cdcl_s S S'] tranclp_cdcl_s_tranclp_cdcl[of S S'] by auto

lemma cdcl_o_conflict_is_false_with_level_inv:
  assumes "cdcl_o S S'"
  and "conflict_is_false_with_level S"
  and "distinct_cdcl_state S"
  and "cdcl_conflicting S"
  and "cdcl_M_level_inv S"
  shows "conflict_is_false_with_level S'"
  using assms
proof (induct rule: cdcl_o_induct)
  case (resolve M N L D k U C) note IH = this(2) and n_d = this(3) and confl = this(4) and lev = this(5)
  have "-L \<notin># D" using n_d unfolding distinct_cdcl_state_def distinct_mset_def by auto
  also have "L \<notin># D"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      also have "Propagated L (C + {#L#}) # M \<Turnstile>as CNot D" using confl unfolding cdcl_conflicting_def by auto
      ultimately have "-L \<in> lits_of (Propagated L (C + {#L#}) # M)" using in_CNot_implies_uminus(2) by blast
      also have "no_dup (Propagated L (C + {#L#}) # M)" using lev by auto
      ultimately show False unfolding lits_of_def by (metis consistent_interp_def image_eqI list.set_intros(1) lits_of_def marked_lit.sel(2) distinctconsistent_interp)
    qed

  ultimately have g_D: "get_maximum_level D (Propagated L (C + {#L#}) # M) = get_maximum_level D M" using get_maximum_level_skip_first[of L D "C + {#L#}" M] unfolding atms_of_def
    proof -
      assume a1: "atm_of L \<notin> atm_of ` set_mset D \<Longrightarrow> get_maximum_level D (Propagated L (C + {#L#}) # M) = get_maximum_level D M"
      have "\<forall>a f L. ((a::'a) \<in> f ` L) = (\<exists>l. (l::'a literal) \<in> L \<and> a = f l)"
        by blast
      thus ?thesis
        using a1 by (metis (no_types) `- L \<notin># D` `L \<notin># D` atm_of_eq_atm_of mem_set_mset_iff)
    qed
  { assume "get_maximum_level D (Propagated L (C + {#L#}) # M) = k" and "k > 0"
    hence D: "get_maximum_level D M = k" unfolding g_D by blast
    hence ?case using `k > 0` get_maximum_level_exists_lit[of k D M] by auto
  }
  also {
    assume "k = 0"
    have "\<And>L. get_level L M = 0"
      proof -
        fix L
        have "atm_of L \<notin> atm_of ` (lit_of ` set M) \<Longrightarrow> get_level L M = 0" by auto
        also {
          assume "atm_of L \<in> atm_of ` (lit_of ` set M)"
          have g_r: "get_all_levels_of_marked M = rev [Suc 0..<Suc k]"
            using lev unfolding cdcl_M_level_inv_def by auto
          have "Max (insert 0 (set (get_all_levels_of_marked M))) = k"
            using lev unfolding g_r by (simp add: Max_n_upt del: upt.simps)
          hence "get_level L M = 0" using get_maximum_possible_level_ge_get_level[of L M] unfolding get_maximum_possible_level_max_get_all_levels_of_marked `k = 0` by auto
        }
        ultimately show "get_level L M = 0" by blast
      qed
    hence ?case using `k = 0` using get_maximum_level_exists_lit_of_max_level by simp blast
  }
  ultimately show ?case using resolve.hyps(1) by blast
next
  case (skip M N L C' D k U) note D = this(2) and confl = this(5) and lev = this(6)
  then obtain La where "La \<in># D" and "get_level La (Propagated L C' # M) = k" using skip by auto
  also
    have "atm_of La \<noteq> atm_of L"
      proof (rule ccontr)
        assume "\<not> ?thesis"
        hence La: "La = L" using `La \<in># D` `- L \<notin># D` by (auto simp add: atm_of_eq_atm_of)
        have "Propagated L C' # M \<Turnstile>as CNot D" using confl by auto
        hence "-L \<in> lits_of M"
          using `La \<in># D` in_CNot_implies_uminus(2)[of D L "Propagated L C' # M"] unfolding La by auto
        thus False using lev unfolding cdcl_M_level_inv_def consistent_interp_def by auto
      qed
    hence "get_level La (Propagated L C' # M) = get_level La M"  by auto
  ultimately show ?case using D by auto
qed (auto elim: btE decidedE)

subsubsection \<open>Strong completeness\<close>
lemma cdcl_cp_propagate_confl:
  assumes "cdcl_cp S T"
  shows "propagate\<^sup>*\<^sup>* S T \<or> (\<exists>S'. propagate\<^sup>*\<^sup>* S S' \<and> conflict S' T)"
  using assms by (induction) blast+

lemma rtranclp_cdcl_cp_propagate_confl:
  assumes "cdcl_cp\<^sup>*\<^sup>* S T"
  shows "propagate\<^sup>*\<^sup>* S T \<or> (\<exists>S'. propagate\<^sup>*\<^sup>* S S' \<and> conflict S' T)"
  using assms
proof (induction)
  case base
  show ?case by blast
next
  case (step T U) note st = this(2) and IH = this(3)
  then consider (propa) "propagate\<^sup>*\<^sup>* S T" | (confl) "\<exists>S'. propagate\<^sup>*\<^sup>* S S' \<and> conflict S' T"
    by metis
  thus ?case
    proof cases
      case confl
      with st have "False"
        by (induction) blast+
      thus ?thesis by fast
    next
      case propa
      thus ?thesis using cdcl_cp_propagate_confl[OF st] rtranclp_trans[of propagate] by fast
    qed
qed

lemma cdcl_cp_propagate_completeness:
  assumes MN: "set M \<Turnstile>s N" and
  cons: "consistent_interp (set M)" and
  tot: "total_over_m (set M) N" and
  "lits_of (trail S) \<subseteq> set M" and
  "clauses S = N" and
  "propagate\<^sup>*\<^sup>* S S'" and
  "learned_clauses S = {}"
  shows "length (trail S) \<le> length (trail S') \<and> lits_of (trail S') \<subseteq> set M"
  using assms(6,4,5,7)
proof (induction rule: rtranclp.induct)
  case rtrancl_refl
  thus ?case by auto
next
  case (rtrancl_into_rtrancl X Y Z)
  note st = this(1) and propa = this(2) and IH = this(3) and lits' = this(4) and NS = this(5) and learned = this(6)
  hence len: "length (trail X) \<le> length (trail Y)" and LM: "lits_of (trail Y) \<subseteq> set M"
     by blast+

  obtain M' N' U k C L where
    Y: "Y = (M', N', U, k, C_True)" and
    Z: "Z = (Propagated L (C + {#L#}) # M', N', U, k, C_True)" and
    C: "C + {#L#} \<in> N' \<union> U" and
    M'_C: "M' \<Turnstile>as CNot C" and
    "undefined_lit L (trail Y)"
    using propa by auto
  have "clauses X  = clauses Y"
    using st by induction auto
  then have [simp]: "N' = N" using NS unfolding Y Z by simp
  have "learned_clauses Y = {}"
    using st learned by induction auto
  hence [simp]: "U = {}" unfolding Y by auto
  have "set M \<Turnstile>s CNot C"
    using M'_C LM unfolding true_annots_def Ball_def true_annot_def true_clss_def Y true_cls_def
    by auto
  also
    have "set M \<Turnstile> C + {#L#}"
      using MN C learned unfolding true_clss_def by auto
  ultimately have "L \<in> set M" by (simp add: cons consistent_CNot_not)
  then show ?case using LM len unfolding Y Z by (cases X) auto
qed

lemma completeness_is_a_full_propagation:
  fixes S :: "'v cdcl_state" and M :: "'v literal list"
  assumes MN: "set M \<Turnstile>s N"
  and cons: "consistent_interp (set M)"
  and tot: "total_over_m (set M) N"
  and fin: "finite (clauses S)"
  and alien: "no_strange_atm S"
  and learned: "learned_clauses S = {}"
  and clsS[simp]: "clauses S = N"
  and lits: "lits_of (trail S) \<subseteq> set M"
  shows "\<exists>S'. propagate\<^sup>*\<^sup>* S S' \<and> full0 cdcl_cp S S'"
proof -
  obtain S' where full: "full0 cdcl_cp S S'"
    using always_exists_full_cdcl_cp_step alien fin by blast
  then consider (propa) "propagate\<^sup>*\<^sup>* S S'"
    | (confl) "\<exists>X. propagate\<^sup>*\<^sup>* S X \<and> conflict X S'"
    using rtranclp_cdcl_cp_propagate_confl unfolding full0_def by blast
  thus ?thesis
    proof cases
      case propa thus ?thesis using full by blast
    next
      case confl
      then obtain X where
        X: "propagate\<^sup>*\<^sup>* S X" and
        Xconf: "conflict X S'"
      by blast
      have clsX: "clauses X = clauses S"
        using rtranclp_cdcl_no_more_clauses X rtranclp_propagate_is_rtranclp_cdcl by fast
      have learnedX: "learned_clauses X = {}" using X learned by induction auto
      obtain E where
        E: "E \<in> clauses X \<union> learned_clauses X" and
        Not_E: "trail X \<Turnstile>as CNot E"
        using Xconf by (auto simp add: conflict.simps)
      have "lits_of (trail X) \<subseteq> set M"
        using cdcl_cp_propagate_completeness[OF assms(1-3) lits _ X learned] learned by auto
      hence MNE: "set M \<Turnstile>s CNot E"
        using Not_E
        by (fastforce simp add: true_annots_def true_annot_def true_clss_def true_cls_def)
      have "\<not> set M \<Turnstile>s N"
         using E consistent_CNot_not[OF cons MNE]
         unfolding learnedX true_clss_def unfolding clsX clsS by blast
      thus ?thesis using MN by blast
    qed
qed

lemma cdcl_cp_strong_completeness_n:
  assumes MN: "set M \<Turnstile>s N"
  and cons: "consistent_interp (set M)"
  and tot: "total_over_m (set M) N"
  and atm_incl: "atm_of ` (set M) \<subseteq> atms_of_m N"
  and "total_over_m (set M) N"
  and distM: "distinct M"
  and fin: "finite N"
  and length: "n \<le> length M"
  shows
    "\<exists>M' k. length M' \<ge>  n \<and>
      lits_of M' \<subseteq> set M \<and>
      rtranclp cdcl_s (S0_cdcl N) (M', N, {}, k, C_True)"
  using length
proof (induction n)
  case 0 thus ?case using MN unfolding no_more_propagation_to_do_def by force
next
  case (Suc n) note IH = this(1) and n = this(2)
  then obtain M' k where
    l_M': "length M' \<ge> n" and
    M': "lits_of M' \<subseteq> set M" and
    st: "cdcl_s\<^sup>*\<^sup>* (S0_cdcl N) (M', N, {}, k, C_True)"
    by auto
    let ?S = "(M', N, {}, k, C_True)"
  have
    M: "cdcl_M_level_inv ?S" and
    alien: "no_strange_atm ?S"
      using rtranclp_cdcl_consistent_inv[OF rtranclp_cdcl_s_rtranclp_cdcl[OF st]] rtranclp_cdcl_no_strange_atm_inv[OF rtranclp_cdcl_s_rtranclp_cdcl[OF st]] by auto

  { assume no_step: "\<not>no_step propagate ?S"

    obtain S' where S': "propagate\<^sup>*\<^sup>* ?S S'" and full0: "full0 cdcl_cp ?S S'"
      using completeness_is_a_full_propagation[OF assms(1-3), of ?S] fin alien M' by auto
    hence "length (trail ?S) \<le> length (trail S') \<and> lits_of (trail S') \<subseteq> set M"
      using cdcl_cp_propagate_completeness[OF assms(1-3), of ?S] M' by auto
    also have full: "full cdcl_cp ?S S'"
     using full0 no_step no_step_cdcl_cp_no_conflict_no_propagate(2) unfolding full_def full0_def rtranclp_unfold by blast
    moreover {
      have "propagate\<^sup>+\<^sup>+ ?S S'" using S' full unfolding full_def by (metis rtranclpD tranclpD)
      also have "trail ?S = M'" by auto
      ultimately have "length (trail S') > n"
        using l_M' by (induction rule: tranclp.induct) auto}
    moreover have stS': "cdcl_s\<^sup>*\<^sup>* (S0_cdcl N) S'"
      using st cdcl_s.conflict'[OF full] by auto
    moreover have "clauses S' = N" using stS' rtranclp_cdcl_s_no_more_clauses by fastforce
    moreover have "learned_clauses S' = {}"
      using full0 unfolding full0_def by (fastforce dest: rtranclp_cdcl_cp_learned_clause_inv)
    moreover have "conflicting S' = C_True" using S' by induction auto
    ultimately have ?case
      apply -
      by (rule exI[of _ "trail S'"], rule exI[of _ "backtrack_level S'"]) auto
  }
  also {
    assume no_step: "no_step propagate ?S"
    have ?case
      proof (cases "length M' \<ge> Suc n")
        case True
        thus ?thesis using l_M' M' st M alien by blast
      next
        case False
        hence n': "length M' = n" using l_M' by auto
        have no_confl: "no_step conflict (M', N, {}, k, C_True)"
          proof -
            { fix D
              assume "D \<in> N" and "M' \<Turnstile>as CNot D"
              hence "set M \<Turnstile> D" using MN unfolding true_clss_def by auto
              also have "set M \<Turnstile>s CNot D"
                using `M' \<Turnstile>as CNot D` M'
                by (meson true_annots_true_cls true_cls_mono_l true_clss_def)
              ultimately have False using cons consistent_CNot_not by blast
            }
            thus ?thesis by (auto simp add: conflict.simps true_clss_def)
          qed
        have lenM: "length M = card (set M)" using distM by (induction M) auto
        have "no_dup M'" using M unfolding cdcl_M_level_inv_def by simp
        hence "card (lits_of M') = length M'"
          by (induction M') (auto simp add: lits_of_def card_insert_if)
        hence "lits_of M' \<subset> set M"
          using n M' n' lenM by auto
        then obtain m where m: "m \<in> set M" and undef_m: "m \<notin> lits_of M'" by auto
        also have "undefined_lit m M'"
          using M' Marked_Propagated_in_iff_in_lits_of calculation(1,2) cons
          consistent_interp_def by blast
        ultimately have dec: "decided (M', N, {}, k, C_True) (Marked m (k+1)# M', N, {}, k+1, C_True)"
          using atm_incl by fast
        let ?S' = "(Marked m (k+1)# M', N, {}, k+1, C_True)"
        have "lits_of (trail ?S') \<subseteq> set M" using m M' by auto
        also have "finite (clauses ?S')"
          using fin by (auto elim!: decidedE)
        moreover have "no_strange_atm ?S'"
          using alien dec by (meson cdcl_no_strange_atm_inv decided other)
        ultimately obtain S'' where S'': "propagate\<^sup>*\<^sup>* ?S' S''" and full0: "full0 cdcl_cp ?S' S''"
          using completeness_is_a_full_propagation[OF assms(1-3), of ?S'] by auto
        hence "length (trail ?S') \<le> length (trail S'') \<and> lits_of (trail S'') \<subseteq> set M"
          using cdcl_cp_propagate_completeness[OF assms(1-3), of ?S' S''] m M' by simp
        hence "Suc n \<le> length (trail S'') \<and> lits_of (trail S'') \<subseteq> set M"
          using l_M' by (auto elim: decidedE)
        also have S'': "S''=  (trail S'', N, {}, backtrack_level S'', C_True)"
          using S'' by induct auto
        hence "cdcl_s\<^sup>*\<^sup>* (S0_cdcl N) (trail S'', N, {}, backtrack_level S'', C_True)"
          using cdcl_s.intros(2)[OF decided[OF dec] no_step no_confl full0] st by auto
        ultimately show ?thesis by blast
      qed
  }
  ultimately show ?case by blast
qed

lemma cdcl_cp_strong_completeness:
  assumes MN: "set M \<Turnstile>s N"
  and cons: "consistent_interp (set M)"
  and tot: "total_over_m (set M) N"
  and atm_incl: "atm_of ` (set M) \<subseteq> atms_of_m N"
  and "total_over_m (set M) N"
  and distM: "distinct M"
  and fin: "finite N"
  shows
    "\<exists>M' k.
      lits_of M' = set M \<and>
      rtranclp cdcl_s (S0_cdcl N) (M', N, {}, k, C_True) \<and>
      final_cdcl_state (M', N, {}, k, C_True)"
proof -
  from cdcl_cp_strong_completeness_n[OF assms, of "length M"]
  obtain M' k where
    l: "length M \<le> length M'" and
    M'_M: "lits_of M' \<subseteq> set M" and
    st: "cdcl_s\<^sup>*\<^sup>* (S0_cdcl N) (M', N, {}, k, C_True)"
    by auto
  have "card (set M) = length M" using distM by (simp add: distinct_card)
  also
    have "cdcl_M_level_inv (M', N, {}, k, C_True)"
      using rtranclp_cdcl_s_consistent_inv[OF st] by auto
    hence no_dup: "no_dup M'" by auto
    hence "card (set ((map (\<lambda>l. atm_of (lit_of l)) M'))) = length M'" using distinct_card by fastforce
  moreover have "card (lits_of M') = card (set ((map (\<lambda>l. atm_of (lit_of l)) M')))"
    using no_dup unfolding lits_of_def apply (induction M') by (auto simp add: card_insert_if)
  ultimately have "card (set M) \<le> card (lits_of M')" using l unfolding lits_of_def by auto
  hence "set M = lits_of M'"
    using M'_M  card_seteq by blast
  also
    hence "M' \<Turnstile>as N"
      using MN unfolding true_annots_def Ball_def true_annot_def true_clss_def by auto
    hence "final_cdcl_state (M', N, {}, k, C_True)"
      unfolding final_cdcl_state_def by auto
  ultimately show ?thesis using st by blast
qed

subsubsection \<open>No conflict with only variables of level less than backtrack level\<close>
text \<open>This invariant is stronger than the previous argument in the sense that it is a property about all possible conflicts.\<close>
abbreviation "no_littler_confl (S::'v cdcl_state) \<equiv> (\<forall>M K i M' D. M' @ Marked K i # M = trail S \<longrightarrow> D \<in> clauses S \<union> learned_clauses S \<longrightarrow> \<not>M \<Turnstile>as CNot D)"

lemma "no_littler_confl (S0_cdcl N)" by auto

lemma cdcl_o_no_littler_confl_inv:
  fixes S S' :: "'v cdcl_state"
  assumes "cdcl_o S S'"
  and "conflict_is_false_with_level S"
  and "no_littler_confl S"
  and "cdcl_M_level_inv S"
  and "no_clause_is_false S"
  shows "no_littler_confl S'"
  using assms
proof (induct rule: cdcl_o_induct)
  case (decided M N U k L) note no_f = this(6) and IH = this(4) and lev = this(5)
  show ?case
    proof (intro allI impI)
      fix M' K i M'' Da
      assume "M'' @ Marked K i # M' = trail (Marked L (k + 1) # M, N, U, k + 1, C_True)"
      and D: "Da \<in> clauses (Marked L (k + 1) # M, N, U, k + 1, C_True) \<union> learned_clauses (Marked L (k + 1) # M, N, U, k + 1, C_True)"
      then have "tl M'' @ Marked K i # M' = M \<or> (M'' = [] \<and> Marked K i # M' = Marked L (k + 1) # M)"
        by (metis append_self_conv2 trail_conv list.sel(3) tl_append2)
      also {
        assume "tl M'' @ Marked K i # M' = M"
        hence "\<not>M' \<Turnstile>as CNot Da" using IH D by auto
      }
      moreover {
        assume "Marked K i # M' = Marked L (k + 1) # M"
        hence "\<not>M' \<Turnstile>as CNot Da" using no_f D by auto
      }
      ultimately show "~M' \<Turnstile>as CNot Da" by auto
   qed
next
  case (resolve L C M N U k D)
  thus ?case by force
next
  case (skip L C' M N U k D)
  thus ?case by force
next
  case (backtrack M N U k D L K i M1 M2) note S = this(1) and decomp = this(1) and IH = this(6) and lev = this(7)
  obtain c where M: "M = c @ M2 @ Marked K (i+1) # M1" using get_all_marked_decomposition_exists_prepend decomp by blast

  show ?case
    proof (intro allI impI)
      fix M' K' ia M'' Da
      assume "M'' @ Marked K' ia # M' = trail (Propagated L (D + {#L#}) # M1, N, U \<union> {D + {#L#}}, i, C_True)"
      hence "tl M'' @ Marked K' ia # M' = M1" apply simp by (metis append_self_conv2 list.inject list.sel(3) marked_lit.distinct(1) tl_append2)
      assume D: "Da \<in> clauses (Propagated L (D + {#L#}) # M1, N, U \<union> {D + {#L#}}, i, C_True) \<union> learned_clauses (Propagated L (D + {#L#}) # M1, N, U \<union> {D + {#L#}}, i, C_True)"
      also{
        assume "Da \<in> N \<union> U"
        hence "\<not>M' \<Turnstile>as CNot Da" using IH `tl M'' @ Marked K' ia # M' = M1` unfolding S M by auto
      }
      moreover {
        assume Da: "Da = D + {#L#}"
        have "\<not>M' \<Turnstile>as CNot Da"
          proof (rule ccontr)
            assume "\<not> ?thesis"
            hence "-L \<in> lits_of M'" unfolding Da by auto
            hence "-L \<in> lits_of (Propagated L (D + {#L#}) # M1)" using UnI2 `tl M'' @ Marked K' ia # M' = M1` by auto
            also
              have "cdcl_M_level_inv (Propagated L (D + {#L#}) # M1, N, U \<union> {D + {#L#}}, i, C_True)"
                using cdcl_consistent_inv[OF cdcl.other[OF cdcl_o.backtrack[OF backtracking[OF _  backtrack.hyps]]] lev]
                by auto
              hence "no_dup  (Propagated L (D + {#L#}) # M1)" by auto
            ultimately show False apply simp by (metis atm_of_uminus imageI image_image lits_of_def)
          qed
      }
      ultimately show "~M' \<Turnstile>as CNot Da" by auto
    qed
qed

lemma conflict_no_littler_confl_inv:
  assumes "conflict S S'"
  and "no_littler_confl S"
  shows "no_littler_confl S'"
  using assms by fastforce

lemma propagate_no_littler_confl_inv:
  assumes propagate: "propagate S S'"
  and n_l: "no_littler_confl S"
  shows "no_littler_confl S'"
proof (intro allI impI)
  fix M' K i M'' D
  assume M': "M'' @ Marked K i # M' = trail S'"
  and "D \<in> clauses S' \<union> learned_clauses S'"
  obtain M N U k C L where S: "S = (M, N, U, k, C_True)"
  and S': "S' = (Propagated L (C + {#L#}) # M, N, U, k, C_True)"
  and "C + {#L#} \<in> N \<union> U"
  and "M \<Turnstile>as CNot C"
  and "undefined_lit L M"
    using propagate by auto
  have "tl M'' @ Marked K i # M' = trail S" using M' unfolding S S'  apply auto by (metis append_Nil list.inject list.sel(3) marked_lit.distinct(1) tl_append2)
  hence "\<not> M' \<Turnstile>as CNot D " using `D \<in> clauses S' \<union> learned_clauses S'` n_l unfolding S S' by auto
  thus "\<not>M' \<Turnstile>as CNot D" by auto
qed

lemma cdcl_cp_no_littler_confl_inv:
  assumes propagate: "cdcl_cp S S'"
  and n_l: "no_littler_confl S"
  shows "no_littler_confl S'"
  using assms
proof (induct rule: cdcl_cp.induct)
  case (conflict' S S')
  thus ?case using conflict_no_littler_confl_inv[of S S'] by blast
next
  case (propagate_conf' S S' S'')
  thus ?case using propagate_no_littler_confl_inv[of S S'] conflict_no_littler_confl_inv[of S' S''] by fastforce
next
  case (propagate_no_conf' S S')
  thus ?case using propagate_no_littler_confl_inv[of S S'] by metis
qed

lemma rtrancp_cdcl_cp_no_littler_confl_inv:
  assumes propagate: "cdcl_cp\<^sup>*\<^sup>* S S'"
  and n_l: "no_littler_confl S"
  shows "no_littler_confl S'"
  using assms
proof (induct rule: rtranclp.induct)
  case rtrancl_refl
  thus ?case by simp
next
  case (rtrancl_into_rtrancl S S' S'')
  thus ?case using cdcl_cp_no_littler_confl_inv[of S' S''] by fast
qed

lemma trancp_cdcl_cp_no_littler_confl_inv:
  assumes propagate: "cdcl_cp\<^sup>+\<^sup>+ S S'"
  and n_l: "no_littler_confl S"
  shows "no_littler_confl S'"
  using assms
proof (induct rule: tranclp.induct)
  case (r_into_trancl S S')
  thus ?case using cdcl_cp_no_littler_confl_inv[of S S'] by blast
next
  case (trancl_into_trancl S S' S'')
  thus ?case using cdcl_cp_no_littler_confl_inv[of S' S''] by fast
qed

lemma full0_cdcl_cp_no_littler_confl_inv:
  assumes "full0 cdcl_cp S S'"
  and n_l: "no_littler_confl S"
  shows "no_littler_confl S'"
  using assms unfolding full0_def
  using rtrancp_cdcl_cp_no_littler_confl_inv[of S S'] by blast

lemma full_cdcl_cp_no_littler_confl_inv:
  assumes "full cdcl_cp S S'"
  and n_l: "no_littler_confl S"
  shows "no_littler_confl S'"
  using assms unfolding full_def
  using trancp_cdcl_cp_no_littler_confl_inv[of S S'] by blast

lemma cdcl_s_no_littler_confl_inv:
  assumes "cdcl_s S S'"
  and n_l: "no_littler_confl S"
  and "conflict_is_false_with_level S"
  and "cdcl_M_level_inv S"
  shows "no_littler_confl S'"
  using assms
proof (induct rule: cdcl_s.induct)
  case (conflict' S S')
  thus ?case using full_cdcl_cp_no_littler_confl_inv[of S S'] by blast
next
  case (other' S S' S'')
  have "no_littler_confl S'" using cdcl_o_no_littler_confl_inv[OF other'.hyps(1) other'.prems(2)  other'.prems(1) other'.prems(3)] not_conflict_not_any_negated_clauses[OF other'.hyps(3)] by blast
  thus ?case  using full0_cdcl_cp_no_littler_confl_inv[of S' S''] other'.hyps(4) by blast
qed


lemma conflict_conflict_is_no_clause_is_false_test:
  assumes "conflict S S'"
  and "(\<forall>D \<in> clauses S \<union> learned_clauses S. trail S \<Turnstile>as CNot D \<longrightarrow> (\<exists>L. L \<in># D \<and> get_level L (trail S) = backtrack_level S))"
  shows "\<forall>D \<in> clauses S' \<union> learned_clauses S'. trail S' \<Turnstile>as CNot D \<longrightarrow> (\<exists>L. L \<in># D \<and> get_level L (trail S') = backtrack_level S')"
  using assms
  by auto

lemma cdcl_cp_exists_conflict:
  assumes "cdcl_cp S' S''"
  and "\<not>(\<forall>D\<in>clauses S' \<union> learned_clauses S'. \<not> trail S' \<Turnstile>as CNot D)"
  and "conflicting S' = C_True"
  shows "conflict S' S''"
  using assms
proof (induct rule: cdcl_cp.induct)
  case (conflict' S S')
  thus ?case by auto
next
  case (propagate_conf' S S')
  also have "\<exists>S'. conflict S S'" using propagate_conf'.prems by (auto simp add: conflict.simps)
  ultimately show ?case by blast
next
  case (propagate_no_conf' S S')
  also have "\<exists>S'. conflict S S'" using propagate_no_conf'.prems by (auto simp add: conflict.simps)
  ultimately show ?case by blast
qed

lemma is_conflicting_exists_conflict:
  assumes "\<not>(\<forall>D\<in>clauses S' \<union> learned_clauses S'. \<not> trail S' \<Turnstile>as CNot D)"
  and "conflicting S' = C_True"
  shows "\<exists>S''. conflict S' S''"
  using assms by (auto simp add: conflict.simps)

lemma rtranclp_cdcl_cp_exists_conflict:
  assumes "cdcl_cp\<^sup>+\<^sup>+ S' S''"
  and "\<not>(\<forall>D\<in>clauses S' \<union> learned_clauses S'. \<not> trail S' \<Turnstile>as CNot D)"
  and "conflicting S' = C_True"
  shows "conflict S' S''"
  using assms
proof (induct rule: tranclp.induct)
  case (r_into_trancl S S')
  thus ?case using cdcl_cp_exists_conflict[of S S'] by blast
next
  case (trancl_into_trancl S S' S'')
  thus ?case by auto
qed

lemma full0_cdcl_cp_exists_conflict:
  assumes "full0 cdcl_cp S' S''"
  and "\<not>(\<forall>D\<in>clauses S' \<union> learned_clauses S'. \<not> trail S' \<Turnstile>as CNot D)"
  and "conflicting S' = C_True"
  shows "conflict S' S''"
proof -
  have "\<exists>S''. conflict S' S''" using assms(2,3) by (auto simp add: conflict.simps)
  hence "cdcl_cp\<^sup>+\<^sup>+ S' S''" using assms(1) cdcl_cp.conflict' unfolding full0_unfold full_def by blast
  thus ?thesis using rtranclp_cdcl_cp_exists_conflict[OF _ assms(2,3)] by auto
qed


lemma cdcl_o_conflict_is_no_clause_is_false:
  fixes S S' :: "'v cdcl_state"
  assumes "cdcl_o S S'"
  and "conflict_is_false_with_level S"
  and "no_clause_is_false S"
  and "cdcl_M_level_inv S"
  and "no_littler_confl S"
  shows "no_clause_is_false S' \<or> (conflicting S' = C_True \<longrightarrow>(\<forall>D \<in> clauses S' \<union> learned_clauses S'. trail S' \<Turnstile>as CNot D \<longrightarrow> (\<exists>L. L \<in># D \<and> get_level L (trail S') = backtrack_level S')))"
  using assms
proof (induct rule: cdcl_o_induct)
  case (decided M N U k L) note S = this(1) and undef = this(1) and no_f = this(4) and lev = this(5)
  show ?case
    proof (rule HOL.disjI2, clarify)
      fix D
      assume "D \<in> N \<union> U"
      and M_D: "Marked L (k + 1) # M \<Turnstile>as CNot D"
      have "~M \<Turnstile>as CNot D" using no_f `D \<in> N \<union> U` unfolding S by auto
      have "-L \<in># D"
        proof (rule ccontr)
          assume "\<not> ?thesis"
          have "M \<Turnstile>as CNot D"
            unfolding true_annots_def Ball_def true_annot_def CNot_def true_cls_def
            proof (intro allI impI)
              fix x
              assume x: "x \<in> {{#- L#} |L. L \<in># D}"
              then obtain L' where L': "x = {#-L'#}" "L' \<in># D" by auto
              obtain L'' where "L'' \<in># x" and "lits_of (Marked L (k + 1) # M) \<Turnstile>l L''"
                using M_D x unfolding true_annots_def Ball_def true_annot_def CNot_def true_cls_def
                by blast
              show "\<exists>L. L \<in># x \<and> lits_of M \<Turnstile>l L"  by (metis `- L \<notin># D` `L'' \<in># x` L' `lits_of (Marked L (k + 1) # M) \<Turnstile>l L''` count_single insertE less_numeral_extra(3) lits_of_cons marked_lit.sel(1) true_lit_def uminus_of_uminus_id)
            qed
          thus False using `~M \<Turnstile>as CNot D` by auto
        qed
      have "atm_of L \<notin> atm_of ` (lit_of ` set M)" using undef defined_lit_map by fastforce
      hence "get_level (-L) (Marked L (k + 1) # M) = k + 1" by simp
      thus "\<exists>La. La \<in># D \<and> get_level La (Marked L (k + 1) # M) = k + 1" using `-L \<in># D` by auto
    qed
next
  case (resolve L C M N U k D)
  thus ?case by auto
next
  case (skip L C' M N U k D)
  thus ?case by auto
next
  case (backtrack M N U k D L K i M1 M2) note decomp = this(1) and lev = this(6) and no_f = this(7) and no_l = this(8)
  show ?case
    proof (rule HOL.disjI2, clarify)
      fix Da
      assume Da: "Da \<in> N \<union> (U \<union> {D + {#L#}})"
      and M_D: "Propagated L (D + {#L#}) # M1 \<Turnstile>as CNot Da"
      obtain c where M: "M = c @ M2 @ Marked K (i + 1) # M1" using decomp get_all_marked_decomposition_exists_prepend by blast
      have lev': "cdcl_M_level_inv (Propagated L (D + {#L#}) # M1, N, U \<union> {D + {#L#}}, i, C_True)"
        using cdcl_consistent_inv[OF cdcl.other[OF cdcl_o.backtrack[OF backtracking[OF _ backtrack.hyps]]] no_f] by auto
      hence "- L \<notin> lits_of M1"
        unfolding cdcl_M_level_inv_def lits_of_def by (metis consistent_interp_def trail_conv insert_iff lits_of_cons lits_of_def marked_lit.sel(2))
      { assume "Da \<in> N \<union> U"
        hence "~M1 \<Turnstile>as CNot Da" using no_l unfolding M by auto
      }
      also {
        assume Da: "Da = D + {#L#}"
        have "~M1 \<Turnstile>as CNot Da" using `- L \<notin> lits_of M1` unfolding Da by simp
      }
      ultimately have "~M1 \<Turnstile>as CNot Da" using Da by auto
      hence "-L \<in># Da"
        by (metis M_D cdcl_M_level_inv_def lev' marked_lit.sel(2) trail_conv true_annots_lit_of_notin_skip)
      have g_M1: "get_all_levels_of_marked M1 = rev [1..<i+1]" using lev' unfolding cdcl_M_level_inv_def by auto
      have "no_dup (Propagated L (D + {#L#}) # M1)" using lev' by auto
      hence L: "atm_of L \<notin> atm_of ` lit_of ` set M1" by auto
      have "get_level (-L) (Propagated L (D + {#L#}) # M1) = i"
        using get_level_get_rev_level_get_all_levels_of_marked[OF L, of "[Propagated L (D + {#L#})]"] by (simp add: g_M1 split: if_splits)
      thus "\<exists>La. La \<in># Da \<and> get_level La (Propagated L (D + {#L#}) # M1) = i"
        using `-L \<in># Da` by auto
    qed
qed

lemma cdcl_s_no_littler_confl_inv_ex_lit_of_max_level:
  assumes "cdcl_s S S'"
  and n_l: "no_littler_confl S"
  and "conflict_is_false_with_level S"
  and "cdcl_M_level_inv S"
  and "no_clause_is_false S"
  and "distinct_cdcl_state S"
  and "cdcl_conflicting S"
  shows "no_littler_confl S' \<and> conflict_is_false_with_level S'"
  using assms
proof (induct rule: cdcl_s.induct)
  case (conflict' S S')
  have "no_littler_confl S'" using conflict'.hyps conflict'.prems(1) full_cdcl_cp_no_littler_confl_inv by blast
  also have "conflict_is_false_with_level S'" using conflict'.hyps conflict'.prems(2-4) rtranclp_cdcl_co_conflict_ex_lit_of_max_level[of S S'] unfolding full_def rtranclp_unfold by blast
  ultimately show ?case by blast
next
  case (other' S S' S'')
  have lev': " cdcl_M_level_inv S'" using cdcl_consistent_inv other other'.hyps(1) other'.prems(3) by blast
  have "no_littler_confl S''" using cdcl_s_no_littler_confl_inv[OF cdcl_s.other'[OF other'.hyps(1-4)]] other'.prems(1-3) by blast
  also
  have "no_clause_is_false S' \<or> (conflicting S' = C_True \<longrightarrow> (\<forall>D\<in>clauses S' \<union> learned_clauses S'. trail S' \<Turnstile>as CNot D \<longrightarrow> (\<exists>L. L \<in># D \<and> get_level L (trail S') = backtrack_level S')))"  using cdcl_o_conflict_is_no_clause_is_false[of S S'] other'.hyps(1) other'.prems(1-4) by fastforce
  moreover {
    assume "no_clause_is_false S'"
    {
      assume "conflicting S' = C_True"
      hence "conflict_is_false_with_level S'" by auto
      also   have "cdcl_cp\<^sup>*\<^sup>* S' S''"
        by (metis (no_types) full0_def other'.hyps(4))
      ultimately have "conflict_is_false_with_level S''" using rtranclp_cdcl_co_conflict_ex_lit_of_max_level[of S' S''] lev' `no_clause_is_false S'` by fastforce
    }
    also
    {
      assume c: "conflicting S' \<noteq> C_True"
      have "conflicting S \<noteq> C_True" using other'.hyps(1) c
        by (induct rule: cdcl_o_induct) auto
      hence "conflict_is_false_with_level S'" using cdcl_o_conflict_is_false_with_level_inv[OF other'.hyps(1) other'.prems(2)] other'.prems(3,5,6) by blast
      also have "cdcl_cp\<^sup>*\<^sup>* S' S''" using other'.hyps(4) unfolding full0_def by auto
      hence "S' = S''" using c
        by (induct rule: rtranclp.induct)
           (fastforce intro: conflicting_clause.exhaust)+
      ultimately have "conflict_is_false_with_level S''" by auto
    }
    ultimately have "conflict_is_false_with_level S''" by blast
  }
  moreover {
     assume "conflicting S' = C_True" and D_L: "\<forall>D \<in> clauses S' \<union> learned_clauses S'. trail S' \<Turnstile>as CNot D \<longrightarrow> (\<exists>L. L \<in># D \<and> get_level L (trail S') = backtrack_level S')"
     { assume "\<forall>D\<in>clauses S' \<union> learned_clauses S'. \<not> trail S' \<Turnstile>as CNot D"
       hence "no_clause_is_false S'" using `conflicting S' = C_True` by simp
       hence "conflict_is_false_with_level S''" using calculation(3) by blast
     }
     also {
       assume "\<not>(\<forall>D\<in>clauses S' \<union> learned_clauses S'. \<not> trail S' \<Turnstile>as CNot D)"
       then obtain D where S'': "S'' = (trail S', clauses S', learned_clauses S', backtrack_level S', C_Clause D)" and "D \<in> clauses S' \<union> learned_clauses S'" and "trail S' \<Turnstile>as CNot D" using full0_cdcl_cp_exists_conflict[OF other'.hyps(4)] `conflicting S' = C_True` by auto
       then obtain L where "L \<in># D \<and> get_level L (trail S') = backtrack_level S'" using D_L by metis
       hence "conflict_is_false_with_level S''" unfolding S'' by fast
     }
     ultimately have "conflict_is_false_with_level S''" by blast
  }
  moreover
  {
    assume "conflicting S' \<noteq> C_True"
    have "no_clause_is_false S'" using `conflicting S' \<noteq> C_True`  by auto
    hence "conflict_is_false_with_level S''" using calculation(3) by blast
  }
  ultimately show ?case by fast
qed


lemma rtranclp_cdcl_s_no_littler_confl_inv:
  assumes "cdcl_s\<^sup>*\<^sup>* S S'"
  and n_l: "no_littler_confl S"
  and "conflict_is_false_with_level S"
  and "cdcl_M_level_inv S"
  and "no_clause_is_false S"
  and "distinct_cdcl_state S"
  and "cdcl_conflicting S"
  and "all_decomposition_implies (clauses S) (get_all_marked_decomposition (trail S))"
  and "cdcl_learned_clause S"
  and "no_strange_atm S"
  shows "no_littler_confl S' \<and> conflict_is_false_with_level S'"
  using assms
proof (induct rule: rtranclp.induct)
  case (rtrancl_refl S)
  thus ?case by auto
next
  case (rtrancl_into_rtrancl S S' S'') note st = this(1) and IH = this(2) and cls_false = this(7) and no_dup = this(8)
  have "no_littler_confl S'" and "conflict_is_false_with_level S'"
    using IH[OF rtrancl_into_rtrancl.prems] by blast+
  moreover have "cdcl_M_level_inv S'"
    using  st rtrancl_into_rtrancl.prems(3) rtranclp_cdcl_s_rtranclp_cdcl
    by (blast intro: rtranclp_cdcl_consistent_inv)+
  moreover have "no_clause_is_false S'"
    using st cls_false by (metis (mono_tags, lifting) cdcl_s_not_non_negated_clauses  rtranclp.simps)
  moreover have "distinct_cdcl_state S'"
    using rtanclp_distinct_cdcl_state_inv st no_dup rtranclp_cdcl_s_rtranclp_cdcl by blast
  moreover have "cdcl_conflicting S'"
    using rtranclp_cdcl_all_inv(6)[of S S'] st rtrancl_into_rtrancl.prems
    by (simp add: rtranclp_cdcl_s_rtranclp_cdcl)
  ultimately show ?case using cdcl_s_no_littler_confl_inv_ex_lit_of_max_level[OF rtrancl_into_rtrancl.hyps(3)] by fast
qed



lemma full_cdcl_cp_exists_conflict:
  assumes "full cdcl_cp S' S''"
  and "\<not>(\<forall>D\<in>clauses S' \<union> learned_clauses S'. \<not> trail S' \<Turnstile>as CNot D)"
  and "conflicting S' = C_True"
  shows "conflict S' S''"
proof -
  have "\<exists>S''. conflict S' S''" using assms(2,3) by (auto simp add:  conflict.simps)
  hence "cdcl_cp\<^sup>+\<^sup>+ S' S''" using assms(1) cdcl_cp.conflict' unfolding full_def by blast
  thus ?thesis using rtranclp_cdcl_cp_exists_conflict[OF _ assms(2,3)] by auto
qed

lemma cdcl_s_exists_conflict:
  assumes "cdcl_s S' S''"
  and "\<not>(\<forall>D\<in>clauses S' \<union> learned_clauses S'. \<not> trail S' \<Turnstile>as CNot D)"
  and "conflicting S' = C_True"
  shows "conflict S' S''"
  using assms
  by (induct rule: cdcl_s.induct)
     (metis full_cdcl_cp_exists_conflict is_conflicting_exists_conflict)+

lemma cdcl_s_conflict_is_false_with_level_inv:
  assumes "cdcl_s S S'"
  and "conflict_is_false_with_level S"
  and "distinct_cdcl_state S"
  and "cdcl_conflicting S"
  and "cdcl_M_level_inv S"
  and "no_clause_is_false S"
  and "no_littler_confl S"
  shows "conflict_is_false_with_level S'"
  using assms
proof (induct rule: cdcl_s.induct)
  case (conflict' S S')
  thus ?case unfolding full_def
    by (metis (mono_tags, lifting) tranclp_cdcl_co_conflict_ex_lit_of_max_level)
next
  case (other' S S' S'') note o = this(1) and st = this(4) and confl = this(5) and no_dup = this(6) and conf = this(7) and lev = this(8) and n_f = this(9) and little = this(10)
  have st: "cdcl_cp\<^sup>*\<^sup>* S' S''" using st unfolding full0_def by blast
  have confl': "conflict_is_false_with_level S'" using cdcl_o_conflict_is_false_with_level_inv[OF o confl no_dup conf lev] .
  have lev': "cdcl_M_level_inv S'" using cdcl_consistent_inv lev o other by blast
  { assume "no_clause_is_false S'"
    hence ?case using rtranclp_cdcl_co_conflict_ex_lit_of_max_level[OF st _ confl' lev'] by blast
  }
  also {
     assume "conflicting S' = C_True" and D_L: "\<forall>D \<in> clauses S' \<union> learned_clauses S'. trail S' \<Turnstile>as CNot D \<longrightarrow> (\<exists>L. L \<in># D \<and> get_level L (trail S') = backtrack_level S')"
     { assume "\<forall>D\<in>clauses S' \<union> learned_clauses S'. \<not> trail S' \<Turnstile>as CNot D"
       hence "no_clause_is_false S'" using `conflicting S' = C_True` by simp
       hence ?case using rtranclp_cdcl_co_conflict_ex_lit_of_max_level[OF st _ confl' lev'] by blast
     }
     also {
       assume "\<not>(\<forall>D\<in>clauses S' \<union> learned_clauses S'. \<not> trail S' \<Turnstile>as CNot D)"
       then obtain D where
         "S'' = (trail S', clauses S', learned_clauses S', backtrack_level S', C_Clause D)" and
         "D \<in> clauses S' \<union> learned_clauses S'" and
         "trail S' \<Turnstile>as CNot D"
         using full0_cdcl_cp_exists_conflict[OF other'.hyps(4)] `conflicting S' = C_True` by auto
       hence ?case using D_L by fast
     }
     ultimately have ?case by blast
  }
  moreover
  {
    assume "conflicting S' \<noteq> C_True"
    have "no_clause_is_false S'" using `conflicting S' \<noteq> C_True`  by auto
    hence ?case using rtranclp_cdcl_co_conflict_ex_lit_of_max_level[OF st _ confl' lev'] by blast
  }
  ultimately show ?case
    using cdcl_o_conflict_is_no_clause_is_false[OF o confl n_f lev little] by satx
qed

lemma rtranclp_cdcl_s_conflict_is_false_with_level_inv:
  assumes "cdcl_s\<^sup>*\<^sup>* S S'"
  and "conflict_is_false_with_level S"
  and "distinct_cdcl_state S"
  and "cdcl_conflicting S"
  and "cdcl_M_level_inv S"
  and "no_clause_is_false S"
  and "no_littler_confl S"
  and "all_decomposition_implies (clauses S) (get_all_marked_decomposition (trail S))"
  and "cdcl_learned_clause S"
  and "no_strange_atm S"
  and "no_clause_is_false S"
  shows "conflict_is_false_with_level S'"
  using assms
proof (induct rule: rtranclp.induct)
  case rtrancl_refl
  thus ?case by auto
next
  case (rtrancl_into_rtrancl S S' S'')
  hence st: "cdcl_s\<^sup>*\<^sup>* S S''" by auto
  have confl: "conflict_is_false_with_level S'"
    using  rtrancl_into_rtrancl.hyps(2)[OF rtrancl_into_rtrancl.prems] by blast
  have no_dup: "distinct_cdcl_state S'"
    using rtanclp_distinct_cdcl_state_inv[OF rtranclp_cdcl_s_rtranclp_cdcl[OF rtrancl_into_rtrancl.hyps(1)]] rtrancl_into_rtrancl.prems(2) by blast
  have confl': "cdcl_conflicting S'"
    by (meson rtrancl_into_rtrancl.hyps(1) rtrancl_into_rtrancl.prems(2-4,7-9) rtranclp_cdcl_all_inv(6) rtranclp_cdcl_s_rtranclp_cdcl)
  have lev: "cdcl_M_level_inv S'"
    using rtranclp_cdcl_consistent_inv  rtrancl_into_rtrancl.hyps(1) rtrancl_into_rtrancl.prems(4) rtranclp_cdcl_s_rtranclp_cdcl by blast
  have n_l: "no_littler_confl S'"
    using rtranclp_cdcl_s_no_littler_confl_inv[OF rtrancl_into_rtrancl.hyps(1) rtrancl_into_rtrancl.prems(6,1,4,10)] by (simp add: rtrancl_into_rtrancl.prems(2,3,7,8,9))
  have "no_clause_is_false S'"
    by (metis (mono_tags, lifting) cdcl_s_not_non_negated_clauses rtrancl_into_rtrancl.hyps(1) rtrancl_into_rtrancl.prems(5) rtranclp.simps)
  thus ?case
    using cdcl_s_conflict_is_false_with_level_inv[OF rtrancl_into_rtrancl.hyps(3) confl no_dup confl' lev _ n_l] by blast
qed

subsubsection \<open>Final states are at the end\<close>
(*prop 2.10.7*)
lemma full_cdcl_s_normal_forms_non_false:
  fixes S' :: "'v cdcl_state"
  assumes full: "full0 cdcl_s (S0_cdcl N) S'"
  and no_d: "distinct_mset_set N"
  and finite: "finite (clauses (S0_cdcl N))"
  and no_empty: "\<forall>D\<in>N. D \<noteq> {#}"
  shows "(conflicting S' = C_Clause {#} \<and> unsatisfiable (clauses S')) \<or> (conflicting S' = C_True \<and> trail S' \<Turnstile>as clauses S')"
proof -
  let ?S = "S0_cdcl N"
  have termi: "\<forall>S''. \<not>cdcl_s S' S''"
  and step: "cdcl_s\<^sup>*\<^sup>* (S0_cdcl N) S'" using full unfolding full0_def by auto
  also have "all_decomposition_implies (clauses (S0_cdcl N)) (get_all_marked_decomposition (fst (S0_cdcl N)))" by auto
  hence
    decomp: "all_decomposition_implies (clauses S') (get_all_marked_decomposition (trail S'))" and
    learned: "cdcl_learned_clause S'" and
    level_inv: "cdcl_M_level_inv S'" and
    alien: "no_strange_atm S'" and
    no_dup: "distinct_cdcl_state S'" and
    confl: "cdcl_conflicting S'"
    using no_d tranclp_cdcl_s_tranclp_cdcl[of ?S S'] step rtranclp_cdcl_all_inv(1-6)[of ?S S']
    unfolding rtranclp_unfold by auto
  moreover
    have finite: "finite (clauses S')" using rtranclp_cdcl_s_no_more_clauses[OF step] finite by auto
  moreover
    have "\<forall>D\<in>N. \<not> [] \<Turnstile>as CNot D" using no_empty by auto
    hence confl_k: "conflict_is_false_with_level S'"
      using rtranclp_cdcl_s_conflict_is_false_with_level_inv[OF step] no_d by simp
  show ?thesis
    using cdcl_s_normal_forms[OF termi decomp learned level_inv alien no_dup confl finite confl_k] .
qed


lemma conflict_is_full_cdcl_cp:
  assumes cp: "conflict S S'"
  shows "full cdcl_cp S S'"
proof -
  have "cdcl_cp S S'" and "conflicting S' \<noteq> C_True" using cp cdcl_cp.intros by auto
  hence "cdcl_cp\<^sup>+\<^sup>+ S S'" by blast
  also have "no_step cdcl_cp S'"
    using `conflicting S' \<noteq> C_True` by (metis cdcl_cp_conflicting_not_empty conflicting_clause.exhaust)
  ultimately show "full cdcl_cp S S'" unfolding full_def by blast+
qed

lemma cdcl_cp_conflit_conflict:
  assumes "cdcl_cp S S''"
  and "conflict S S'"
  shows "conflict S S''"
  using assms by (induct rule: cdcl_cp.induct) blast+

lemma tranclp_cdcl_cp_conflit_conflict:
  assumes "cdcl_cp\<^sup>+\<^sup>+ S S''"
  and "conflict S S'"
  shows "conflict S S''"
  using assms
  by (induct rule: tranclp.induct) (force intro: cdcl_cp_conflit_conflict)+

lemma cdcl_s_conflit_conflict:
  assumes "cdcl_s S S''"
  and "conflict S S'"
  shows "conflict S S''"
  using assms
  apply (induct rule: cdcl_s.induct)
  unfolding full_def by (blast intro: tranclp_cdcl_cp_conflit_conflict)+

lemma cdcl_cp_fst_empty_conflicting_false:
  assumes "cdcl_cp S S'"
  and "trail S = []"
  and "conflicting S \<noteq> C_True"
  shows False
  using assms by (induct rule: cdcl_cp.induct) auto

lemma cdcl_o_fst_empty_conflicting_false:
  assumes "cdcl_o S S'"
  and "trail S = []"
  and "conflicting S \<noteq> C_True"
  shows False
  using assms by (induct rule: cdcl_o_induct) auto

lemma cdcl_s_fst_empty_conflicting_false:
  assumes "cdcl_s S S'"
  and "trail S = []"
  and "conflicting S \<noteq> C_True"
  shows False
  using assms apply (induct rule: cdcl_s.induct)
  using tranclpD cdcl_cp_fst_empty_conflicting_false unfolding full_def apply fast
  using cdcl_o_fst_empty_conflicting_false by blast

lemma full_cdcl_s_normal_forms_is_one_false:
  fixes S' :: "'v cdcl_state"
  assumes full: "full0 cdcl_s (S0_cdcl N) S'"
  and no_d: "distinct_mset_set N"
  and finite: "finite (clauses (S0_cdcl N))"
  and empty: "\<exists>D\<in>N. D = {#}"
  shows "(conflicting S' = C_Clause {#} \<and> unsatisfiable (clauses S')) \<or> (conflicting S' = C_True \<and> trail S' \<Turnstile>as clauses S')"
proof -
  let ?S = "S0_cdcl N"
  have "cdcl_s\<^sup>*\<^sup>* (S0_cdcl N) S'" and "no_step cdcl_s S'" using full unfolding full0_def by auto
  hence plus_or_eq: "cdcl_s\<^sup>+\<^sup>+ (S0_cdcl N) S' \<or> S' = ?S" unfolding rtranclp_unfold by auto
  have "\<exists>S''. conflict ?S S''" using empty by (auto simp add: conflict.simps)
  hence cdcl_s: "\<exists>S'. cdcl_s ?S S'"
    using cdcl_cp.conflict'[of ?S] conflict_is_full_cdcl_cp cdcl_s.intros(1)  by metis
  have "S' \<noteq> ?S"  using `no_step cdcl_s S'` cdcl_s by blast
  then obtain St where "cdcl_s (S0_cdcl N) St" and "cdcl_s\<^sup>*\<^sup>* St S'"
    using plus_or_eq by (metis (no_types) `cdcl_s\<^sup>*\<^sup>* (S0_cdcl N) S'` converse_rtranclpE)
  hence conf: "conflict ?S St" using cdcl_s_conflit_conflict `\<exists>S''. conflict ?S S''` by blast
  hence "conflicting St \<noteq> C_True" and "learned_clauses St = {}" and "fst ?S = []" by auto

  obtain \<alpha> where \<alpha>: "conflicting St = C_Clause \<alpha>"
    using `conflicting St \<noteq> C_True` by (case_tac "conflicting St") auto
  hence "\<alpha> = {#}" using `conflict ?S St` by (case_tac \<alpha>) auto
  moreover have St: "St = S'"
    using `cdcl_s\<^sup>*\<^sup>* St S'` `learned_clauses St = {}` `fst ?S = []` tranclpD
     by (metis (no_types) \<alpha> calculation conflict_with_false_implies_terminated rtranclpD
       tranclp_cdcl_s_tranclp_cdcl)
  moreover have "unsatisfiable N" by (meson empty satisfiable_carac true_cls_empty true_clss_def)
  moreover have "N = clauses S'" using St `cdcl_s (S0_cdcl N) St` cdcl_s_no_more_clauses by blast
  ultimately show ?thesis using `conflicting St = C_Clause \<alpha>` by auto
qed

(** prop 2.10.9*)
lemma full_cdcl_s_normal_forms:
  fixes S' :: "'v cdcl_state"
  assumes full: "full0 cdcl_s (S0_cdcl N) S'"
  and no_d: "distinct_mset_set N"
  and finite: "finite (clauses (S0_cdcl N))"
  shows "(conflicting S' = C_Clause {#} \<and> unsatisfiable (clauses S')) \<or> (conflicting S' = C_True \<and> trail S' \<Turnstile>as clauses S')"
  using assms full_cdcl_s_normal_forms_is_one_false full_cdcl_s_normal_forms_non_false by blast

lemma full_cdcl_s_normal_forms':
  fixes S' :: "'v cdcl_state"
  assumes full: "full0 cdcl_s (S0_cdcl N) S'"
  and no_d: "distinct_mset_set N"
  and finite: "finite (clauses (S0_cdcl N))"
  shows "(conflicting S' = C_Clause {#} \<and> unsatisfiable (clauses S')) 
    \<or> (conflicting S' = C_True \<and> trail S' \<Turnstile>as clauses S' \<and> satisfiable (clauses S'))"
proof -
  consider 
      (confl) "conflicting S' = C_Clause {#}" and " unsatisfiable (clauses S')"
    | (sat) "conflicting S' = C_True" and "trail S' \<Turnstile>as clauses S'"
    using full_cdcl_s_normal_forms[OF assms] by auto
  thus ?thesis
    proof cases
      case confl
      thus ?thesis by auto
    next
      case sat
      have "cdcl_M_level_inv (S0_cdcl N)" by auto
      hence "cdcl_M_level_inv S'" 
        using full rtranclp_cdcl_s_consistent_inv unfolding full0_def by blast
      hence "consistent_interp (lits_of (trail S'))" unfolding cdcl_M_level_inv_def by blast
      also have "lits_of (trail S') \<Turnstile>s clauses S'"
        using sat(2) by (auto simp add: true_annots_def true_annot_def true_clss_def)
      ultimately have "satisfiable (clauses S')" by simp
      thus ?thesis using sat by blast
    qed
qed
end
