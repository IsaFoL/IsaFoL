theory CDCL_W_Level
imports
  Entailment_Definition.Partial_Annotated_Herbrand_Interpretation
begin


subsubsection \<open>Level of literals and clauses\<close>
text \<open>Getting the level of a variable, implies that the list has to be reversed. Here is the
  function \<^emph>\<open>after\<close> reversing.\<close>

definition count_decided :: "('v, 'b, 'm) annotated_lit list \<Rightarrow> nat" where
"count_decided l = length (filter is_decided l)"

definition get_level :: "('v, 'm) ann_lits \<Rightarrow> 'v literal \<Rightarrow> nat" where
"get_level S L = length (filter is_decided (dropWhile (\<lambda>S. atm_of (lit_of S) \<noteq> atm_of L) S))"

lemma get_level_uminus[simp]: \<open>get_level M (-L) = get_level M L\<close>
  by (auto simp: get_level_def)

lemma get_level_Neg_Pos: \<open>get_level M (Neg L) = get_level M (Pos L)\<close>
  unfolding get_level_def by auto

lemma count_decided_0_iff:
  \<open>count_decided M = 0 \<longleftrightarrow> (\<forall>L \<in> set M. \<not>is_decided L)\<close>
  by (auto simp: count_decided_def filter_empty_conv)

lemma
  shows
    count_decided_nil[simp]: \<open>count_decided [] = 0\<close> and
    count_decided_cons[simp]:
      \<open>count_decided (a # M) = (if is_decided a then Suc (count_decided M) else count_decided M)\<close> and
    count_decided_append[simp]:
      \<open>count_decided (M @ M') = count_decided M + count_decided M'\<close>
  by (auto simp: count_decided_def)

lemma atm_of_notin_get_level_eq_0[simp]:
  assumes "undefined_lit M L"
  shows "get_level M L = 0"
  using assms by (induct M rule: ann_lit_list_induct) (auto simp: get_level_def defined_lit_map)

lemma get_level_ge_0_atm_of_in:
  assumes "get_level M L > n"
  shows "atm_of L \<in> atm_of ` lits_of_l M"
  using atm_of_notin_get_level_eq_0[of M L] assms unfolding defined_lit_map
  by (auto simp: lits_of_def simp del: atm_of_notin_get_level_eq_0)

text \<open>In @{const get_level} (resp. @{const get_level}), the beginning (resp. the end) can be
  skipped if the literal is not in the beginning (resp. the end).\<close>
lemma get_level_skip[simp]:
  assumes "undefined_lit M L"
  shows "get_level (M @ M') L = get_level M' L"
  using assms by (induct M rule: ann_lit_list_induct) (auto simp: get_level_def defined_lit_map)

text \<open>If the literal is at the beginning, then the end can be skipped\<close>
lemma get_level_skip_end[simp]:
  assumes "defined_lit M L"
  shows "get_level (M @ M') L = get_level M L + count_decided M'"
  using assms by (induct M' rule: ann_lit_list_induct)
    (auto simp: lits_of_def get_level_def count_decided_def defined_lit_map)

lemma get_level_skip_beginning[simp]:
  assumes "atm_of L' \<noteq> atm_of (lit_of K)"
  shows "get_level (K # M) L' = get_level M L'"
  using assms by (auto simp: get_level_def)

lemma get_level_take_beginning[simp]:
  assumes "atm_of L' = atm_of (lit_of K)"
  shows "get_level (K # M) L' = count_decided (K # M)"
  using assms by (auto simp: get_level_def count_decided_def)

lemma get_level_cons_if:
  \<open>get_level (K # M) L' =
    (if atm_of L' = atm_of (lit_of K) then count_decided (K # M) else get_level M L')\<close>
  by auto

lemma get_level_skip_beginning_not_decided[simp]:
  assumes "undefined_lit S L"
  and "\<forall>s\<in>set S. \<not>is_decided s"
  shows "get_level (M @ S) L = get_level M L"
  using assms apply (induction S rule: ann_lit_list_induct)
    apply auto[2]
  apply (case_tac "atm_of L \<in> atm_of ` lits_of_l M")
   apply (auto simp: image_iff lits_of_def filter_empty_conv count_decided_def defined_lit_map
      dest: set_dropWhileD)
  done

lemma get_level_skip_all_not_decided[simp]:
  fixes M
  assumes "\<forall>m\<in>set M. \<not> is_decided m"
  shows "get_level M L = 0"
  using assms by (auto simp: filter_empty_conv get_level_def dest: set_dropWhileD)

text \<open>the @{term "{#0#}"} is there to ensures that the set is not empty.\<close>
definition get_maximum_level :: "('a, 'b) ann_lits \<Rightarrow> 'a clause \<Rightarrow> nat"
  where
"get_maximum_level M D = Max_mset ({#0#} + image_mset (get_level M) D)"

lemma get_maximum_level_ge_get_level:
  "L \<in># D \<Longrightarrow> get_maximum_level M D \<ge> get_level M L"
  unfolding get_maximum_level_def by auto

lemma get_maximum_level_empty[simp]:
  "get_maximum_level M {#} = 0"
  unfolding get_maximum_level_def by auto

lemma get_maximum_level_exists_lit_of_max_level:
  "D \<noteq> {#} \<Longrightarrow> \<exists>L\<in># D. get_level M L = get_maximum_level M D"
  unfolding get_maximum_level_def
  apply (induct D)
   apply simp
  by (rename_tac x D, case_tac "D = {#}") (auto simp add: max_def)

lemma get_maximum_level_empty_list[simp]:
  "get_maximum_level [] D = 0"
  unfolding get_maximum_level_def by (simp add: image_constant_conv)

lemma get_maximum_level_add_mset:
  "get_maximum_level M (add_mset L D) = max (get_level M L) (get_maximum_level M D)"
  unfolding get_maximum_level_def by simp

lemma get_level_append_if:
  \<open>get_level (M @ M') L = (if defined_lit M L then get_level M L + count_decided M'
            else get_level M' L)\<close>
  by (auto)

text \<open>Do mot activate as [simp] rules. It breaks everything.\<close>
lemma get_maximum_level_single:
  \<open>get_maximum_level M {#x#} = get_level M x\<close>
  by (auto simp: get_maximum_level_add_mset)

lemma get_maximum_level_plus:
  "get_maximum_level M (D + D') = max (get_maximum_level M D) (get_maximum_level M D')"
  by (induction D) (simp_all add: get_maximum_level_add_mset)

lemma get_maximum_level_cong:
  assumes \<open>\<forall>L \<in># D. get_level M L = get_level M' L\<close>
  shows \<open>get_maximum_level M D = get_maximum_level M' D\<close>
  using assms by (induction D) (auto simp: get_maximum_level_add_mset)

lemma get_maximum_level_exists_lit:
  assumes n: "n > 0"
  and max: "get_maximum_level M D = n"
  shows "\<exists>L \<in>#D. get_level M L = n"
proof -
  have f: "finite (insert 0 ((\<lambda>L. get_level M L) ` set_mset D))" by auto
  then have "n \<in> ((\<lambda>L. get_level M L) ` set_mset D)"
    using n max Max_in[OF f] unfolding get_maximum_level_def by simp
  then show "\<exists>L \<in># D. get_level M L = n" by auto
qed

lemma get_maximum_level_skip_first[simp]:
  assumes "atm_of (lit_of K) \<notin> atms_of D"
  shows "get_maximum_level (K # M) D = get_maximum_level M D"
  using assms unfolding get_maximum_level_def atms_of_def
    atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set
  by (smt atm_of_in_atm_of_set_in_uminus get_level_skip_beginning image_iff lit_of.simps(2)
      multiset.map_cong0)

lemma get_maximum_level_skip_beginning:
  assumes DH: "\<forall>x \<in># D. undefined_lit c x"
  shows "get_maximum_level (c @ H) D = get_maximum_level H D"
proof -
  have "(get_level (c @ H)) ` set_mset D = (get_level H) ` set_mset D"
    apply (rule image_cong)
     apply (simp; fail)
    using DH unfolding atms_of_def by auto
  then show ?thesis using DH unfolding get_maximum_level_def by auto
qed

lemma get_maximum_level_D_single_propagated:
  "get_maximum_level [Propagated x21 x22] D = 0"
  unfolding get_maximum_level_def by (simp add: image_constant_conv)

lemma get_maximum_level_union_mset:
  "get_maximum_level M (A \<union># B) = get_maximum_level M (A + B)"
  unfolding get_maximum_level_def by (auto simp: image_Un)

lemma count_decided_rev[simp]:
  "count_decided (rev M) = count_decided M"
  by (auto simp: count_decided_def rev_filter[symmetric])

lemma count_decided_ge_get_level:
  "count_decided M \<ge> get_level M L"
  by (induct M rule: ann_lit_list_induct)
    (auto simp add: count_decided_def le_max_iff_disj get_level_def)

lemma count_decided_ge_get_maximum_level:
  "count_decided M \<ge> get_maximum_level M D"
  using get_maximum_level_exists_lit_of_max_level unfolding Bex_def
  by (metis get_maximum_level_empty count_decided_ge_get_level le0)

lemma get_level_last_decided_ge:
   \<open>defined_lit (c @ [Decided K]) L' \<Longrightarrow> 0 < get_level (c @ [Decided K]) L'\<close>
  by (induction c) (auto simp: defined_lit_cons get_level_cons_if)

lemma get_maximum_level_mono:
  \<open>D \<subseteq># D' \<Longrightarrow> get_maximum_level M D \<le> get_maximum_level M D'\<close>
  unfolding get_maximum_level_def by auto

fun get_all_mark_of_propagated where
"get_all_mark_of_propagated [] = []" |
"get_all_mark_of_propagated (Decided _ # L) = get_all_mark_of_propagated L" |
"get_all_mark_of_propagated (Propagated _ mark # L) = mark # get_all_mark_of_propagated L"

lemma get_all_mark_of_propagated_append[simp]:
  "get_all_mark_of_propagated (A @ B) = get_all_mark_of_propagated A @ get_all_mark_of_propagated B"
  by (induct A rule: ann_lit_list_induct) auto

lemma get_all_mark_of_propagated_tl_proped:
  \<open>M \<noteq> [] \<Longrightarrow> is_proped (hd M) \<Longrightarrow> get_all_mark_of_propagated (tl M) = tl (get_all_mark_of_propagated M)\<close>
  by (induction M rule: ann_lit_list_induct) auto


subsubsection \<open>Properties about the levels\<close>

lemma atm_lit_of_set_lits_of_l:
  "(\<lambda>l. atm_of (lit_of l)) ` set xs = atm_of ` lits_of_l xs"
  unfolding lits_of_def by auto

text \<open>Before I try yet another time to prove that I can remove the assumption \<^term>\<open>no_dup M\<close>:
  It does not work. The problem is that \<^term>\<open>get_level M K = Suc i\<close> peaks the first occurrence
  of the literal \<^term>\<open>K\<close>. This is for example an issue for the trail \<^term>\<open>replicate n (Decided K)\<close>.
  An explicit counter-example is below.
\<close>
lemma le_count_decided_decomp:
  assumes \<open>no_dup M\<close>
  shows \<open>i < count_decided M \<longleftrightarrow> (\<exists>c K c'. M = c @ Decided K # c' \<and> get_level M K = Suc i)\<close>
    (is "?A \<longleftrightarrow> ?B")
proof
  assume ?B
  then obtain c K c' where
    "M = c @ Decided K # c'" and "get_level M K = Suc i"
    by blast
  then show ?A using count_decided_ge_get_level[of M K] by auto
next
  assume ?A
  then show ?B
    using \<open>no_dup M\<close>
  proof (induction M rule: ann_lit_list_induct)
    case Nil
    then show ?case by simp
  next
    case (Decided L M) note IH = this(1) and i = this(2) and n_d = this(3)
    then have n_d_M: "no_dup M" by simp
    show ?case
    proof (cases "i < count_decided M")
      case True
      then obtain c K c' where
	M: "M = c @ Decided K # c'" and lev_K: "get_level M K = Suc i"
	using IH n_d_M by blast
      show ?thesis
	apply (rule exI[of _ "Decided L # c"])
	apply (rule exI[of _ K])
	apply (rule exI[of _ c'])
	using lev_K n_d unfolding M by (auto simp: get_level_def defined_lit_map)
    next
      case False
      show ?thesis
	apply (rule exI[of _ "[]"])
	apply (rule exI[of _ L])
	apply (rule exI[of _ M])
	using False i by (auto simp: get_level_def count_decided_def)
    qed
    next
      case (Propagated L mark' M) note i = this(2) and IH = this(1) and n_d = this(3)
      then obtain c K c' where
	M: "M = c @ Decided K # c'" and lev_K: "get_level M K = Suc i"
	by (auto simp: count_decided_def)
      show ?case
	apply (rule exI[of _ "Propagated L mark' # c"])
	apply (rule exI[of _ "K"])
	apply (rule exI[of _ "c'"])
	using lev_K n_d unfolding M by (auto simp: atm_lit_of_set_lits_of_l get_level_def
	  defined_lit_map)
    qed
qed

text \<open>The counter-example if the assumption \<^term>\<open>no_dup M\<close>.\<close>
lemma
  fixes K
  defines \<open>M \<equiv> replicate 3 (Decided K)\<close>
  defines \<open>i \<equiv> 1\<close>
  assumes \<open>i < count_decided M \<longleftrightarrow> (\<exists>c K c'. M = c @ Decided K # c' \<and> get_level M K = Suc i)\<close>
  shows False
  using assms(3-) unfolding M_def i_def numeral_3_eq_3
  by (auto simp: Cons_eq_append_conv)

lemma Suc_count_decided_gt_get_level:
  \<open>get_level M L < Suc (count_decided M)\<close>
  by (induction M rule: ann_lit_list_induct) (auto simp: get_level_cons_if)

lemma get_level_neq_Suc_count_decided[simp]:
  \<open>get_level M L \<noteq> Suc (count_decided M)\<close>
  using Suc_count_decided_gt_get_level[of M L] by auto

lemma length_get_all_ann_decomposition: \<open>length (get_all_ann_decomposition M) = 1+count_decided M\<close>
  by (induction M rule: ann_lit_list_induct) auto

lemma get_maximum_level_remove_non_max_lvl:
   \<open>get_level M a < get_maximum_level M D \<Longrightarrow>
  get_maximum_level M (remove1_mset a D) = get_maximum_level M D\<close>
  by (cases \<open>a \<in># D\<close>)
    (auto dest!: multi_member_split simp: get_maximum_level_add_mset)

lemma exists_lit_max_level_in_negate_ann_lits:
  \<open>negate_ann_lits M \<noteq> {#} \<Longrightarrow> \<exists>L\<in>#negate_ann_lits M. get_level M L = count_decided M\<close>
  by (cases \<open>M\<close>) (auto simp: negate_ann_lits_def)
lemma get_maximum_level_eq_count_decided_iff:
  \<open>ya \<noteq> {#} \<Longrightarrow> get_maximum_level xa ya = count_decided xa \<longleftrightarrow> (\<exists>L \<in># ya. get_level xa L = count_decided xa)\<close>
  apply (rule iffI)
  defer
  subgoal
    using count_decided_ge_get_maximum_level[of xa]
    apply (auto dest!: multi_member_split dest: le_antisym simp: get_maximum_level_add_mset max_def)
    using le_antisym by blast
  subgoal
    using get_maximum_level_exists_lit_of_max_level[of ya xa]
    by auto
  done

definition card_max_lvl where
  \<open>card_max_lvl M C \<equiv> size (filter_mset (\<lambda>L. get_level M L = count_decided M) C)\<close>

lemma card_max_lvl_add_mset: \<open>card_max_lvl M (add_mset L C) =
  (if get_level M L = count_decided M then 1 else 0) +
    card_max_lvl M C\<close>
  by (auto simp: card_max_lvl_def)

lemma card_max_lvl_empty[simp]: \<open>card_max_lvl M {#} = 0\<close>
  by (auto simp: card_max_lvl_def)

lemma card_max_lvl_all_poss:
   \<open>card_max_lvl M C = card_max_lvl M (poss (atm_of `# C))\<close>
  unfolding card_max_lvl_def
  apply (induction C)
  subgoal by auto
  subgoal for L C
    using get_level_uminus[of M L]
    by (cases L) (auto)
  done

lemma card_max_lvl_distinct_cong:
  assumes
    \<open>\<And>L. get_level M (Pos L) = count_decided M \<Longrightarrow> (L \<in> atms_of C) \<Longrightarrow> (L \<in> atms_of C')\<close> and
    \<open>\<And>L. get_level M (Pos L) = count_decided M \<Longrightarrow> (L \<in> atms_of C') \<Longrightarrow> (L \<in> atms_of C)\<close> and
    \<open>distinct_mset C\<close> \<open>\<not>tautology C\<close> and
    \<open>distinct_mset C'\<close> \<open>\<not>tautology C'\<close>
  shows \<open>card_max_lvl M C = card_max_lvl M C'\<close>
proof -
  have [simp]: \<open>NO_MATCH (Pos x) L \<Longrightarrow> get_level M L = get_level M (Pos (atm_of L))\<close> for x L
    by (simp add: get_level_def)
  have [simp]: \<open>atm_of L \<notin> atms_of C' \<longleftrightarrow> L \<notin># C' \<and> -L \<notin># C'\<close> for L C'
    by (cases L) (auto simp: atm_iff_pos_or_neg_lit)
  then have [iff]: \<open>atm_of L \<in> atms_of C' \<longleftrightarrow> L \<in># C' \<or> -L \<in># C'\<close> for L C'
    by blast
  have H: \<open>distinct_mset {#L \<in># poss (atm_of `# C). get_level M L = count_decided M#}\<close>
    if \<open>distinct_mset C\<close> \<open>\<not>tautology C\<close> for C
    using that by (induction C) (auto simp: tautology_add_mset atm_of_eq_atm_of)
  show ?thesis
    apply (subst card_max_lvl_all_poss)
    apply (subst (2) card_max_lvl_all_poss)
    unfolding card_max_lvl_def
    apply (rule arg_cong[of _ _ size])
    apply (rule distinct_set_mset_eq)
    subgoal by (rule H) (use assms in fast)+
    subgoal by (rule H) (use assms in fast)+
    subgoal using assms by (auto simp: atms_of_def imageI image_iff) blast+
    done
qed

lemma get_maximum_level_card_max_lvl_ge1:
  \<open>count_decided xa > 0 \<Longrightarrow> get_maximum_level xa ya = count_decided xa \<longleftrightarrow> card_max_lvl xa ya > 0\<close>
  apply (cases \<open>ya = {#}\<close>)
  subgoal by auto
  subgoal
    by (auto simp: card_max_lvl_def get_maximum_level_eq_count_decided_iff dest: multi_member_split
      dest!: multi_nonempty_split[of \<open>filter_mset _ _\<close>] filter_mset_eq_add_msetD
      simp flip: nonempty_has_size)
  done

lemma card_max_lvl_remove_hd_trail_iff:
  \<open>xa \<noteq> [] \<Longrightarrow> - lit_of (hd xa) \<in># ya \<Longrightarrow> 0 < card_max_lvl xa (remove1_mset (- lit_of (hd xa)) ya) \<longleftrightarrow> Suc 0 < card_max_lvl xa ya\<close>
  by (cases xa)
    (auto dest!: multi_member_split simp: card_max_lvl_add_mset)

lemma card_max_lvl_Cons:
  assumes \<open>no_dup (L # a)\<close> \<open>distinct_mset y\<close>\<open>\<not>tautology y\<close> \<open>\<not>is_decided L\<close>
  shows \<open>card_max_lvl (L # a) y =
    (if (lit_of L \<in># y \<or> -lit_of L \<in># y) \<and> count_decided a \<noteq> 0 then card_max_lvl a y + 1
    else card_max_lvl a y)\<close>
proof -
  have [simp]: \<open>count_decided a = 0 \<Longrightarrow> get_level a L = 0\<close> for L
    by (simp add: count_decided_0_iff)
  have [simp]: \<open>lit_of L \<notin># A \<Longrightarrow>
         - lit_of L \<notin># A \<Longrightarrow>
          {#La \<in># A. La \<noteq> lit_of L \<and> La \<noteq> - lit_of L \<longrightarrow> get_level a La = b#} =
          {#La \<in># A. get_level a La = b#}\<close> for A b
    apply (rule filter_mset_cong)
     apply (rule refl)
    by auto
  show ?thesis
    using assms by (auto simp: card_max_lvl_def get_level_cons_if tautology_add_mset
        atm_of_eq_atm_of
        dest!: multi_member_split)
qed

lemma card_max_lvl_tl:
  assumes \<open>a \<noteq> []\<close> \<open>distinct_mset y\<close>\<open>\<not>tautology y\<close> \<open>\<not>is_decided (hd a)\<close> \<open>no_dup a\<close>
   \<open>count_decided a \<noteq> 0\<close>
  shows \<open>card_max_lvl (tl a) y =
      (if (lit_of(hd a) \<in># y \<or> -lit_of(hd a) \<in># y)
        then card_max_lvl a y - 1 else card_max_lvl a y)\<close>
  using assms by (cases a) (auto simp: card_max_lvl_Cons)

text \<open>This is the critical theorem for vivification: propagations are entailed by the decisions on the lower level.\<close>
lemma all_decomposition_implies_propagations_upto:
  assumes \<open>all_decomposition_implies N (get_all_ann_decomposition M)\<close> \<open>no_dup M\<close>
  shows \<open>N \<union> {unmark L |L. is_decided L \<and> L \<in> set M \<and> get_level M (lit_of L) \<le> k} \<Turnstile>ps unmark_l (filter (\<lambda>L. get_level M (lit_of L) \<le> k) M)\<close>
proof -
  let ?DECO = \<open>\<lambda>M k. unmark ` set (filter (\<lambda>L. is_decided L \<and> L \<in> set M \<and> get_level M (lit_of L) \<le> k) M)\<close>
  have 1: \<open>{unmark L |L. is_decided L \<and> L \<in> set M \<and> get_level M (lit_of L) \<le> k} = ?DECO M k\<close> for M k
    by auto
  show ?thesis
    using assms unfolding 1
  proof (induction M arbitrary: k rule: ann_lit_list_induct)
    case Nil
    then show ?case by auto
  next
    case (Decided L xs) note IH = this(1) and decomp = this(2) and nd = this(3)
    then have \<open>all_decomposition_implies N (get_all_ann_decomposition xs)\<close>
      by fastforce
    then have IH: \<open>N \<union> unmark_l (filter (\<lambda>L. is_decided L \<and> L \<in> set xs \<and> get_level xs (lit_of L) \<le> k) xs) \<Turnstile>ps
      unmark_l (filter (\<lambda>L. get_level xs (lit_of L) \<le> k) xs)\<close>
      using IH decomp nd by auto
    have \<open>count_decided xs \<le> k \<Longrightarrow> {x. is_decided x \<and> x \<in> set xs \<and> get_level xs (lit_of x) \<le> k} =
      {x. is_decided x \<and> x \<in> set xs}\<close>
      using count_decided_ge_get_level[of xs] le_trans by blast
    then have 0: \<open>?DECO (Decided L # xs) k = ?DECO xs k \<union> (if k > count_decided xs then {{#L#}} else {})\<close>
      using nd
      apply (auto simp: get_level_cons_if image_iff dest: undefined_notin)
      apply (metis defined_lit_Pos_atm_iff undefined_notin)
      by (metis (no_types, lifting) defined_lit_map undefined_notin)
    moreover have \<open>unmark_l (filter (\<lambda>La. get_level (Decided L # xs) (lit_of La) \<le> k) (Decided L # xs)) =
      unmark_l (filter (\<lambda>La. get_level xs (lit_of La) \<le> k) xs) \<union> (if k > count_decided xs then {{#L#}} else {})\<close>
      using nd apply (auto simp: get_level_cons_if image_iff dest: undefined_notin)
      apply (metis defined_lit_Pos_atm_iff undefined_notin)
      by (metis (no_types, lifting) defined_lit_map undefined_notin)
    ultimately show ?case
      using IH by auto
  next
    case (Propagated L C xs) note IH = this(1) and decomp = this(2) and nd = this(3)
    have 0: \<open>?DECO (Propagated L C # xs) k = ?DECO xs k\<close>
      using nd apply (auto simp: get_level_cons_if dest: undefined_notin)
      apply (metis defined_lit_Pos_atm_iff undefined_notin)
      by (metis (mono_tags, lifting) defined_lit_map mem_Collect_eq rev_image_eqI)
    have \<open>all_decomposition_implies N (get_all_ann_decomposition xs)\<close>
      using decomp by (metis all_decomposition_implies_mono_right append_Cons append_Nil)
    then have IH: \<open>N \<union> ?DECO (Propagated L C # xs) k \<Turnstile>ps unmark_l (filter (\<lambda>L. get_level xs (lit_of L) \<le> k) xs)\<close>
      using IH nd "0" by auto
    have unm: \<open>unmark_s {x \<in> set xs. get_level (Propagated L C # xs) (lit_of x) \<le> k} = unmark_s {x \<in> set xs. get_level xs (lit_of x) \<le> k}\<close>
      using nd apply (auto simp: get_level_cons_if dest: undefined_notin)
      apply (metis defined_lit_Pos_atm_iff undefined_notin)
      by (smt (z3) defined_lit_Pos_atm_iff imageI mem_Collect_eq undefined_notin)
    moreover have \<open>count_decided xs \<le> k \<Longrightarrow> {x. is_decided x \<and> x \<in> set xs \<and> get_level xs (lit_of x) \<le> k} =
      {x. is_decided x \<and> x \<in> set xs}\<close>
      using count_decided_ge_get_level[of xs] le_trans by blast
    moreover have 3: \<open>{unmark La |La. is_decided La \<and> La \<in> set (Propagated L C # xs)} = unmark ` set (filter (\<lambda>L. is_decided L\<and> L \<in> set xs) xs)\<close>
      using nd by auto
    ultimately show ?case
      using IH all_decomposition_implies_propagated_lits_are_implied[OF decomp] unfolding 0 1 3
      by (auto simp: unm ac_simps)[]
  qed
qed

end
