theory CDCL_W_Level
imports Partial_Annotated_Clausal_Logic
begin

subsubsection \<open>Level of literals and clauses\<close>
text \<open>Getting the level of a variable, implies that the list has to be reversed. Here is the
  function after reversing.\<close>

abbreviation count_decided :: "('v, 'm) ann_lits \<Rightarrow> nat" where
"count_decided l \<equiv> length (filter is_decided l)"

abbreviation get_level :: "('v, 'm) ann_lits \<Rightarrow> 'v literal \<Rightarrow> nat" where
"get_level S L \<equiv> length (filter is_decided (dropWhile (\<lambda>S. atm_of (lit_of S) \<noteq> atm_of L) S))"

lemma get_level_uminus: "get_level M (-L) = get_level M L"
  by auto

lemma atm_of_notin_get_rev_level_eq_0[simp]:
  assumes "atm_of L \<notin> atm_of ` lits_of_l M"
  shows "get_level M L = 0"
  using assms by (induct M rule: ann_lit_list_induct) auto

lemma get_level_ge_0_atm_of_in:
  assumes "get_level M L > n"
  shows "atm_of L \<in> atm_of ` lits_of_l M"
  using assms by (induct M arbitrary: n rule: ann_lit_list_induct) fastforce+

text \<open>In @{const get_level} (resp. @{const get_level}), the beginning (resp. the end) can be
  skipped if the literal is not in the beginning (resp. the end).\<close>
lemma get_rev_level_skip[simp]:
  assumes "atm_of L \<notin> atm_of ` lits_of_l M"
  shows "get_level (M @ M') L = get_level M' L"
  using assms by (induct M rule: ann_lit_list_induct) auto

text \<open>If the literal is at the beginning, then the end can be skipped\<close>
lemma get_rev_level_skip_end[simp]:
  assumes "atm_of L \<in> atm_of ` lits_of_l M"
  shows "get_level (M @ M') L = get_level M L + length (filter is_decided M')"
  using assms by (induct M' rule: ann_lit_list_induct) (auto simp: lits_of_def)

lemma get_level_skip_beginning:
  assumes "atm_of L' \<noteq> atm_of (lit_of K)"
  shows "get_level (K # M) L' = get_level M L'"
  using assms by auto

lemma get_level_skip_beginning_not_decided[simp]:
  assumes "atm_of L \<notin> atm_of ` lits_of_l S"
  and "\<forall>s\<in>set S. \<not>is_decided s"
  shows "get_level (M @ S) L = get_level M L"
  using assms apply (induction S rule: ann_lit_list_induct)
    apply auto[2]
  apply (case_tac "atm_of L \<in> atm_of ` lits_of_l M")
  apply (auto simp: image_iff lits_of_def filter_empty_conv dest: set_dropWhileD)
  done

lemma get_level_skip_in_all_not_decided:
  fixes M :: "('a, 'b) ann_lits" and L :: "'a literal"
  assumes "\<forall>m\<in>set M. \<not> is_decided m"
  and "atm_of L \<in> atm_of ` lits_of_l M"
  shows "get_level M L = 0"
  using assms by (induction M rule: ann_lit_list_induct) auto

lemma get_level_skip_all_not_decided[simp]:
  fixes M
  assumes "\<forall>m\<in>set M. \<not> is_decided m"
  shows "get_level M L = 0"
  using assms by (auto simp: filter_empty_conv dest: set_dropWhileD)

abbreviation "MMax M \<equiv> Max (set_mset M)"

text \<open>the @{term "{#0#}"} is there to ensures that the set is not empty.\<close>
definition get_maximum_level :: "('a, 'b) ann_lits \<Rightarrow> 'a literal multiset \<Rightarrow> nat"
  where
"get_maximum_level M D = MMax ({#0#} + image_mset (get_level M) D)"

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
  by (rename_tac D x, case_tac "D = {#}") (auto simp add: max_def)

lemma get_maximum_level_empty_list[simp]:
  "get_maximum_level [] D = 0"
  unfolding get_maximum_level_def by (simp add: image_constant_conv)

lemma get_maximum_level_single[simp]:
  "get_maximum_level M {#L#} = get_level M L"
  unfolding get_maximum_level_def by simp

lemma get_maximum_level_plus:
  "get_maximum_level M (D + D') = max (get_maximum_level M D) (get_maximum_level M D')"
  by (induct D) (auto simp add: get_maximum_level_def)

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
  assumes "atm_of L \<notin> atms_of D"
  shows "get_maximum_level (Propagated L C # M) D = get_maximum_level M D"
  using assms unfolding get_maximum_level_def atms_of_def
    atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set
  by (smt atm_of_in_atm_of_set_in_uminus get_level_skip_beginning image_iff ann_lit.sel(2)
    multiset.map_cong0)

lemma get_maximum_level_skip_beginning:
  assumes DH: "\<forall>x \<in> atms_of D. x \<notin> atm_of ` lits_of_l c"
  shows "get_maximum_level (c @ H) D = get_maximum_level H D"
proof -
  have "(get_level (c @ H)) ` set_mset D = (get_level H) ` set_mset D"
    apply (rule image_cong)
     apply simp
    using DH unfolding atms_of_def by auto
  then show ?thesis using DH unfolding get_maximum_level_def by auto
qed

lemma get_maximum_level_D_single_propagated:
  "get_maximum_level [Propagated x21 x22] D = 0"
  unfolding get_maximum_level_def by (simp add: image_constant_conv)

lemma get_maximum_level_skip_un_decided_not_present:
  assumes
    "\<forall>L\<in>#D. atm_of L \<notin> atm_of ` lits_of_l M" and
    "\<forall>m\<in>set M. \<not> is_decided m"
  shows "get_maximum_level (M @ aa) D = get_maximum_level aa D"
  using assms unfolding get_maximum_level_def by simp

lemma get_maximum_level_union_mset:
  "get_maximum_level M (A #\<union> B) = get_maximum_level M (A + B)"
  unfolding get_maximum_level_def by (auto simp: image_Un)

lemma count_decided_rev[simp]:
  "count_decided (rev M) = count_decided M"
  by (auto simp: rev_filter[symmetric])

lemma count_decided_ge_get_level[simp]:
  "count_decided M \<ge> get_level M L"
  by (induct M rule: ann_lit_list_induct) (auto simp add: le_max_iff_disj)

lemma count_decided_ge_get_maximum_level:
  "count_decided M \<ge> get_maximum_level M D"
  using get_maximum_level_exists_lit_of_max_level unfolding Bex_def
  by (metis get_maximum_level_empty count_decided_ge_get_level le0)

fun get_all_mark_of_propagated where
"get_all_mark_of_propagated [] = []" |
"get_all_mark_of_propagated (Decided _ # L) = get_all_mark_of_propagated L" |
"get_all_mark_of_propagated (Propagated _ mark # L) = mark # get_all_mark_of_propagated L"

lemma get_all_mark_of_propagated_append[simp]:
  "get_all_mark_of_propagated (A @ B) = get_all_mark_of_propagated A @ get_all_mark_of_propagated B"
  by (induct A rule: ann_lit_list_induct) auto

subsubsection \<open>Properties about the levels\<close>
lemma atm_lit_of_set_lits_of_l:
  "(\<lambda>l. atm_of (lit_of l)) ` set xs = atm_of ` lits_of_l xs"
  unfolding lits_of_def by auto

lemma le_count_decided_decomp:
  assumes "no_dup M"
  shows"i < count_decided M \<longleftrightarrow> (\<exists>c K c'. M = c @ Decided K # c' \<and> get_level M K = Suc i)"
    (is "?A \<longleftrightarrow> ?B")
proof
  assume ?B
  then obtain c K c' where
    "M = c @ Decided K # c'" and "get_level M K = Suc i"
    by blast
  then show ?A using count_decided_ge_get_level[of K M] by auto
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
            apply (rule exI[of _ "K"])
            apply (rule exI[of _ "c'"])
            using lev_K n_d unfolding M by auto
        next
          case False
          show ?thesis
            apply (rule exI[of _ "[]"])
            apply (rule exI[of _ "L"])
            apply (rule exI[of _ "M"])
            using False i by auto
        qed
      next
        case (Propagated L mark' M) note i = this(2) and n_d = this(3) and IH = this(1)
        then obtain c K c' where
          M: "M = c @ Decided K # c'" and lev_K: "get_level M K = Suc i"
          by auto
        show ?case
          apply (rule exI[of _ "Propagated L mark' # c"])
          apply (rule exI[of _ "K"])
          apply (rule exI[of _ "c'"])
          using lev_K n_d unfolding M by (auto simp: atm_lit_of_set_lits_of_l)
      qed
qed

end
