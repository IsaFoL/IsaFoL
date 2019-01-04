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
        case (Propagated L mark' M) note i = this(2) and n_d = this(3) and IH = this(1)
        then obtain c K c' where
          M: "M = c @ Decided K # c'" and lev_K: "get_level M K = Suc i"
          by (auto simp: count_decided_def)
        show ?case
          apply (rule exI[of _ "Propagated L mark' # c"])
          apply (rule exI[of _ "K"])
          apply (rule exI[of _ "c'"])
          using lev_K n_d unfolding M by (auto simp: atm_lit_of_set_lits_of_l get_level_def defined_lit_map)
      qed
qed


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

end
