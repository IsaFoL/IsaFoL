theory CDCL_W_Level
imports Partial_Annotated_Clausal_Logic
begin

subsubsection \<open>Level of literals and clauses\<close>
text \<open>Getting the level of a variable, implies that the list has to be reversed. Here is the funtion
  after reversing.\<close>
fun get_rev_level :: "('v, nat, 'a) marked_lits \<Rightarrow> nat \<Rightarrow> 'v literal \<Rightarrow> nat" where
"get_rev_level [] _ _ = 0" |
"get_rev_level (Marked l level # Ls) n L =
  (if atm_of l = atm_of L then level else get_rev_level Ls level L)" |
"get_rev_level (Propagated l _ # Ls) n L =
  (if atm_of l = atm_of L then n else get_rev_level Ls n L)"

abbreviation "get_level M L \<equiv> get_rev_level (rev M) 0 L"

lemma get_rev_level_uminus[simp]: "get_rev_level M n(-L) = get_rev_level M n L"
  by (induct arbitrary: n rule: get_rev_level.induct) auto

(* TODO as this, unusable w.r.t. no_dup *)
lemma atm_of_notin_get_rev_level_eq_0[simp]:
  assumes "atm_of L \<notin> atm_of ` lits_of_l M"
  shows "get_rev_level M n L = 0"
  using assms by (induct M arbitrary: n rule: marked_lit_list_induct) auto

lemma get_rev_level_ge_0_atm_of_in:
  assumes  "get_rev_level M n L > n"
  shows "atm_of L \<in> atm_of ` lits_of_l M"
  using assms by (induct M arbitrary: n rule: marked_lit_list_induct) fastforce+

text \<open>In @{const get_rev_level} (resp. @{const get_level}), the beginning (resp. the end) can be
  skipped if the literal is not in the beginning (resp. the end).\<close>
lemma get_rev_level_skip[simp]:
  assumes  "atm_of L \<notin> atm_of ` lits_of_l M"
  shows "get_rev_level (M @ Marked K i # M') n L = get_rev_level (Marked K i # M') i L"
  using assms by (induct M arbitrary: n i rule: marked_lit_list_induct) auto

lemma get_rev_level_notin_end[simp]:
  assumes  "atm_of L \<notin> atm_of ` lits_of_l M'"
  shows "get_rev_level (M @ M') n L = get_rev_level M n L"
  using assms by (induct M arbitrary: n rule: marked_lit_list_induct) auto

text \<open>If the literal is at the beginning, then the end can be skipped\<close>
lemma get_rev_level_skip_end[simp]:
  assumes  "atm_of L \<in> atm_of ` lits_of_l M"
  shows "get_rev_level (M @ M') n L = get_rev_level M n L"
  using assms by (induct arbitrary: n rule: marked_lit_list_induct) auto

lemma get_level_skip_beginning:
  assumes "atm_of L' \<noteq> atm_of (lit_of K)"
  shows "get_level (K # M) L' = get_level M L'"
  using assms by auto

lemma get_level_skip_beginning_not_marked_rev:
  assumes "atm_of L \<notin> atm_of ` lit_of `(set S)"
  and "\<forall>s\<in>set S. \<not>is_marked s"
  shows "get_level (M @ rev S) L = get_level M L"
  using assms by (induction S rule: marked_lit_list_induct) auto

lemma get_level_skip_beginning_not_marked[simp]:
  assumes "atm_of L \<notin> atm_of ` lit_of `(set S)"
  and "\<forall>s\<in>set S. \<not>is_marked s"
  shows "get_level (M @ S) L = get_level M L"
  using get_level_skip_beginning_not_marked_rev[of L "rev S" M] assms by auto

lemma get_rev_level_skip_beginning_not_marked[simp]:
  assumes "atm_of L \<notin> atm_of ` lit_of `(set S)"
  and "\<forall>s\<in>set S. \<not>is_marked s"
  shows "get_rev_level (rev S @ rev M) 0 L = get_level M L"
  using get_level_skip_beginning_not_marked_rev[of L "rev S" M] assms by auto

lemma get_level_skip_in_all_not_marked:
  fixes M :: "('a, nat, 'b) marked_lit list" and L :: "'a literal"
  assumes "\<forall>m\<in>set M. \<not> is_marked m"
  and "atm_of L \<in> atm_of ` lit_of ` (set M)"
  shows "get_rev_level M n L = n"
  using assms by (induction M rule: marked_lit_list_induct) auto

lemma get_level_skip_all_not_marked[simp]:
  fixes M
  defines "M' \<equiv> rev M"
  assumes "\<forall>m\<in>set M. \<not> is_marked m"
  shows "get_level M L = 0"
proof -
  have M: "M = rev M'"
    unfolding M'_def by auto
  show ?thesis
    using assms unfolding M by (induction M' rule: marked_lit_list_induct) auto
qed

abbreviation "MMax M \<equiv> Max (set_mset M)"

text \<open>the @{term "{#0#}"}  is there to ensures that the set is not empty.\<close>
definition get_maximum_level :: "('a, nat, 'b) marked_lit list \<Rightarrow> 'a literal multiset \<Rightarrow> nat"
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
  by (smt atm_of_in_atm_of_set_in_uminus get_level_skip_beginning image_iff marked_lit.sel(2)
    multiset.map_cong0)

lemma get_maximum_level_skip_beginning:
  assumes DH: "atms_of D \<subseteq> atm_of `lits_of_l H"
  shows "get_maximum_level (c @ Marked Kh i # H) D = get_maximum_level H D"
proof -
  have "(get_rev_level (rev H @ Marked Kh i # rev c) 0) ` set_mset D
      = (get_rev_level (rev H) 0) ` set_mset D"
    using DH unfolding atms_of_def
    by (metis (no_types, lifting) get_rev_level_skip_end image_cong image_subset_iff set_rev)
  then show ?thesis using DH unfolding get_maximum_level_def by auto
qed

lemma get_maximum_level_D_single_propagated:
  "get_maximum_level [Propagated x21 x22] D = 0"
proof -
  have A: "insert 0 ((\<lambda>L. 0) ` (set_mset D \<inter> {L. atm_of x21 = atm_of L})
      \<union> (\<lambda>L. 0) ` (set_mset D \<inter> {L. atm_of x21 \<noteq> atm_of L})) = {0}"
    by auto
  show ?thesis unfolding get_maximum_level_def by (simp add: A)
qed

lemma get_maximum_level_skip_notin:
  assumes D: "\<forall>L\<in>#D. atm_of L \<in> atm_of `lits_of_l M"
  shows "get_maximum_level M D = get_maximum_level (Propagated x21 x22 # M) D"
proof -
  have A: "(get_rev_level (rev M @ [Propagated x21 x22]) 0) ` set_mset D
      = (get_rev_level (rev M) 0) ` set_mset D"
    using D by (auto intro!: image_cong simp add:  lits_of_def)
  show ?thesis unfolding get_maximum_level_def by (auto simp: A)
qed

lemma get_maximum_level_skip_un_marked_not_present:
  assumes "\<forall>L\<in>#D. atm_of L \<in> atm_of ` lits_of_l aa" and
  "\<forall>m\<in>set M. \<not> is_marked m"
  shows "get_maximum_level aa D = get_maximum_level (M @ aa) D"
  using assms by (induction M rule: marked_lit_list_induct)
  (auto intro!: get_maximum_level_skip_notin[of D "_ @ aa"] simp add: image_Un)

fun get_maximum_possible_level:: "('b, nat, 'c) marked_lit list \<Rightarrow> nat"   where
"get_maximum_possible_level [] = 0" |
"get_maximum_possible_level (Marked K i # l) = max i (get_maximum_possible_level l)" |
"get_maximum_possible_level (Propagated _ _ # l) = get_maximum_possible_level l"

lemma get_maximum_possible_level_append[simp]:
  "get_maximum_possible_level (M@M')
    = max (get_maximum_possible_level M) (get_maximum_possible_level M')"
  by (induct M rule: marked_lit_list_induct) auto

lemma get_maximum_possible_level_rev[simp]:
  "get_maximum_possible_level (rev M) = get_maximum_possible_level M"
  by (induct M rule: marked_lit_list_induct) auto

lemma get_maximum_possible_level_ge_get_rev_level:
  "max (get_maximum_possible_level M) i \<ge> get_rev_level M i L"
  by (induct M arbitrary: i rule: marked_lit_list_induct) (auto simp add: le_max_iff_disj)

lemma get_maximum_possible_level_ge_get_level[simp]:
  "get_maximum_possible_level M \<ge> get_level M L"
  using get_maximum_possible_level_ge_get_rev_level[of "rev _" 0] by auto

lemma get_maximum_possible_level_ge_get_maximum_level[simp]:
  "get_maximum_possible_level M \<ge> get_maximum_level M D"
  using get_maximum_level_exists_lit_of_max_level unfolding Bex_def
  by (metis get_maximum_level_empty get_maximum_possible_level_ge_get_level le0)

fun get_all_mark_of_propagated where
"get_all_mark_of_propagated [] = []" |
"get_all_mark_of_propagated (Marked _ _ # L) = get_all_mark_of_propagated L" |
"get_all_mark_of_propagated (Propagated _ mark # L) = mark # get_all_mark_of_propagated L"

lemma get_all_mark_of_propagated_append[simp]:
  "get_all_mark_of_propagated (A @ B) = get_all_mark_of_propagated A @ get_all_mark_of_propagated B"
  by (induct A rule: marked_lit_list_induct) auto

subsubsection \<open>Properties about the levels\<close>
fun get_all_levels_of_marked :: "('b, 'a, 'c) marked_lit list \<Rightarrow> 'a list"  where
"get_all_levels_of_marked [] = []" |
"get_all_levels_of_marked (Marked l level # Ls) = level # get_all_levels_of_marked Ls" |
"get_all_levels_of_marked (Propagated _ _ # Ls) = get_all_levels_of_marked Ls"

lemma get_all_levels_of_marked_nil_iff_not_is_marked:
  "get_all_levels_of_marked xs = [] \<longleftrightarrow> (\<forall> x \<in> set xs. \<not>is_marked x)"
  using assms by (induction xs rule: marked_lit_list_induct) auto

lemma get_all_levels_of_marked_cons:
  "get_all_levels_of_marked (a # b) =
    (if is_marked a then [level_of a] else []) @ get_all_levels_of_marked b"
  by (cases a) simp_all

lemma get_all_levels_of_marked_append[simp]:
  "get_all_levels_of_marked (a @ b) = get_all_levels_of_marked a @ get_all_levels_of_marked b"
  by (induct a) (simp_all add: get_all_levels_of_marked_cons)

lemma in_get_all_levels_of_marked_iff_decomp:
  "i \<in> set (get_all_levels_of_marked M) \<longleftrightarrow> (\<exists>c K c'. M = c @ Marked K i # c')" (is "?A \<longleftrightarrow> ?B")
proof
  assume ?B
  then show ?A by auto
next
  assume ?A
  then show ?B
    apply (induction M rule: marked_lit_list_induct)
      apply auto[]
     apply (metis append_Cons append_Nil get_all_levels_of_marked.simps(2) set_ConsD)
    by (metis append_Cons get_all_levels_of_marked.simps(3))
qed

lemma get_rev_level_less_max_get_all_levels_of_marked:
  "get_rev_level M n L \<le> Max (set (n # get_all_levels_of_marked M))"
  by (induct M arbitrary: n rule: get_all_levels_of_marked.induct)
     (simp_all add: max.coboundedI2)

lemma get_rev_level_ge_min_get_all_levels_of_marked:
  assumes "atm_of L \<in> atm_of ` lits_of_l M"
  shows "get_rev_level M n L \<ge> Min (set (n # get_all_levels_of_marked M))"
  using assms by (induct M arbitrary: n rule: get_all_levels_of_marked.induct)
    (auto simp add: min_le_iff_disj)

lemma get_all_levels_of_marked_rev_eq_rev_get_all_levels_of_marked[simp]:
  "get_all_levels_of_marked (rev M) = rev (get_all_levels_of_marked M)"
  by (induct M rule: get_all_levels_of_marked.induct)
     (simp_all add: max.coboundedI2)

lemma get_maximum_possible_level_max_get_all_levels_of_marked:
  "get_maximum_possible_level M = Max (insert 0 (set (get_all_levels_of_marked M)))"
  by (induct M rule: marked_lit_list_induct) (auto simp: insert_commute)

lemma get_rev_level_in_levels_of_marked:
  "get_rev_level M n L \<in> {0, n} \<union> set (get_all_levels_of_marked M)"
  by (induction M arbitrary: n rule: marked_lit_list_induct) (force simp add: atm_of_eq_atm_of)+

lemma get_rev_level_in_atms_in_levels_of_marked:
  "atm_of L \<in> atm_of ` (lits_of_l M) \<Longrightarrow> 
    get_rev_level M n L \<in> {n} \<union> set (get_all_levels_of_marked M)"
  by (induction M arbitrary: n rule: marked_lit_list_induct) (auto simp add: atm_of_eq_atm_of)

lemma get_all_levels_of_marked_no_marked:
  "(\<forall>l\<in>set Ls. \<not> is_marked l) \<longleftrightarrow> get_all_levels_of_marked Ls = []"
  by (induction Ls) (auto simp add: get_all_levels_of_marked_cons)

lemma get_level_in_levels_of_marked:
  "get_level M L \<in> {0} \<union> set (get_all_levels_of_marked M)"
  using get_rev_level_in_levels_of_marked[of "rev M" 0 L] by auto

text \<open>The zero is here to avoid empty-list issues with @{term last}:\<close>
lemma get_level_get_rev_level_get_all_levels_of_marked:
  assumes "atm_of L \<notin> atm_of ` (lits_of_l M)"
  shows 
    "get_level (K @ M) L = get_rev_level (rev K) (last (0 # get_all_levels_of_marked (rev M))) L"
  using assms
proof (induct M arbitrary: K)
  case Nil
  then show ?case by auto
next
  case (Cons a M)
  then have H: "\<And>K. get_level (K @ M) L
    = get_rev_level (rev K) (last (0 # get_all_levels_of_marked (rev M))) L"
    by auto
  have "get_level ((K @ [a])@ M) L
    = get_rev_level (a # rev K) (last (0 # get_all_levels_of_marked (rev M))) L"
    using H[of "K @ [a]"] by simp
  then show ?case using Cons(2) by (cases a) auto
qed

lemma get_rev_level_can_skip_correctly_ordered:
  assumes
    "no_dup M" and
    "atm_of L \<notin> atm_of ` (lits_of_l M)" and
    "get_all_levels_of_marked M = rev [Suc 0..<Suc (length (get_all_levels_of_marked M))]"
  shows "get_rev_level (rev M @ K) 0 L = get_rev_level K (length (get_all_levels_of_marked M)) L"
  using assms
proof (induct M arbitrary: K rule: marked_lit_list_induct)
  case nil
  then show ?case by simp
next
  case (marked L' i M K)
  then have
    i: "i = Suc (length (get_all_levels_of_marked M))" and
    "get_all_levels_of_marked M = rev [Suc 0..<Suc (length (get_all_levels_of_marked M))]"
    by auto
  then have "get_rev_level (rev M @ (Marked L' i # K)) 0 L
    = get_rev_level (Marked L' i # K) (length (get_all_levels_of_marked M)) L"
    using marked by auto
  then show ?case using marked unfolding i by auto
next
  case (proped L' D M K)
  then have "get_all_levels_of_marked M = rev [Suc 0..<Suc (length (get_all_levels_of_marked M))]"
    by auto
  then have "get_rev_level (rev M @ (Propagated L' D # K)) 0 L
    = get_rev_level (Propagated L' D # K) (length (get_all_levels_of_marked M)) L"
    using proped by auto
  then show ?case using proped by auto
qed

lemma get_level_skip_beginning_hd_get_all_levels_of_marked:
  assumes "atm_of L \<notin> atm_of ` lits_of_l S" and "get_all_levels_of_marked S \<noteq> []"
  shows "get_level (M@ S) L = get_rev_level (rev M) (hd (get_all_levels_of_marked S)) L"
  using assms
proof (induction S arbitrary: M rule: marked_lit_list_induct)
  case nil
  then show ?case by (auto simp add: lits_of_def)
next
  case (marked K m) note notin = this(2)
  then show ?case by (auto simp add: lits_of_def)
next
  case (proped L l) note IH = this(1) and L = this(2) and neq = this(3)
  show ?case using IH[of "M@[Propagated L l]"] L neq by (auto simp add: atm_of_eq_atm_of)
qed

end
