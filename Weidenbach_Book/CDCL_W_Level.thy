theory CDCL_W_Level
imports Partial_Annotated_Clausal_Logic
begin

subsubsection \<open>Level of literals and clauses\<close>
text \<open>Getting the level of a variable, implies that the list has to be reversed. Here is the 
  function after reversing.\<close>

abbreviation count_decided :: "('b, 'a, 'c) ann_lit list \<Rightarrow> nat" where
"count_decided l \<equiv> length (filter is_decided l)"

abbreviation get_level :: "('v, 'b, 'a) ann_lits \<Rightarrow> 'v literal \<Rightarrow> nat" where
"get_level S L \<equiv> length (filter is_decided (dropWhile (\<lambda>S. atm_of (lit_of S) \<noteq> atm_of L) S))"

lemma get_level_uminus: "get_level M (-L) = get_level M L"
  by auto

lemma atm_of_notin_get_rev_level_eq_0[simp]:
  assumes "atm_of L \<notin> atm_of ` lits_of_l M"
  shows "get_level M L = 0"
  using assms by (induct M rule: ann_lit_list_induct) auto

lemma get_level_ge_0_atm_of_in:
  assumes  "get_level M L > n"
  shows "atm_of L \<in> atm_of ` lits_of_l M"
  using assms by (induct M arbitrary: n rule: ann_lit_list_induct) fastforce+

text \<open>In @{const get_level} (resp. @{const get_level}), the beginning (resp. the end) can be
  skipped if the literal is not in the beginning (resp. the end).\<close>
lemma get_rev_level_skip[simp]:
  assumes  "atm_of L \<notin> atm_of ` lits_of_l M"
  shows "get_level (M @ M') L = get_level M' L"
  using assms by (induct M rule: ann_lit_list_induct) auto

text \<open>If the literal is at the beginning, then the end can be skipped\<close>
lemma get_rev_level_skip_end[simp]:
  assumes  "atm_of L \<in> atm_of ` lits_of_l M"
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
  apply (auto simp:  image_iff lits_of_def filter_empty_conv dest: set_dropWhileD)
  done

lemma get_level_skip_in_all_not_decided:
  fixes M :: "('a, 'c, 'b) ann_lit list" and L :: "'a literal"
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

text \<open>the @{term "{#0#}"}  is there to ensures that the set is not empty.\<close>
definition get_maximum_level :: "('a, 'c, 'b) ann_lit list \<Rightarrow> 'a literal multiset \<Rightarrow> nat"
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

(* lemma get_maximum_level_skip_notin:
  assumes D: "\<forall>L\<in>#D. atm_of L \<notin> atm_of ` lits_of_l M"
  shows "get_maximum_level M D = get_maximum_level (Propagated x21 x22 # M) D"
proof -
  have A: "(get_level ([Propagated x21 x22] # M)) ` set_mset D
      = (get_level M) ` set_mset D"
    using D by (auto intro!: image_cong simp add:  lits_of_def)
  show ?thesis unfolding get_maximum_level_def by (auto simp: A)
qed

lemma get_maximum_level_skip_un_decided_not_present:
  assumes "\<forall>L\<in>#D. atm_of L \<notin> atm_of ` lits_of_l M" and
  "\<forall>m\<in>set M. \<not> is_decided m"
  shows "get_maximum_level aa D = get_maximum_level (M @ aa) D"
  using assms by (induction M rule: ann_lit_list_induct)
  (auto intro!:  simp add: image_Un) *)

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
"get_all_mark_of_propagated (Decided _ _ # L) = get_all_mark_of_propagated L" |
"get_all_mark_of_propagated (Propagated _ mark # L) = mark # get_all_mark_of_propagated L"

lemma get_all_mark_of_propagated_append[simp]:
  "get_all_mark_of_propagated (A @ B) = get_all_mark_of_propagated A @ get_all_mark_of_propagated B"
  by (induct A rule: ann_lit_list_induct) auto

subsubsection \<open>Properties about the levels\<close>
fun get_all_levels_of_ann :: "('b, 'a, 'c) ann_lit list \<Rightarrow> 'a list"  where
"get_all_levels_of_ann [] = []" |
"get_all_levels_of_ann (Decided l level # Ls) = level # get_all_levels_of_ann Ls" |
"get_all_levels_of_ann (Propagated _ _ # Ls) = get_all_levels_of_ann Ls"

lemma get_all_levels_of_ann_nil_iff_not_is_decided:
  "get_all_levels_of_ann xs = [] \<longleftrightarrow> (\<forall> x \<in> set xs. \<not>is_decided x)"
  using assms by (induction xs rule: ann_lit_list_induct) auto

lemma get_all_levels_of_ann_cons:
  "get_all_levels_of_ann (a # b) =
    (if is_decided a then [level_of a] else []) @ get_all_levels_of_ann b"
  by (cases a) simp_all

lemma get_all_levels_of_ann_append[simp]:
  "get_all_levels_of_ann (a @ b) = get_all_levels_of_ann a @ get_all_levels_of_ann b"
  by (induct a) (simp_all add: get_all_levels_of_ann_cons)

lemma atm_lit_of_set_list_of_l:  
  "(\<lambda>l. atm_of (lit_of l)) ` set xs = atm_of ` lits_of_l xs"
  unfolding lits_of_def by auto
  
lemma le_count_decided_decomp:
  assumes "no_dup M"
  shows"i < count_decided M \<longleftrightarrow> (\<exists>c K c' mark. M = c @ Decided K mark # c' \<and> get_level M K = Suc i)" 
    (is "?A \<longleftrightarrow> ?B") 
proof 
  assume ?B
  then obtain c K c' mark where
    "M = c @ Decided K mark # c'" and "get_level M K = Suc i" 
    by blast
  then show ?A using count_decided_ge_get_level[of K M] by auto
next
  assume ?A
  then show ?B
    using \<open>no_dup M\<close>
    proof (induction M rule: ann_lit_list_induct)
      case nil
      then show ?case by simp
    next
      case (decided L mark' M) note IH = this(1) and i = this(2) and n_d = this(3)
      then have n_d_M: "no_dup M" by simp
      show ?case
        proof (cases "i < count_decided M")
          case True
          then obtain c K c' mark where
            M: "M = c @ Decided K mark # c'" and lev_K: "get_level M K = Suc i"
            using IH n_d_M by blast
          show ?thesis
            apply (rule exI[of _ "Decided L mark' # c"])
            apply (rule exI[of _ "K"])
            apply (rule exI[of _ "c'"])
            using lev_K n_d unfolding M by auto
        next
          case False
          show ?thesis
            apply (rule exI[of _ "[]"])
            apply (rule exI[of _ "L"])
            apply (rule exI[of _ "M"])
            apply (rule exI[of _ "mark'"])
            using False i by auto
        qed
      next
        case (proped L mark' M) note i = this(2) and n_d = this(3) and IH = this(1)
        then obtain c K c' mark where
          M: "M = c @ Decided K mark # c'" and lev_K: "get_level M K = Suc i"
          by auto
        show ?case
          apply (rule exI[of _ "Propagated L mark' # c"])
          apply (rule exI[of _ "K"])
          apply (rule exI[of _ "c'"])
          using lev_K n_d unfolding M by (auto simp: atm_lit_of_set_list_of_l)
      qed
qed

(* lemma get_rev_level_less_max_get_all_levels_of_ann:
  "get_rev_level M n L \<le> Max (set (n # get_all_levels_of_ann M))"
  by (induct M arbitrary: n rule: get_all_levels_of_ann.induct)
     (simp_all add: max.coboundedI2)

lemma get_rev_level_ge_min_get_all_levels_of_ann:
  assumes "atm_of L \<in> atm_of ` lits_of_l M"
  shows "get_rev_level M n L \<ge> Min (set (n # get_all_levels_of_ann M))"
  using assms by (induct M arbitrary: n rule: get_all_levels_of_ann.induct)
    (auto simp add: min_le_iff_disj) *)

lemma get_all_levels_of_ann_rev_eq_rev_get_all_levels_of_ann[simp]:
  "get_all_levels_of_ann (rev M) = rev (get_all_levels_of_ann M)"
  by (induct M rule: get_all_levels_of_ann.induct)
     (simp_all add: max.coboundedI2)

(* lemma count_decided_max_get_all_levels_of_ann:
  "count_decided M = Max (insert 0 (set (get_all_levels_of_ann M)))"
  by (induct M rule: ann_lit_list_induct) (auto simp: insert_commute) *)

(* lemma get_rev_level_in_levels_of_decided:
  "get_rev_level M n L \<in> {0, n} \<union> set (get_all_levels_of_ann M)"
  by (induction M arbitrary: n rule: ann_lit_list_induct) (force simp add: atm_of_eq_atm_of)+ *)

(* lemma get_rev_level_in_atms_in_levels_of_decided:
  "atm_of L \<in> atm_of ` (lits_of_l M) \<Longrightarrow> 
    get_rev_level M n L \<in> {n} \<union> set (get_all_levels_of_ann M)"
  by (induction M arbitrary: n rule: ann_lit_list_induct) (auto simp add: atm_of_eq_atm_of)
 *)
lemma get_all_levels_of_ann_no_decided:
  "(\<forall>l\<in>set Ls. \<not> is_decided l) \<longleftrightarrow> get_all_levels_of_ann Ls = []"
  by (induction Ls) (auto simp add: get_all_levels_of_ann_cons)

(* lemma get_level_in_levels_of_decided:
  "get_level M L \<in> {0} \<union> set (get_all_levels_of_ann M)"
  using get_rev_level_in_levels_of_decided[of "rev M" 0 L] by auto *)

(* text \<open>The zero is here to avoid empty-list issues with @{term last}:\<close>
lemma get_level_get_rev_level_get_all_levels_of_ann:
  assumes "atm_of L \<notin> atm_of ` (lits_of_l M)"
  shows 
    "get_level (K @ M) L = get_level K (last (0 # get_all_levels_of_ann (rev M))) L"
  using assms
proof (induct M arbitrary: K)
  case Nil
  then show ?case by auto
next
  case (Cons a M)
  then have H: "\<And>K. get_level (K @ M) L
    = get_rev_level (rev K) (last (0 # get_all_levels_of_ann (rev M))) L"
    by auto
  have "get_level ((K @ [a])@ M) L
    = get_rev_level (a # rev K) (last (0 # get_all_levels_of_ann (rev M))) L"
    using H[of "K @ [a]"] by simp
  then show ?case using Cons(2) by (cases a) auto
qed
 *)
(* lemma get_rev_level_can_skip_correctly_ordered:
  assumes
    "no_dup M" and
    "atm_of L \<notin> atm_of ` (lits_of_l M)" and
    "get_all_levels_of_ann M = rev [Suc 0..<Suc (length (get_all_levels_of_ann M))]"
  shows "get_level (rev M @ K) L = length (get_all_levels_of_ann M) + get_level K L"
  using assms
proof (induct M arbitrary: K rule: ann_lit_list_induct)
  case nil
  then show ?case by simp
next
  case (decided L' i M K)
  then have
    i: "i = Suc (length (get_all_levels_of_ann M))" and
    "get_all_levels_of_ann M = rev [Suc 0..<Suc (length (get_all_levels_of_ann M))]"
    by auto(* 
  then have "get_rev_level (rev M @ (Decided L' i # K)) 0 L
    = get_rev_level (Decided L' i # K) (length (get_all_levels_of_ann M)) L"
    using decided by auto *)
  then show ?case using decided unfolding i by auto
next
  case (proped L' D M K)
  then have "get_all_levels_of_ann M = rev [Suc 0..<Suc (length (get_all_levels_of_ann M))]"
    by auto
  then show ?case using proped by auto
qed *)

(* lemma get_level_skip_beginning_hd_get_all_levels_of_ann:
  assumes "atm_of L \<notin> atm_of ` lits_of_l S" and "get_all_levels_of_ann S \<noteq> []"
  shows "get_level (M@ S) L = get_level (rev M) (hd (get_all_levels_of_ann S)) L"
  using assms
proof (induction S arbitrary: M rule: ann_lit_list_induct)
  case nil
  then show ?case by (auto simp add: lits_of_def)
next
  case (decided K m) note notin = this(2)
  then show ?case by (auto simp add: lits_of_def)
next
  case (proped L l) note IH = this(1) and L = this(2) and neq = this(3)
  show ?case using IH[of "M@[Propagated L l]"] L neq by (auto simp add: atm_of_eq_atm_of)
qed
 *)
end
