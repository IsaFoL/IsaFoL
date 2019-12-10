theory DPLL_CDCL_W_Implementation
imports
  Entailment_Definition.Partial_Annotated_Herbrand_Interpretation
  CDCL_W_Level
begin
chapter \<open>List-based Implementation of DPLL and CDCL\<close>

text \<open>We can now reuse all the theorems to go towards an implementation using 2-watched literals:
  \<^item> @{file CDCL_W_Abstract_State.thy} defines a better-suited state: the operation operating on it
  are more constrained, allowing simpler proofs and less edge cases later.\<close>

section \<open>Simple List-Based Implementation of the DPLL and CDCL\<close>

text \<open>The idea of the list-based implementation is to test the stack: the theories about the
  calculi, adapting the theorems to a simple implementation and the code exportation. The
  implementation are very simple ans simply iterate over-and-over on lists.\<close>

subsection \<open>Common Rules\<close>

subsubsection \<open>Propagation\<close>

text \<open>The following theorem holds:\<close>

lemma lits_of_l_unfold:
  "(\<forall>c \<in> set C. -c \<in> lits_of_l Ms) \<longleftrightarrow> Ms \<Turnstile>as CNot (mset C)"
  unfolding true_annots_def Ball_def true_annot_def CNot_def by auto
text \<open>The right-hand version is written at a high-level, but only the left-hand side is executable.\<close>

definition is_unit_clause :: "'a literal list \<Rightarrow> ('a, 'b) ann_lits \<Rightarrow> 'a literal option"
 where
 "is_unit_clause l M =
   (case List.filter (\<lambda>a. atm_of a \<notin> atm_of ` lits_of_l M) l of
     a # [] \<Rightarrow> if M \<Turnstile>as CNot (mset l - {#a#}) then Some a else None
   | _ \<Rightarrow> None)"

definition is_unit_clause_code :: "'a literal list \<Rightarrow> ('a, 'b) ann_lits
  \<Rightarrow> 'a literal option" where
 "is_unit_clause_code l M =
   (case List.filter (\<lambda>a. atm_of a \<notin> atm_of ` lits_of_l M) l of
     a # [] \<Rightarrow> if (\<forall>c \<in>set (remove1 a l). -c \<in> lits_of_l M) then Some a else None
   | _ \<Rightarrow> None)"

lemma is_unit_clause_is_unit_clause_code[code]:
  "is_unit_clause l M = is_unit_clause_code l M"
proof -
  have 1: "\<And>a. (\<forall>c\<in>set (remove1 a l). - c \<in> lits_of_l M) \<longleftrightarrow> M \<Turnstile>as CNot (mset l - {#a#})"
    using lits_of_l_unfold[of "remove1 _ l", of _ M] by simp
  then show ?thesis
    unfolding is_unit_clause_code_def is_unit_clause_def 1 by blast
qed

lemma is_unit_clause_some_undef:
  assumes "is_unit_clause l M = Some a"
  shows "undefined_lit M a"
proof -
  have "(case [a\<leftarrow>l . atm_of a \<notin> atm_of ` lits_of_l M] of [] \<Rightarrow> None
          | [a] \<Rightarrow> if M \<Turnstile>as CNot (mset l - {#a#}) then Some a else None
          | a # ab # xa \<Rightarrow> Map.empty xa) = Some a"
    using assms unfolding is_unit_clause_def .
  then have "a \<in> set [a\<leftarrow>l . atm_of a \<notin> atm_of ` lits_of_l M]"
    apply (cases "[a\<leftarrow>l . atm_of a \<notin> atm_of ` lits_of_l M]")
      apply simp
    apply (rename_tac aa list; case_tac list) by (auto split: if_split_asm)
  then have "atm_of a \<notin> atm_of ` lits_of_l M" by auto
  then show ?thesis
    by (simp add: Decided_Propagated_in_iff_in_lits_of_l
      atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set )
qed

lemma is_unit_clause_some_CNot: "is_unit_clause l M = Some a \<Longrightarrow> M \<Turnstile>as CNot (mset l - {#a#})"
  unfolding is_unit_clause_def
proof -
  assume "(case [a\<leftarrow>l . atm_of a \<notin> atm_of ` lits_of_l M] of [] \<Rightarrow> None
          | [a] \<Rightarrow> if M \<Turnstile>as CNot (mset l - {#a#}) then Some a else None
          | a # ab # xa \<Rightarrow> Map.empty xa) = Some a"
  then show ?thesis
    apply (cases "[a\<leftarrow>l . atm_of a \<notin> atm_of ` lits_of_l M]", simp)
      apply simp
    apply (rename_tac aa list, case_tac list) by (auto split: if_split_asm)
qed

lemma is_unit_clause_some_in: "is_unit_clause l M = Some a \<Longrightarrow> a \<in> set l"
  unfolding is_unit_clause_def
proof -
  assume "(case [a\<leftarrow>l . atm_of a \<notin> atm_of ` lits_of_l M] of [] \<Rightarrow> None
         | [a] \<Rightarrow> if M \<Turnstile>as CNot (mset l - {#a#}) then Some a else None
         | a # ab # xa \<Rightarrow> Map.empty xa) = Some a"
  then show "a \<in> set l"
    by (cases "[a\<leftarrow>l . atm_of a \<notin> atm_of ` lits_of_l M]")
       (fastforce dest: filter_eq_ConsD split: if_split_asm split: list.splits)+
qed

lemma is_unit_clause_Nil[simp]: "is_unit_clause [] M = None"
  unfolding is_unit_clause_def by auto


subsubsection \<open>Unit propagation for all clauses\<close>

text \<open>Finding the first clause to propagate\<close>
fun find_first_unit_clause :: "'a literal list list \<Rightarrow> ('a, 'b) ann_lits
  \<Rightarrow> ('a literal \<times> 'a literal list) option" where
"find_first_unit_clause (a # l) M =
  (case is_unit_clause a M of
    None \<Rightarrow> find_first_unit_clause l M
  | Some L \<Rightarrow> Some (L, a))" |
"find_first_unit_clause [] _ = None"

lemma find_first_unit_clause_some:
  "find_first_unit_clause l M = Some (a, c)
  \<Longrightarrow> c \<in> set l \<and>  M \<Turnstile>as CNot (mset c - {#a#}) \<and> undefined_lit M a \<and> a \<in> set c"
  apply (induction l)
    apply simp
  by (auto split: option.splits dest: is_unit_clause_some_in is_unit_clause_some_CNot
         is_unit_clause_some_undef)

lemma propagate_is_unit_clause_not_None:
  assumes
  M: "M \<Turnstile>as CNot (mset c - {#a#})" and
  undef: "undefined_lit M a" and
  ac: "a \<in> set c"
  shows "is_unit_clause c M \<noteq> None"
proof -
  have "[a\<leftarrow>c . atm_of a \<notin> atm_of ` lits_of_l M] = [a]"
    using assms
    proof (induction c)
      case Nil then show ?case by simp
    next
      case (Cons ac c)
      show ?case
        proof (cases "a = ac")
          case True
          then show ?thesis using Cons
            by (auto simp del: lits_of_l_unfold
                 simp add: lits_of_l_unfold[symmetric] Decided_Propagated_in_iff_in_lits_of_l
                   atm_of_eq_atm_of atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set)
        next
          case False
          then have T: "mset c + {#ac#} - {#a#} = mset c - {#a#} + {#ac#}"
            by (auto simp add: multiset_eq_iff)
          show ?thesis using False Cons
            by (auto simp add: T atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set)
        qed
    qed
  then show ?thesis
    using M unfolding is_unit_clause_def by auto
qed

lemma find_first_unit_clause_none:
  "c \<in> set l \<Longrightarrow>  M \<Turnstile>as CNot (mset c - {#a#}) \<Longrightarrow> undefined_lit M a \<Longrightarrow> a \<in> set c
  \<Longrightarrow> find_first_unit_clause l M \<noteq> None"
  by (induction l)
     (auto split: option.split simp add: propagate_is_unit_clause_not_None)

subsubsection \<open>Decide\<close>
fun find_first_unused_var :: "'a literal list list \<Rightarrow> 'a literal set \<Rightarrow> 'a literal option" where
"find_first_unused_var (a # l) M =
  (case List.find (\<lambda>lit. lit \<notin> M \<and> -lit \<notin> M) a of
    None \<Rightarrow> find_first_unused_var l M
  | Some a \<Rightarrow> Some a)" |
"find_first_unused_var [] _ = None"

lemma find_none[iff]:
  "List.find (\<lambda>lit. lit \<notin> M \<and> -lit \<notin> M) a = None \<longleftrightarrow>  atm_of ` set a \<subseteq> atm_of `  M"
  apply (induct a)
  using atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set
    by (force simp add:  atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set)+

lemma find_some: "List.find (\<lambda>lit. lit \<notin> M \<and> -lit \<notin> M) a = Some b \<Longrightarrow> b \<in> set a \<and> b \<notin> M \<and> -b \<notin> M"
  unfolding find_Some_iff by (metis nth_mem)

lemma find_first_unused_var_None[iff]:
  "find_first_unused_var l M = None \<longleftrightarrow> (\<forall>a \<in> set l. atm_of ` set a \<subseteq> atm_of `  M)"
  by (induct l)
     (auto split: option.splits dest!: find_some
       simp add: image_subset_iff atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set)

lemma find_first_unused_var_Some_not_all_incl:
  assumes "find_first_unused_var l M = Some c"
  shows " \<not>(\<forall>a \<in> set l. atm_of ` set a \<subseteq> atm_of `  M)"
proof -
  have "find_first_unused_var l M \<noteq> None"
    using assms by (cases "find_first_unused_var l M") auto
  then show "\<not>(\<forall>a \<in> set l. atm_of ` set a \<subseteq> atm_of `  M)" by auto
qed

lemma find_first_unused_var_Some:
  "find_first_unused_var l M = Some a \<Longrightarrow> (\<exists>m \<in> set l. a \<in> set m \<and> a \<notin> M \<and> -a \<notin> M)"
  by (induct l) (auto split: option.splits dest: find_some)

lemma find_first_unused_var_undefined:
  "find_first_unused_var l (lits_of_l Ms) = Some a \<Longrightarrow> undefined_lit Ms a"
  using find_first_unused_var_Some[of l "lits_of_l Ms" a] Decided_Propagated_in_iff_in_lits_of_l
  by blast


subsection \<open>CDCL specific functions\<close>

subsubsection \<open>Level\<close>

fun maximum_level_code:: "'a literal list \<Rightarrow> ('a, 'b) ann_lits \<Rightarrow> nat"
  where
"maximum_level_code [] _ = 0" |
"maximum_level_code (L # Ls) M = max (get_level M L) (maximum_level_code Ls M)"

lemma maximum_level_code_eq_get_maximum_level[simp]:
  "maximum_level_code D M = get_maximum_level M (mset D)"
  by (induction D) (auto simp add: get_maximum_level_add_mset)

lemma [code]:
  fixes M :: "('a, 'b) ann_lits"
  shows "get_maximum_level M (mset D) = maximum_level_code D M"
  by simp

subsubsection \<open>Backjumping\<close>
fun find_level_decomp where
"find_level_decomp M [] D k = None" |
"find_level_decomp M (L # Ls) D k =
  (case (get_level M L, maximum_level_code (D @ Ls) M) of
    (i, j) \<Rightarrow> if i = k \<and> j < i then Some (L, j) else find_level_decomp M Ls (L#D) k
  )"

lemma find_level_decomp_some:
  assumes "find_level_decomp M Ls D k = Some (L, j)"
  shows "L \<in> set Ls \<and> get_maximum_level M (mset (remove1 L (Ls @ D))) = j \<and> get_level M L = k"
  using assms
proof (induction Ls arbitrary: D)
  case Nil
  then show ?case by simp
next
  case (Cons L' Ls) note IH = this(1) and H = this(2)
  (* heavily modified sledgehammer proof *)
  define find where "find \<equiv> (if get_level M L' \<noteq> k \<or> \<not> get_maximum_level M (mset D + mset Ls) < get_level M L'
    then find_level_decomp M Ls (L' # D) k
    else Some (L', get_maximum_level M (mset D + mset Ls)))"
  have a1: "\<And>D. find_level_decomp M Ls D k = Some (L, j) \<Longrightarrow>
     L \<in> set Ls \<and> get_maximum_level M (mset Ls + mset D - {#L#}) = j \<and> get_level M L = k"
    using IH by simp
  have a2: "find = Some (L, j)"
    using H unfolding find_def by (auto split: if_split_asm)
  { assume "Some (L', get_maximum_level M (mset D + mset Ls)) \<noteq> find"
    then have f3: "L \<in> set Ls" and "get_maximum_level M (mset Ls + mset (L' # D) - {#L#}) = j"
      using a1 IH a2 unfolding find_def by meson+
    moreover then have "mset Ls + mset D - {#L#} + {#L'#} = {#L'#} + mset D + (mset Ls - {#L#})"
      by (auto simp: ac_simps multiset_eq_iff Suc_leI)
    ultimately have f4: "get_maximum_level M (mset Ls + mset D - {#L#} + {#L'#}) = j"
      by auto
  } note f4 = this
  have "{#L'#} + (mset Ls + mset D) = mset Ls + (mset D + {#L'#})"
      by (auto simp: ac_simps)
  then have
    "L = L' \<longrightarrow> get_maximum_level M (mset Ls + mset D) = j \<and> get_level M L' = k" and
    "L \<noteq> L' \<longrightarrow> L \<in> set Ls \<and> get_maximum_level M (mset Ls + mset D - {#L#} + {#L'#}) = j \<and>
      get_level M L = k"
     using a2 a1[of "L' # D"] unfolding find_def
     apply (metis add.commute add_diff_cancel_left' add_mset_add_single mset.simps(2)
         option.inject prod.inject)
    using f4 a2 a1[of "L' # D"] unfolding find_def by (metis option.inject prod.inject)
  then show ?case by simp
qed

lemma find_level_decomp_none:
  assumes "find_level_decomp M Ls E k = None" and "mset (L#D) = mset (Ls @ E)"
  shows "\<not>(L \<in> set Ls \<and> get_maximum_level M (mset D) < k \<and> k = get_level M L)"
  using assms
proof (induction Ls arbitrary: E L D)
  case Nil
  then show ?case by simp
next
  case (Cons L' Ls) note IH = this(1) and find_none = this(2) and LD = this(3)
  have "mset D + {#L'#} = mset E + (mset Ls + {#L'#})  \<Longrightarrow> mset D = mset E + mset Ls"
    by (metis add_right_imp_eq union_assoc)
  then show ?case
    using find_none IH[of "L' # E" L D] LD by (auto simp add: ac_simps split: if_split_asm)
qed

fun bt_cut where
"bt_cut i (Propagated _ _ # Ls) = bt_cut i Ls" |
"bt_cut i (Decided K # Ls) = (if count_decided Ls = i then Some (Decided K # Ls) else bt_cut i Ls)" |
"bt_cut i [] = None"

lemma bt_cut_some_decomp:
  assumes "no_dup M" and "bt_cut i M = Some M'"
  shows "\<exists>K M2 M1. M = M2 @ M' \<and> M' = Decided K # M1 \<and> get_level M K = (i+1)"
  using assms by (induction i M rule: bt_cut.induct) (auto simp: no_dup_def split: if_split_asm)

lemma bt_cut_not_none:
  assumes "no_dup M" and "M = M2 @ Decided K # M'" and "get_level M K = (i+1)"
  shows "bt_cut i M \<noteq> None"
  using assms by (induction M2 arbitrary: M rule: ann_lit_list_induct)
  (auto simp: no_dup_def atm_lit_of_set_lits_of_l)

lemma get_all_ann_decomposition_ex:
  "\<exists>N. (Decided K # M', N) \<in> set (get_all_ann_decomposition (M2@Decided K # M'))"
  apply (induction M2 rule: ann_lit_list_induct)
    apply auto[2]
  by (rename_tac L m xs,  case_tac "get_all_ann_decomposition (xs @ Decided K # M')")
  auto

lemma bt_cut_in_get_all_ann_decomposition:
  assumes "no_dup M" and "bt_cut i M = Some M'"
  shows "\<exists>M2. (M', M2) \<in> set (get_all_ann_decomposition M)"
  using bt_cut_some_decomp[OF assms] by (auto simp add: get_all_ann_decomposition_ex)

fun do_backtrack_step where
"do_backtrack_step (M, N, U, Some D) =
  (case find_level_decomp M D [] (count_decided M) of
    None \<Rightarrow> (M, N, U, Some D)
  | Some (L, j) \<Rightarrow>
    (case bt_cut j M of
      Some (Decided _ # Ls) \<Rightarrow> (Propagated L D # Ls, N, D # U, None)
    | _ \<Rightarrow> (M, N, U, Some D))
  )" |
"do_backtrack_step S = S"

end
