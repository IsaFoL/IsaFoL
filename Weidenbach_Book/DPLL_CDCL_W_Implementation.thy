theory DPLL_CDCL_W_Implementation
imports Partial_Annotated_Clausal_Logic
begin

section \<open>Simple Implementation of the DPLL and CDCL\<close>
subsection \<open>Common Rules\<close>
subsubsection \<open>Propagation\<close>
text \<open>The following theorem holds:\<close>
lemma lits_of_unfold[iff]:
  "(\<forall>c \<in> set C. -c \<in> lits_of Ms) \<longleftrightarrow> Ms \<Turnstile>as CNot (mset C)"
  unfolding true_annots_def Ball_def true_annot_def CNot_def mem_set_multiset_eq by auto
text \<open>The right-hand version is written at a high-level, but only the left-hand side is executable.\<close>

definition is_unit_clause :: "'a literal list \<Rightarrow> ('a, 'b, 'c) ann_literal list \<Rightarrow> 'a literal option"
 where
 "is_unit_clause l M =
   (case List.filter (\<lambda>a. atm_of a \<notin> atm_of ` lits_of M) l of
     a # [] \<Rightarrow> if M \<Turnstile>as CNot (mset l - {#a#}) then Some a else None
   | _ \<Rightarrow> None)"

definition is_unit_clause_code :: "'a literal list \<Rightarrow> ('a, 'b, 'c) ann_literal list
  \<Rightarrow> 'a literal option" where
 "is_unit_clause_code l M =
   (case List.filter (\<lambda>a. atm_of a \<notin> atm_of ` lits_of M) l of
     a # [] \<Rightarrow> if (\<forall>c \<in>set (remove1 a l). -c \<in> lits_of M) then Some a else None
   | _ \<Rightarrow> None)"

lemma is_unit_clause_is_unit_clause_code[code]:
  "is_unit_clause l M = is_unit_clause_code l M"
proof -
  have 1: "\<And>a. (\<forall>c\<in>set (remove1 a l). - c \<in> lits_of M) \<longleftrightarrow> M \<Turnstile>as CNot (mset l - {#a#})"
    using lits_of_unfold[of "remove1 _ l", of _ M] by simp
  thus ?thesis
    unfolding is_unit_clause_code_def is_unit_clause_def 1 by blast
qed

lemma is_unit_clause_some_undef:
  assumes "is_unit_clause l M = Some a"
  shows "undefined_lit M a"
proof -
  have "(case [a\<leftarrow>l . atm_of a \<notin> atm_of ` lits_of M] of [] \<Rightarrow> None
          | [a] \<Rightarrow> if M \<Turnstile>as CNot (mset l - {#a#}) then Some a else None
          | a # ab # xa \<Rightarrow> Map.empty xa) = Some a"
    using assms unfolding is_unit_clause_def .
  hence "a \<in> set [a\<leftarrow>l . atm_of a \<notin> atm_of ` lits_of M]"
    apply (cases "[a\<leftarrow>l . atm_of a \<notin> atm_of ` lits_of M]")
      apply simp
    apply (rename_tac aa list; case_tac list) by (auto split: split_if_asm)
  hence "atm_of a \<notin> atm_of ` lits_of M" by auto
  thus ?thesis
    by (simp add: Marked_Propagated_in_iff_in_lits_of
      atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set )
qed

lemma is_unit_clause_some_CNot: "is_unit_clause l M = Some a \<Longrightarrow> M \<Turnstile>as CNot (mset l - {#a#})"
  unfolding is_unit_clause_def
proof -
  assume "(case [a\<leftarrow>l . atm_of a \<notin> atm_of ` lits_of M] of [] \<Rightarrow> None
          | [a] \<Rightarrow> if M \<Turnstile>as CNot (mset l - {#a#}) then Some a else None
          | a # ab # xa \<Rightarrow> Map.empty xa) = Some a"
  thus ?thesis
    apply (cases "[a\<leftarrow>l . atm_of a \<notin> atm_of ` lits_of M]", simp)
      apply simp
    apply (rename_tac aa list, case_tac list) by (auto split: split_if_asm)
qed

lemma is_unit_clause_some_in: "is_unit_clause l M = Some a \<Longrightarrow> a \<in> set l"
  unfolding is_unit_clause_def
proof -
  assume "(case [a\<leftarrow>l . atm_of a \<notin> atm_of ` lits_of M] of [] \<Rightarrow> None
         | [a] \<Rightarrow> if M \<Turnstile>as CNot (mset l - {#a#}) then Some a else None
         | a # ab # xa \<Rightarrow> Map.empty xa) = Some a"
  thus "a \<in> set l"
    by (cases "[a\<leftarrow>l . atm_of a \<notin> atm_of ` lits_of M]")
       (fastforce dest: filter_eq_ConsD split: split_if_asm  split: list.splits)+
qed

lemma is_unit_clause_nil[simp]: "is_unit_clause [] M = None"
  unfolding is_unit_clause_def by auto

subsubsection \<open>Unit propagation for all clauses\<close>
text \<open>Finding the first clause to propagate\<close>
fun find_first_unit_clause :: "'a literal list list \<Rightarrow> ('a, 'b, 'c) ann_literal list
  \<Rightarrow> ('a literal \<times> 'a literal list) option"  where
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
  assumes dist: "distinct c" and
  M: "M \<Turnstile>as CNot (mset c - {#a#})" and
  undef: "undefined_lit M a" and
  ac: "a \<in> set c"
  shows "is_unit_clause c M \<noteq> None"
proof -
  have "[a\<leftarrow>c . atm_of a \<notin> atm_of ` lits_of M] = [a]"
    using assms
    proof (induction c)
      case Nil thus ?case by simp
    next
      case (Cons ac c)
      show ?case
        proof (cases "a = ac")
          case True
          thus ?thesis using Cons
            by (auto simp del: lits_of_unfold
                 simp add: lits_of_unfold[symmetric] Marked_Propagated_in_iff_in_lits_of
                   atm_of_eq_atm_of atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set)
        next
          case False
          hence T: "mset c + {#ac#} - {#a#} = mset c - {#a#} + {#ac#}"
            by (auto simp add: multiset_eq_iff)
          show ?thesis using False Cons
            by (auto simp add: T atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set)
        qed
    qed
  thus ?thesis
    using M unfolding is_unit_clause_def by auto
qed

lemma find_first_unit_clause_none:
  "distinct c \<Longrightarrow> c \<in> set l \<Longrightarrow>  M \<Turnstile>as CNot (mset c - {#a#}) \<Longrightarrow> undefined_lit M a \<Longrightarrow> a \<in> set c
  \<Longrightarrow> find_first_unit_clause l M \<noteq> None"
  by (induction l)
     (auto split: option.split simp add: propagate_is_unit_clause_not_None)

subsubsection \<open>Decide\<close>
fun find_first_unused_var :: "'a literal list list \<Rightarrow> 'a literal set \<Rightarrow> 'a literal option"  where
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
  thus "\<not>(\<forall>a \<in> set l. atm_of ` set a \<subseteq> atm_of `  M)" by auto
qed

lemma find_first_unused_var_Some:
  "find_first_unused_var l M = Some a \<Longrightarrow> (\<exists>m \<in> set l. a \<in> set m \<and> a \<notin> M \<and> -a \<notin> M)"
  by (induct l) (auto split: option.splits dest: find_some)

lemma find_first_unused_var_undefined:
  "find_first_unused_var l (lits_of Ms) = Some a \<Longrightarrow> undefined_lit Ms a"
  using find_first_unused_var_Some[of l "lits_of Ms" a] Marked_Propagated_in_iff_in_lits_of
  by blast

end
