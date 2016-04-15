(* Title:       Partial Clausal Logic
    Author:      Mathias Fleury <mathias.fleury at mpi-inf.mpg.de>, 2014
*)

section \<open>Partial Clausal Logic\<close>
text \<open>We here define decided literals (that will be used in both DPLL and CDCL) and the entailment
  corresponding to it.\<close>

theory Partial_Annotated_Clausal_Logic
imports Partial_Clausal_Logic

begin

subsection \<open>Decided Literals\<close>
subsubsection \<open>Definition\<close>
datatype ('v, 'mark) ann_lit =
  is_decided: Decided (lit_of: "'v literal") |
  is_proped: Propagated (lit_of: "'v literal") (mark_of: 'mark)

lemma ann_lit_list_induct[case_names Nil Decided Propagated]:
  assumes "P []" and
  "\<And>L xs. P xs \<Longrightarrow> P (Decided L # xs)" and
  "\<And>L m xs. P xs \<Longrightarrow> P (Propagated L m # xs)"
  shows "P xs"
  using assms apply (induction xs, simp)
  by (rename_tac a xs, case_tac a) auto

lemma is_decided_ex_Decided:
  "is_decided L \<Longrightarrow> (\<And>K. L = Decided K \<Longrightarrow> P) \<Longrightarrow> P"
  by (cases L) auto

type_synonym ('v, 'm) ann_lits = "('v, 'm) ann_lit list"

definition lits_of :: "('a, 'b) ann_lit set \<Rightarrow> 'a literal set" where
"lits_of Ls = lit_of ` Ls"

abbreviation lits_of_l :: "('a, 'b) ann_lits \<Rightarrow> 'a literal set" where
"lits_of_l Ls \<equiv> lits_of (set Ls)"

lemma lits_of_l_empty[simp]:
  "lits_of {} = {}"
  unfolding lits_of_def by auto

lemma lits_of_insert[simp]:
  "lits_of (insert L Ls) = insert (lit_of L) (lits_of Ls)"
  unfolding lits_of_def by auto

lemma lits_of_l_Un[simp]:
  "lits_of (l \<union> l') = lits_of l \<union> lits_of l'"
  unfolding lits_of_def by auto

lemma finite_lits_of_def[simp]:
  "finite (lits_of_l L)"
  unfolding lits_of_def by auto

abbreviation unmark where
"unmark \<equiv> (\<lambda>a. {#lit_of a#})"

abbreviation unmark_s where
"unmark_s M \<equiv> unmark ` M"

abbreviation unmark_l where
"unmark_l M \<equiv> unmark_s (set M)"

lemma atms_of_ms_lambda_lit_of_is_atm_of_lit_of[simp]:
  "atms_of_ms (unmark_l M') = atm_of ` lits_of_l M'"
  unfolding atms_of_ms_def lits_of_def by auto

lemma lits_of_l_empty_is_empty[iff]:
  "lits_of_l M = {} \<longleftrightarrow> M = []"
  by (induct M) (auto simp: lits_of_def)

subsubsection \<open>Entailment\<close>
definition true_annot :: "('a, 'm) ann_lits \<Rightarrow> 'a clause \<Rightarrow> bool" (infix "\<Turnstile>a" 49) where
  "I \<Turnstile>a C \<longleftrightarrow> (lits_of_l I) \<Turnstile> C"

definition true_annots :: "('a, 'm) ann_lits \<Rightarrow> 'a clauses \<Rightarrow> bool" (infix "\<Turnstile>as" 49) where
  "I \<Turnstile>as CC \<longleftrightarrow> (\<forall>C \<in> CC. I \<Turnstile>a C)"

lemma true_annot_empty_model[simp]:
  "\<not>[] \<Turnstile>a \<psi>"
  unfolding true_annot_def true_cls_def by simp

lemma true_annot_empty[simp]:
  "\<not>I \<Turnstile>a {#}"
  unfolding true_annot_def true_cls_def by simp

lemma empty_true_annots_def[iff]:
  "[] \<Turnstile>as \<psi> \<longleftrightarrow> \<psi> = {}"
  unfolding true_annots_def by auto

lemma true_annots_empty[simp]:
  "I \<Turnstile>as {}"
  unfolding true_annots_def by auto

lemma true_annots_single_true_annot[iff]:
  "I \<Turnstile>as {C} \<longleftrightarrow> I \<Turnstile>a C"
  unfolding true_annots_def by auto

lemma true_annot_insert_l[simp]:
  "M \<Turnstile>a A \<Longrightarrow> L # M \<Turnstile>a A"
  unfolding true_annot_def by auto

lemma true_annots_insert_l [simp]:
  "M \<Turnstile>as A \<Longrightarrow> L # M \<Turnstile>as A"
  unfolding true_annots_def by auto

lemma true_annots_union[iff]:
  "M \<Turnstile>as A \<union> B \<longleftrightarrow> (M \<Turnstile>as A \<and> M \<Turnstile>as B)"
  unfolding true_annots_def by auto

lemma true_annots_insert[iff]:
  "M \<Turnstile>as insert a A \<longleftrightarrow> (M \<Turnstile>a a \<and> M \<Turnstile>as A)"
  unfolding true_annots_def by auto

text \<open>Link between \<open>\<Turnstile>as\<close> and \<open>\<Turnstile>s\<close>:\<close>
lemma true_annots_true_cls:
  "I \<Turnstile>as CC \<longleftrightarrow> lits_of_l I \<Turnstile>s CC"
  unfolding true_annots_def Ball_def true_annot_def true_clss_def by auto

(* Before adding a simp/intro flag, think of @{thm true_annot_singleton}*)
lemma in_lit_of_true_annot:
  "a \<in> lits_of_l M \<longleftrightarrow> M \<Turnstile>a {#a#}"
  unfolding true_annot_def lits_of_def by auto

lemma true_annot_lit_of_notin_skip:
  "L # M \<Turnstile>a A \<Longrightarrow> lit_of L \<notin># A \<Longrightarrow> M \<Turnstile>a A"
  unfolding true_annot_def true_cls_def by auto

lemma true_clss_singleton_lit_of_implies_incl:
  "I \<Turnstile>s unmark_l MLs \<Longrightarrow> lits_of_l MLs \<subseteq> I"
  unfolding true_clss_def lits_of_def by auto

lemma true_annot_true_clss_cls:
  "MLs \<Turnstile>a \<psi> \<Longrightarrow> set (map unmark MLs) \<Turnstile>p \<psi>"
  unfolding true_annot_def true_clss_cls_def true_cls_def
  by (auto dest: true_clss_singleton_lit_of_implies_incl)

lemma true_annots_true_clss_cls:
  "MLs \<Turnstile>as \<psi> \<Longrightarrow> set (map unmark MLs) \<Turnstile>ps \<psi>"
  by (auto
    dest: true_clss_singleton_lit_of_implies_incl
    simp add: true_clss_def true_annots_def true_annot_def lits_of_def true_cls_def
    true_clss_clss_def)

lemma true_annots_decided_true_cls[iff]:
  "map Decided M \<Turnstile>as N \<longleftrightarrow> set M \<Turnstile>s N"
proof -
  have *: "lit_of ` Decided ` set M = set M" unfolding lits_of_def by force
  show ?thesis by (simp add: true_annots_true_cls * lits_of_def)
qed

lemma true_annot_singleton[iff]: "M \<Turnstile>a {#L#} \<longleftrightarrow> L \<in> lits_of_l M"
  unfolding true_annot_def lits_of_def by auto

lemma true_annots_true_clss_clss:
  "A \<Turnstile>as \<Psi> \<Longrightarrow> unmark_l A \<Turnstile>ps \<Psi>"
  unfolding true_clss_clss_def true_annots_def true_clss_def
  by (auto dest!: true_clss_singleton_lit_of_implies_incl
    simp: lits_of_def true_annot_def true_cls_def)

lemma true_annot_commute:
  "M @ M' \<Turnstile>a D \<longleftrightarrow> M' @ M \<Turnstile>a D"
  unfolding true_annot_def by (simp add: Un_commute)

lemma true_annots_commute:
  "M @ M' \<Turnstile>as D \<longleftrightarrow> M' @ M \<Turnstile>as D"
  unfolding true_annots_def by (auto simp: true_annot_commute)

lemma true_annot_mono[dest]:
  "set I \<subseteq> set I' \<Longrightarrow> I \<Turnstile>a N \<Longrightarrow> I' \<Turnstile>a N"
  using true_cls_mono_set_mset_l unfolding true_annot_def lits_of_def
  by (metis (no_types) Un_commute Un_upper1 image_Un sup.orderE)

lemma true_annots_mono:
  "set I \<subseteq> set I' \<Longrightarrow> I \<Turnstile>as N \<Longrightarrow> I' \<Turnstile>as N"
  unfolding true_annots_def by auto

subsubsection \<open>Defined and undefined literals\<close>
text \<open>We introduce the functions @{term defined_lit} and @{term undefined_lit} to know whether a
  literal is defined with respect to a list of decided literals (aka a trail in most cases).

  Remark that @{term undefined} already exists and is a completely different Isabelle function.
  \<close>
definition defined_lit :: "('a, 'm) ann_lits \<Rightarrow> 'a literal \<Rightarrow> bool"
  where
"defined_lit I L \<longleftrightarrow> (Decided L \<in> set I) \<or> (\<exists>P. Propagated L P \<in> set I)
  \<or> (Decided (-L) \<in> set I) \<or> (\<exists>P. Propagated (-L) P \<in> set I)"

abbreviation undefined_lit :: "('a, 'm) ann_lits \<Rightarrow> 'a literal \<Rightarrow> bool"
where "undefined_lit I L \<equiv> \<not>defined_lit I L"

lemma defined_lit_rev[simp]:
  "defined_lit (rev M) L \<longleftrightarrow> defined_lit M L"
  unfolding defined_lit_def by auto

lemma atm_imp_decided_or_proped:
  assumes "x \<in> set I"
  shows
    "(Decided (- lit_of x) \<in> set I)
    \<or> (Decided (lit_of x) \<in> set I)
    \<or> (\<exists>l. Propagated (- lit_of x) l \<in> set I)
    \<or> (\<exists>l. Propagated (lit_of x) l \<in> set I)"
  using assms ann_lit.exhaust_sel by metis

lemma literal_is_lit_of_decided:
  assumes "L = lit_of x"
  shows "(x = Decided L) \<or> (\<exists>l'. x = Propagated L l')"
  using assms by (cases x) auto

lemma true_annot_iff_decided_or_true_lit:
  "defined_lit I L \<longleftrightarrow> (lits_of_l I \<Turnstile>l L \<or> lits_of_l I \<Turnstile>l -L)"
  unfolding defined_lit_def by (auto simp add: lits_of_def rev_image_eqI
    dest!: literal_is_lit_of_decided)

lemma consistent_inter_true_annots_satisfiable:
  "consistent_interp (lits_of_l I) \<Longrightarrow> I \<Turnstile>as N \<Longrightarrow> satisfiable N"
  by (simp add: true_annots_true_cls)

lemma defined_lit_map:
  "defined_lit Ls L \<longleftrightarrow> atm_of L \<in> (\<lambda>l. atm_of (lit_of l)) ` set Ls"
 unfolding defined_lit_def apply (rule iffI)
   using image_iff apply fastforce
 by (fastforce simp add: atm_of_eq_atm_of dest: atm_imp_decided_or_proped)

lemma defined_lit_uminus[iff]:
  "defined_lit I (-L) \<longleftrightarrow> defined_lit I L"
  unfolding defined_lit_def by auto

lemma Decided_Propagated_in_iff_in_lits_of_l:
  "defined_lit I L \<longleftrightarrow> (L \<in> lits_of_l I \<or> -L \<in> lits_of_l I)"
  unfolding lits_of_def by (metis lits_of_def true_annot_iff_decided_or_true_lit true_lit_def)

lemma consistent_add_undefined_lit_consistent[simp]:
  assumes
    "consistent_interp (lits_of_l Ls)" and
    "undefined_lit Ls L"
  shows "consistent_interp (insert L (lits_of_l Ls))"
  using assms unfolding consistent_interp_def by (auto simp: Decided_Propagated_in_iff_in_lits_of_l)

lemma decided_empty[simp]:
  "\<not>defined_lit [] L"
  unfolding defined_lit_def by simp

subsection \<open>Backtracking\<close>
fun backtrack_split :: "('v, 'm) ann_lits
  \<Rightarrow> ('v, 'm) ann_lits \<times> ('v, 'm) ann_lits" where
"backtrack_split [] = ([], [])" |
"backtrack_split (Propagated L P # mlits) = apfst ((op #) (Propagated L P)) (backtrack_split mlits)" |
"backtrack_split (Decided L # mlits) = ([], Decided L # mlits)"

lemma backtrack_split_fst_not_decided: "a \<in> set (fst (backtrack_split l)) \<Longrightarrow> \<not>is_decided a"
  by (induct l rule: ann_lit_list_induct) auto

lemma backtrack_split_snd_hd_decided:
  "snd (backtrack_split l) \<noteq> [] \<Longrightarrow> is_decided (hd (snd (backtrack_split l)))"
  by (induct l rule: ann_lit_list_induct) auto

lemma backtrack_split_list_eq[simp]:
  "fst (backtrack_split l) @ (snd (backtrack_split l)) = l"
  by (induct l rule: ann_lit_list_induct) auto

lemma backtrack_snd_empty_not_decided:
  "backtrack_split M = (M'', []) \<Longrightarrow> \<forall>l\<in>set M. \<not> is_decided l"
  by (metis append_Nil2 backtrack_split_fst_not_decided backtrack_split_list_eq snd_conv)

lemma backtrack_split_some_is_decided_then_snd_has_hd:
  "\<exists>l\<in>set M. is_decided l \<Longrightarrow> \<exists>M' L' M''. backtrack_split M = (M'', L' # M')"
  by (metis backtrack_snd_empty_not_decided list.exhaust prod.collapse)

text \<open>Another characterisation of the result of @{const backtrack_split}. This view allows some
  simpler proofs, since @{term takeWhile} and @{term dropWhile} are highly automated:\<close>
lemma backtrack_split_takeWhile_dropWhile:
  "backtrack_split M = (takeWhile (Not o is_decided) M, dropWhile (Not o is_decided) M)"
  by (induction M rule: ann_lit_list_induct) auto

subsection \<open>Decomposition with respect to the First Decided Literals\<close>
text \<open>In this section we define a function that returns a decomposition with the first decided
  literal. This function is useful to define the backtracking of DPLL.\<close>
subsubsection \<open>Definition\<close>
(*TODO: replace apsnd by let? Try to find some better expression on this function.
Ideas:
  * swap the side of Decided
  * case on the form of dropWhile (Not o is_decided)

Split function in 2 + list.product
*)
text \<open>The pattern @{term "get_all_ann_decomposition [] = [([], [])]"} is necessary otherwise, we
  can call the @{term hd} function in the other pattern. \<close>
fun get_all_ann_decomposition :: "('a, 'm) ann_lits
  \<Rightarrow> (('a, 'm) ann_lits \<times> ('a, 'm) ann_lits) list" where
"get_all_ann_decomposition (Decided L # Ls) =
  (Decided L # Ls, []) # get_all_ann_decomposition Ls" |
"get_all_ann_decomposition (Propagated L P# Ls) =
  (apsnd ((op #) (Propagated L P)) (hd (get_all_ann_decomposition Ls)))
    # tl (get_all_ann_decomposition Ls)" |
"get_all_ann_decomposition [] = [([], [])]"

value "get_all_ann_decomposition [Propagated A5 B5, Decided C4, Propagated A3 B3,
  Propagated A2 B2, Decided C1, Propagated A0 B0]"

(*

fun get_all_ann_decomp where
"get_all_ann_decomp [] ls = [([], ls)]" |
"get_all_ann_decomp (L # Ls) ls =
  (if is_decided L then (L # Ls, ls) # get_all_ann_decomp Ls []
   else get_all_ann_decomp Ls (L # ls)) "

abbreviation get_all_ann_decomposition where
"get_all_ann_decomposition l \<equiv> get_all_ann_decomp l []"

lemma get_all_ann_decomposition_never_empty[iff]:
  "get_all_ann_decomp M l = [] \<longleftrightarrow> False"
  by (induct M arbitrary: l, simp) (case_tac a, auto)
*)

text \<open>Now we can prove several simple properties about the function.\<close>

lemma get_all_ann_decomposition_never_empty[iff]:
  "get_all_ann_decomposition M = [] \<longleftrightarrow> False"
  by (induct M, simp) (rename_tac a xs, case_tac a, auto)

lemma get_all_ann_decomposition_never_empty_sym[iff]:
  "[] = get_all_ann_decomposition M \<longleftrightarrow> False"
  using get_all_ann_decomposition_never_empty[of M] by presburger

lemma get_all_ann_decomposition_decomp:
  "hd (get_all_ann_decomposition S) = (a, c) \<Longrightarrow> S = c @ a"
proof (induct S arbitrary: a c)
  case Nil
  then show ?case by simp
next
  case (Cons x A)
  then show ?case by (cases x; cases "hd (get_all_ann_decomposition A)") auto
qed

lemma get_all_ann_decomposition_backtrack_split:
  "backtrack_split S = (M, M') \<longleftrightarrow> hd (get_all_ann_decomposition S) = (M', M)"
proof (induction S arbitrary: M M')
  case Nil
  then show ?case by auto
next
  case (Cons a S)
  then show ?case using backtrack_split_takeWhile_dropWhile by (cases a) force+
qed

lemma get_all_ann_decomposition_Nil_backtrack_split_snd_Nil:
  "get_all_ann_decomposition S = [([], A)] \<Longrightarrow> snd (backtrack_split S) = []"
  by (simp add: get_all_ann_decomposition_backtrack_split sndI)

text \<open>This functions says that the first element is either empty or starts with a decided element
  of the list.\<close>
lemma get_all_ann_decomposition_length_1_fst_empty_or_length_1:
  assumes "get_all_ann_decomposition M = (a, b) # []"
  shows "a = [] \<or> (length a = 1 \<and> is_decided (hd a) \<and> hd a \<in> set M)"
  using assms
proof (induct M arbitrary: a b rule: ann_lit_list_induct)
  case Nil then show ?case by simp
next
  case (Decided L mark)
  then show ?case by simp
next
  case (Propagated L mark M)
  then show ?case by (cases "get_all_ann_decomposition M") force+
qed

lemma get_all_ann_decomposition_fst_empty_or_hd_in_M:
  assumes "get_all_ann_decomposition M = (a, b) # l"
  shows "a = [] \<or> (is_decided (hd a) \<and> hd a \<in> set M)"
  using assms apply (induct M arbitrary: a b rule: ann_lit_list_induct)
    apply auto[2]
  by (metis UnCI backtrack_split_snd_hd_decided get_all_ann_decomposition_backtrack_split
    get_all_ann_decomposition_decomp hd_in_set list.sel(1) set_append snd_conv)

lemma get_all_ann_decomposition_snd_not_decided:
  assumes "(a, b) \<in> set (get_all_ann_decomposition M)"
  and "L \<in> set b"
  shows "\<not>is_decided L"
  using assms apply (induct M arbitrary: a b rule: ann_lit_list_induct, simp)
  by (rename_tac L' xs a b, case_tac "get_all_ann_decomposition xs"; fastforce)+

lemma tl_get_all_ann_decomposition_skip_some:
  assumes "x \<in> set (tl (get_all_ann_decomposition M1))"
  shows "x \<in> set (tl (get_all_ann_decomposition (M0 @ M1)))"
  using assms
  by (induct M0 rule: ann_lit_list_induct)
     (auto simp add: list.set_sel(2))

lemma hd_get_all_ann_decomposition_skip_some:
  assumes "(x, y) = hd (get_all_ann_decomposition M1)"
  shows "(x, y) \<in> set (get_all_ann_decomposition (M0 @ Decided K # M1))"
  using assms
proof (induction M0 rule: ann_lit_list_induct)
  case Nil
  then show ?case by auto
next
  case (Decided L M0)
  then show ?case by auto
next
  case (Propagated L C M0) note xy = this(1)[OF this(2-)] and hd = this(2)
  then show ?case
    by (cases "get_all_ann_decomposition (M0 @ Decided K # M1)")
       (auto dest!: get_all_ann_decomposition_decomp
          arg_cong[of "get_all_ann_decomposition _" _ hd])
qed

lemma in_get_all_ann_decomposition_in_get_all_ann_decomposition_prepend:
  "(a, b) \<in> set (get_all_ann_decomposition M') \<Longrightarrow>
    \<exists>b'. (a, b' @ b) \<in> set (get_all_ann_decomposition (M @ M'))"
  apply (induction M rule: ann_lit_list_induct)
    apply (metis append_Nil)
   apply auto[]
  by (rename_tac L' m xs, case_tac "get_all_ann_decomposition (xs @ M')") auto

lemma in_get_all_ann_decomposition_decided_or_empty:
  assumes "(a, b) \<in> set (get_all_ann_decomposition M)"
  shows "a = [] \<or> (is_decided (hd a))"
  using assms
proof (induct M arbitrary: a b rule: ann_lit_list_induct)
  case Nil then show ?case by simp
next
  case (Decided l M)
  then show ?case by auto
next
  case (Propagated l mark M)
  then show ?case by (cases "get_all_ann_decomposition M") force+
qed

lemma get_all_ann_decomposition_remove_undecided_length:
  assumes "\<forall>l \<in> set M'. \<not>is_decided l"
  shows "length (get_all_ann_decomposition (M' @ M'')) = length (get_all_ann_decomposition M'')"
  using assms by (induct M' arbitrary: M'' rule: ann_lit_list_induct) auto

lemma get_all_ann_decomposition_not_is_decided_length:
  assumes "\<forall>l \<in> set M'. \<not>is_decided l"
  shows "1 + length (get_all_ann_decomposition (Propagated (-L) P # M))
 = length (get_all_ann_decomposition (M' @ Decided L # M))"
 using assms get_all_ann_decomposition_remove_undecided_length by fastforce

lemma get_all_ann_decomposition_last_choice:
  assumes "tl (get_all_ann_decomposition (M' @ Decided L # M)) \<noteq> []"
  and "\<forall>l \<in> set M'. \<not>is_decided l"
  and "hd (tl (get_all_ann_decomposition (M' @ Decided L # M))) = (M0', M0)"
  shows "hd (get_all_ann_decomposition (Propagated (-L) P # M)) = (M0', Propagated (-L) P # M0)"
  using assms by (induct M' rule: ann_lit_list_induct) auto

lemma get_all_ann_decomposition_except_last_choice_equal:
  assumes "\<forall>l \<in> set M'. \<not>is_decided l"
  shows "tl (get_all_ann_decomposition (Propagated (-L) P # M))
 = tl (tl (get_all_ann_decomposition (M' @ Decided L # M)))"
  using assms by (induct M' rule: ann_lit_list_induct) auto

lemma get_all_ann_decomposition_hd_hd:
  assumes "get_all_ann_decomposition Ls = (M, C) # (M0, M0') # l"
  shows "tl M = M0' @ M0 \<and> is_decided (hd M)"
  using assms
proof (induct Ls arbitrary: M C M0 M0' l)
  case Nil
  then show ?case by simp
next
  case (Cons a Ls M C M0 M0' l) note IH = this(1) and g = this(2)
  { fix L level
    assume a: "a = Decided L"
    have "Ls = M0' @ M0"
      using g a by (force intro: get_all_ann_decomposition_decomp)
    then have "tl M = M0' @ M0 \<and> is_decided (hd M)" using g a by auto
  }
  moreover {
    fix L P
    assume a: "a = Propagated L P"
    have "tl M = M0' @ M0 \<and> is_decided (hd M)"
      using IH Cons.prems unfolding a by (cases "get_all_ann_decomposition Ls") auto
  }
  ultimately show ?case by (cases a) auto
qed

lemma get_all_ann_decomposition_exists_prepend[dest]:
  assumes "(a, b) \<in> set (get_all_ann_decomposition M)"
  shows "\<exists>c. M = c @ b @ a"
  using assms apply (induct M rule: ann_lit_list_induct)
    apply simp
  by (rename_tac L' xs, case_tac "get_all_ann_decomposition xs";
    auto dest!: arg_cong[of "get_all_ann_decomposition _" _ hd]
      get_all_ann_decomposition_decomp)+

lemma get_all_ann_decomposition_incl:
  assumes "(a, b) \<in> set (get_all_ann_decomposition M)"
  shows "set b \<subseteq> set M" and "set a \<subseteq> set M"
  using assms get_all_ann_decomposition_exists_prepend by fastforce+

lemma get_all_ann_decomposition_exists_prepend':
  assumes "(a, b) \<in> set (get_all_ann_decomposition M)"
  obtains c where "M = c @ b @ a"
  using assms apply (induct M rule: ann_lit_list_induct)
    apply auto[1]
  by (rename_tac L' xs, case_tac "hd (get_all_ann_decomposition xs)",
    auto dest!: get_all_ann_decomposition_decomp simp add: list.set_sel(2))+

lemma union_in_get_all_ann_decomposition_is_subset:
  assumes "(a, b) \<in> set (get_all_ann_decomposition M)"
  shows "set a \<union> set b \<subseteq> set M"
  using assms by force

lemma Decided_cons_in_get_all_ann_decomposition_append_Decided_cons:
  "\<exists>M1 M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition (c @ Decided K # c'))"
  apply (induction c rule: ann_lit_list_induct)
    apply auto[2]
  apply (rename_tac L xs,
      case_tac "hd (get_all_ann_decomposition (xs @ Decided K # c'))")
  apply (case_tac "get_all_ann_decomposition (xs @ Decided K # c')")
  by auto

lemma fst_get_all_ann_decomposition_prepend_not_decided:
  assumes "\<forall>m\<in>set MS. \<not> is_decided m"
  shows "set (map fst (get_all_ann_decomposition M))
    = set (map fst (get_all_ann_decomposition (MS @ M)))"
    using assms apply (induction MS rule: ann_lit_list_induct)
    apply auto[2]
    by (rename_tac L m xs; case_tac "get_all_ann_decomposition (xs @ M)") simp_all

subsubsection \<open>Entailment of the Propagated by the Decided Literal\<close>
lemma get_all_ann_decomposition_snd_union:
  "set M = \<Union>(set ` snd ` set (get_all_ann_decomposition M)) \<union> {L |L. is_decided L \<and> L \<in> set M}"
  (is "?M M = ?U M \<union> ?Ls M")
proof (induct M rule: ann_lit_list_induct)
  case Nil
  then show ?case by simp
next
  case (Decided L M) note IH = this(1)
  then have "Decided L \<in> ?Ls (Decided L #M)" by auto
  moreover have "?U (Decided L #M) = ?U M" by auto
  moreover have "?M M = ?U M \<union> ?Ls M" using IH by auto
  ultimately show ?case by auto
next
  case (Propagated L m M)
  then show ?case by (cases "(get_all_ann_decomposition M)") auto
qed

definition all_decomposition_implies :: "'a literal multiset set
  \<Rightarrow> (('a, 'm) ann_lits \<times> ('a, 'm) ann_lits) list \<Rightarrow> bool" where
 "all_decomposition_implies N S \<longleftrightarrow> (\<forall>(Ls, seen) \<in> set S. unmark_l Ls \<union> N \<Turnstile>ps unmark_l seen)"

lemma all_decomposition_implies_empty[iff]:
  "all_decomposition_implies N []" unfolding all_decomposition_implies_def by auto

lemma all_decomposition_implies_single[iff]:
  "all_decomposition_implies N [(Ls, seen)] \<longleftrightarrow> unmark_l Ls \<union> N \<Turnstile>ps unmark_l seen"
  unfolding all_decomposition_implies_def by auto

lemma all_decomposition_implies_append[iff]:
  "all_decomposition_implies N (S @ S')
    \<longleftrightarrow> (all_decomposition_implies N S \<and> all_decomposition_implies N S')"
  unfolding all_decomposition_implies_def by auto

lemma all_decomposition_implies_cons_pair[iff]:
  "all_decomposition_implies N ((Ls, seen) # S')
    \<longleftrightarrow> (all_decomposition_implies N [(Ls, seen)] \<and> all_decomposition_implies N S')"
  unfolding all_decomposition_implies_def by auto

lemma all_decomposition_implies_cons_single[iff]:
  "all_decomposition_implies N (l # S') \<longleftrightarrow>
    (unmark_l (fst l) \<union> N \<Turnstile>ps unmark_l (snd l) \<and>
      all_decomposition_implies N S')"
  unfolding all_decomposition_implies_def by auto

lemma all_decomposition_implies_trail_is_implied:
  assumes "all_decomposition_implies N (get_all_ann_decomposition M)"
  shows "N \<union> {unmark L |L. is_decided L \<and> L \<in> set M}
    \<Turnstile>ps unmark ` \<Union>(set ` snd ` set (get_all_ann_decomposition M))"
using assms
proof (induct "length (get_all_ann_decomposition M)" arbitrary: M)
  case 0
  then show ?case by auto
next
  case (Suc n) note IH = this(1) and length = this(2) and decomp = this(3)
  consider
      (le1) "length (get_all_ann_decomposition M) \<le> 1"
    | (gt1) "length (get_all_ann_decomposition M) > 1"
    by arith
  then show ?case
    proof cases
      case le1
      then obtain a b where g: "get_all_ann_decomposition M = (a, b) # []"
        by (cases "get_all_ann_decomposition M") auto
      moreover {
        assume "a = []"
        then have ?thesis using Suc.prems g by auto
      }
      moreover {
        assume l: "length a = 1" and m: "is_decided (hd a)" and hd: "hd a \<in> set M"
        then have "unmark (hd a) \<in> {unmark L |L. is_decided L \<and> L \<in> set M}" by auto
        then have H: "unmark_l a \<union> N \<subseteq> N \<union> {unmark L |L. is_decided L \<and> L \<in> set M}"
          using l by (cases a) auto
        have f1: "unmark_l a \<union> N \<Turnstile>ps unmark_l b"
          using decomp unfolding all_decomposition_implies_def g by simp
        have ?thesis
          apply (rule true_clss_clss_subset) using f1 H g by auto
      }
      ultimately show ?thesis
        using get_all_ann_decomposition_length_1_fst_empty_or_length_1 by blast
    next
      case gt1
      then obtain Ls0 seen0 M' where
        Ls0: "get_all_ann_decomposition M = (Ls0, seen0) # get_all_ann_decomposition M'" and
        length': "length (get_all_ann_decomposition M') = n" and
        M'_in_M: "set M' \<subseteq> set M"
        using length by (induct M rule: ann_lit_list_induct) (auto simp: subset_insertI2)
      let ?d = "\<Union>(set ` snd ` set (get_all_ann_decomposition M'))"
      let ?unM = "{unmark L |L. is_decided L \<and> L \<in> set M}"
      let ?unM' = "{unmark L |L. is_decided L \<and> L \<in> set M'}"
      {
        assume "n = 0"
        then have "get_all_ann_decomposition M' = []" using length' by auto
        then have ?thesis using Suc.prems unfolding all_decomposition_implies_def Ls0 by auto
      }
      moreover {
        assume n: "n > 0"
        then obtain Ls1 seen1 l where
          Ls1: "get_all_ann_decomposition M' = (Ls1, seen1) # l"
          using length' by (induct M' rule: ann_lit_list_induct) auto

        have "all_decomposition_implies N (get_all_ann_decomposition M')"
          using decomp unfolding Ls0 by auto
        then have N: "N \<union> ?unM' \<Turnstile>ps unmark_s ?d"
          using IH length' by auto
        have l: "N \<union> ?unM' \<subseteq> N \<union> ?unM"
          using M'_in_M by auto
        from true_clss_clss_subset[OF this N]
        have \<Psi>N: "N \<union> ?unM \<Turnstile>ps unmark_s ?d" by auto
        have "is_decided (hd Ls0)" and LS: "tl Ls0 = seen1 @ Ls1"
          using get_all_ann_decomposition_hd_hd[of M] unfolding Ls0 Ls1 by auto

        have LSM: "seen1 @ Ls1 = M'" using get_all_ann_decomposition_decomp[of M'] Ls1 by auto
        have M': "set M' = ?d \<union> {L |L. is_decided L \<and> L \<in> set M'}"
          using get_all_ann_decomposition_snd_union by auto

        {
          assume "Ls0 \<noteq> []"
          then have "hd Ls0 \<in> set M"
            using get_all_ann_decomposition_fst_empty_or_hd_in_M Ls0 by blast
          then have "N \<union> ?unM \<Turnstile>p unmark (hd Ls0)"
            using \<open>is_decided (hd Ls0)\<close> by (metis (mono_tags, lifting) UnCI mem_Collect_eq
              true_clss_cls_in)
        } note hd_Ls0 = this

        have l: "unmark ` (?d \<union> {L |L. is_decided L \<and> L \<in> set M'}) = unmark_s ?d \<union> ?unM'"
          by auto
        have "N \<union> ?unM' \<Turnstile>ps unmark ` (?d \<union> {L |L. is_decided L \<and> L \<in> set M'})"
          unfolding l using N by (auto simp: all_in_true_clss_clss)
        then have t: "N \<union> ?unM' \<Turnstile>ps unmark_l (tl Ls0)"
          using M' unfolding LS LSM by auto
        then have "N \<union> ?unM \<Turnstile>ps unmark_l (tl Ls0)"
          using M'_in_M true_clss_clss_subset[OF _ t, of "N \<union> ?unM"] by auto
        then have "N \<union> ?unM \<Turnstile>ps unmark_l Ls0"
          using hd_Ls0 by (cases Ls0) auto

        moreover have "unmark_l Ls0 \<union> N \<Turnstile>ps unmark_l seen0"
          using decomp unfolding Ls0 by simp
        moreover have "\<And>M Ma. (M::'a literal multiset set) \<union> Ma \<Turnstile>ps M"
          by (simp add: all_in_true_clss_clss)
        ultimately have \<Psi>: "N \<union> ?unM \<Turnstile>ps unmark_l seen0"
          by (meson true_clss_clss_left_right true_clss_clss_union_and true_clss_clss_union_l_r)

        moreover have "unmark ` (set seen0 \<union> ?d) = unmark_l seen0 \<union> unmark_s ?d"
          by auto
        ultimately have ?thesis using \<Psi>N unfolding Ls0 by simp
      }
      ultimately show ?thesis by auto
    qed
qed

lemma all_decomposition_implies_propagated_lits_are_implied:
  assumes "all_decomposition_implies N (get_all_ann_decomposition M)"
  shows "N \<union> {unmark L |L. is_decided L \<and> L \<in> set M} \<Turnstile>ps unmark_l M"
    (is "?I \<Turnstile>ps ?A")
proof -
  have "?I \<Turnstile>ps unmark_s {L |L. is_decided L \<and> L \<in> set M}"
    by (auto intro: all_in_true_clss_clss)
  moreover have "?I \<Turnstile>ps unmark ` \<Union>(set ` snd ` set (get_all_ann_decomposition M))"
    using all_decomposition_implies_trail_is_implied assms by blast
  ultimately have "N \<union> {unmark m |m. is_decided m \<and> m \<in> set M}
    \<Turnstile>ps unmark ` \<Union>(set ` snd ` set (get_all_ann_decomposition M))
      \<union> unmark ` {m |m. is_decided m \<and> m \<in> set M}"
      by blast
  then show ?thesis
    by (metis (no_types) get_all_ann_decomposition_snd_union[of M] image_Un)
qed

lemma all_decomposition_implies_insert_single:
  "all_decomposition_implies N M \<Longrightarrow> all_decomposition_implies (insert C N) M"
  unfolding all_decomposition_implies_def by auto

subsection \<open>Negation of Clauses\<close>

text \<open>We define the negation of a @{typ "'a clause"}: it converts it from the a single clause to
  a set of clauses, wherein each clause is a single negated literal.\<close>
definition CNot :: "'v clause \<Rightarrow> 'v clauses" where
"CNot \<psi> = { {#-L#} | L. L \<in># \<psi> }"

lemma in_CNot_uminus[iff]:
  shows "{#L#} \<in> CNot \<psi> \<longleftrightarrow> -L \<in># \<psi>"
  unfolding CNot_def by force

lemma
  shows
    CNot_singleton[simp]: "CNot {#L#} = {{#-L#}}" and
    CNot_empty[simp]: "CNot {#} = {}" and
    CNot_plus[simp]: "CNot (A + B) = CNot A \<union> CNot B"
  unfolding CNot_def by auto

lemma CNot_eq_empty[iff]:
  "CNot D = {} \<longleftrightarrow> D = {#}"
  unfolding CNot_def by (auto simp add: multiset_eqI)

lemma in_CNot_implies_uminus:
  assumes "L \<in># D" and "M \<Turnstile>as CNot D"
  shows "M \<Turnstile>a {#-L#}" and "-L \<in> lits_of_l M"
  using assms by (auto simp: true_annots_def true_annot_def CNot_def)

lemma CNot_remdups_mset[simp]:
  "CNot (remdups_mset A) = CNot A"
  unfolding CNot_def by auto

lemma Ball_CNot_Ball_mset[simp]:
  "(\<forall>x\<in>CNot D. P x) \<longleftrightarrow> (\<forall>L\<in># D. P {#-L#})"
 unfolding CNot_def by auto

lemma consistent_CNot_not:
  assumes "consistent_interp I"
  shows "I \<Turnstile>s CNot \<phi> \<Longrightarrow> \<not>I \<Turnstile> \<phi>"
  using assms unfolding consistent_interp_def true_clss_def true_cls_def by auto

lemma total_not_true_cls_true_clss_CNot:
  assumes "total_over_m I {\<phi>}" and "\<not>I \<Turnstile> \<phi>"
  shows "I \<Turnstile>s CNot \<phi>"
  using assms unfolding total_over_m_def total_over_set_def true_clss_def true_cls_def CNot_def
    apply clarify
  by (rename_tac x L, case_tac L) (force intro: pos_lit_in_atms_of neg_lit_in_atms_of)+

lemma total_not_CNot:
  assumes "total_over_m I {\<phi>}" and "\<not>I \<Turnstile>s CNot \<phi>"
  shows "I \<Turnstile> \<phi>"
  using assms total_not_true_cls_true_clss_CNot by auto

lemma atms_of_ms_CNot_atms_of[simp]:
  "atms_of_ms (CNot C) = atms_of C"
  unfolding atms_of_ms_def atms_of_def CNot_def by fastforce

lemma true_clss_clss_contradiction_true_clss_cls_false:
  "C \<in> D \<Longrightarrow> D \<Turnstile>ps CNot C \<Longrightarrow> D \<Turnstile>p {#}"
  unfolding true_clss_clss_def true_clss_cls_def total_over_m_def
  by (metis Un_commute atms_of_empty atms_of_ms_CNot_atms_of atms_of_ms_insert atms_of_ms_union
    consistent_CNot_not insert_absorb sup_bot.left_neutral true_clss_def)

lemma true_annots_CNot_all_atms_defined:
  assumes "M \<Turnstile>as CNot T" and a1: " L \<in># T"
  shows "atm_of L \<in> atm_of ` lits_of_l M"
  by (metis assms atm_of_uminus image_eqI in_CNot_implies_uminus(1) true_annot_singleton)

lemma true_annots_CNot_all_uminus_atms_defined:
  assumes "M \<Turnstile>as CNot T" and a1: "-L \<in># T"
  shows "atm_of L \<in> atm_of ` lits_of_l M"
  by (metis assms atm_of_uminus image_eqI in_CNot_implies_uminus(1) true_annot_singleton)

lemma true_clss_clss_false_left_right:
  assumes "{{#L#}} \<union> B \<Turnstile>p {#}"
  shows "B \<Turnstile>ps CNot {#L#}"
  unfolding true_clss_clss_def true_clss_cls_def
proof (intro allI impI)
  fix I
  assume
    tot: "total_over_m I (B \<union> CNot {#L#})" and
    cons: "consistent_interp I" and
    I: "I \<Turnstile>s B"
  have "total_over_m I ({{#L#}} \<union> B)" using tot by auto
  then have "\<not>I \<Turnstile>s insert {#L#} B"
    using assms cons unfolding true_clss_cls_def by simp
  then show "I \<Turnstile>s CNot {#L#}"
    using tot I by (cases L) auto
qed

lemma true_annots_true_cls_def_iff_negation_in_model:
  "M \<Turnstile>as CNot C \<longleftrightarrow> (\<forall>L \<in># C. -L \<in> lits_of_l M)"
  unfolding CNot_def true_annots_true_cls true_clss_def by auto

(* TODO Mark as [simp]? *)
lemma true_annot_CNot_diff:
  "I \<Turnstile>as CNot C \<Longrightarrow> I \<Turnstile>as CNot (C - C')"
  by (auto simp: true_annots_true_cls_def_iff_negation_in_model dest: in_diffD)

lemma CNot_mset_replicate[simp]:
  "CNot (mset (replicate n L)) = (if n = 0 then {} else {{#-L#}})"
  by (induction n) auto

lemma consistent_CNot_not_tautology:
  "consistent_interp M \<Longrightarrow> M \<Turnstile>s CNot D \<Longrightarrow> \<not>tautology D"
  by (metis atms_of_ms_CNot_atms_of consistent_CNot_not satisfiable_carac' satisfiable_def
    tautology_def total_over_m_def)

lemma atms_of_ms_CNot_atms_of_ms: "atms_of_ms (CNot CC) = atms_of_ms {CC}"
  by simp

lemma total_over_m_CNot_toal_over_m[simp]:
  "total_over_m I (CNot C) = total_over_set I (atms_of C)"
  unfolding total_over_m_def total_over_set_def by auto

text \<open>The following lemma is very useful when in the goal appears an axioms like @{term "-L = K"}:
  this lemma allows the simplifier to rewrite L.\<close>
lemma uminus_lit_swap: "-(a::'a literal) = i \<longleftrightarrow> a = -i"
  by auto

lemma true_clss_cls_plus_CNot:
  assumes
    CC_L: "A \<Turnstile>p CC + {#L#}" and
    CNot_CC: "A \<Turnstile>ps CNot CC"
  shows "A \<Turnstile>p {#L#}"
  unfolding true_clss_clss_def true_clss_cls_def CNot_def total_over_m_def
proof (intro allI impI)
  fix I
  assume
    tot: "total_over_set I (atms_of_ms (A \<union> {{#L#}}))" and
    cons: "consistent_interp I" and
    I: "I \<Turnstile>s A"
  let ?I = "I \<union> {Pos P|P. P \<in> atms_of CC \<and> P \<notin> atm_of ` I}"
  have cons': "consistent_interp ?I"
    using cons unfolding consistent_interp_def
    by (auto simp: uminus_lit_swap atms_of_def rev_image_eqI)
  have I': "?I \<Turnstile>s A"
    using I true_clss_union_increase by blast
  have tot_CNot: "total_over_m ?I (A \<union> CNot CC)"
    using tot atms_of_s_def by (fastforce simp: total_over_m_def total_over_set_def)

  then have tot_I_A_CC_L: "total_over_m ?I (A \<union> {CC + {#L#}})"
    using tot unfolding total_over_m_def total_over_set_atm_of by auto
  then have "?I \<Turnstile> CC + {#L#}" using CC_L cons' I' unfolding true_clss_cls_def by blast
  moreover
    have "?I \<Turnstile>s CNot CC" using CNot_CC cons' I' tot_CNot unfolding true_clss_clss_def by auto
    then have "\<not>A \<Turnstile>p CC"
      by (metis (no_types, lifting) I' atms_of_ms_CNot_atms_of_ms atms_of_ms_union cons'
        consistent_CNot_not tot_CNot total_over_m_def true_clss_cls_def)
    then have "\<not>?I \<Turnstile> CC" using \<open>?I \<Turnstile>s CNot CC\<close> cons' consistent_CNot_not by blast
  ultimately have "?I \<Turnstile> {#L#}" by blast
  then show "I \<Turnstile> {#L#}"
    by (metis (no_types, lifting) atms_of_ms_union cons' consistent_CNot_not tot total_not_CNot
      total_over_m_def total_over_set_union true_clss_union_increase)
qed

lemma true_annots_CNot_lit_of_notin_skip:
  assumes LM: "L # M \<Turnstile>as CNot A" and LA: "lit_of L \<notin># A" "-lit_of L \<notin># A"
  shows "M \<Turnstile>as CNot A"
  using LM unfolding true_annots_def Ball_def
proof (intro allI impI)
  fix l
  assume H: "\<forall>x. x \<in> CNot A \<longrightarrow> L # M \<Turnstile>a x " and l: "l \<in> CNot A"
  then have "L # M \<Turnstile>a l" by auto
  then show "M \<Turnstile>a l" using LA l by (cases L) (auto simp: CNot_def)
 qed

lemma true_clss_clss_union_false_true_clss_clss_cnot:
  "A \<union> {B} \<Turnstile>ps {{#}} \<longleftrightarrow> A \<Turnstile>ps CNot B"
  using total_not_CNot consistent_CNot_not unfolding total_over_m_def true_clss_clss_def
  by fastforce

lemma true_annot_remove_hd_if_notin_vars:
  assumes "a # M'\<Turnstile>a D" and "atm_of (lit_of a) \<notin> atms_of D"
  shows "M' \<Turnstile>a D"
  using assms true_cls_remove_hd_if_notin_vars unfolding true_annot_def by auto

lemma true_annot_remove_if_notin_vars:
  assumes "M @ M'\<Turnstile>a D" and "\<forall>x\<in>atms_of D. x \<notin> atm_of ` lits_of_l M"
  shows "M' \<Turnstile>a D"
  using assms by (induct M) (auto dest: true_annot_remove_hd_if_notin_vars)

lemma true_annots_remove_if_notin_vars:
  assumes "M @ M'\<Turnstile>as D" and "\<forall>x\<in>atms_of_ms D. x \<notin> atm_of ` lits_of_l M"
  shows "M' \<Turnstile>as D" unfolding true_annots_def
  using assms unfolding true_annots_def atms_of_ms_def
  by (force dest: true_annot_remove_if_notin_vars)

lemma all_variables_defined_not_imply_cnot:
  assumes
    "\<forall>s \<in> atms_of_ms {B}. s \<in> atm_of ` lits_of_l A" and
    "\<not> A \<Turnstile>a B"
  shows "A \<Turnstile>as CNot B"
  unfolding true_annot_def true_annots_def Ball_def CNot_def true_lit_def
proof (clarify, rule ccontr)
  fix L
  assume LB: "L \<in># B" and "\<not> lits_of_l A \<Turnstile>l - L"
  then have "atm_of L \<in> atm_of ` lits_of_l A"
    using assms(1) by (simp add: atm_of_lit_in_atms_of lits_of_def)
  then have "L \<in> lits_of_l A \<or> -L \<in> lits_of_l A"
    using atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set by metis
  then have "L \<in> lits_of_l A" using \<open> \<not> lits_of_l A \<Turnstile>l - L\<close> by auto
  then show False
    using LB assms(2) unfolding true_annot_def true_lit_def true_cls_def Bex_def
    by blast
qed

lemma CNot_union_mset[simp]:
  "CNot (A #\<union> B) = CNot A \<union> CNot B"
  unfolding CNot_def by auto

subsection \<open>Other\<close>
abbreviation "no_dup L \<equiv> distinct (map (\<lambda>l. atm_of (lit_of l)) L)"

lemma no_dup_rev[simp]:
  "no_dup (rev M) \<longleftrightarrow> no_dup M"
  by (auto simp: rev_map[symmetric])

lemma no_dup_length_eq_card_atm_of_lits_of_l:
  assumes "no_dup M"
  shows "length M = card (atm_of ` lits_of_l M)"
  using assms unfolding lits_of_def by (induct M) (auto simp add: image_image)

lemma distinct_consistent_interp:
  "no_dup M \<Longrightarrow> consistent_interp (lits_of_l M)"
proof (induct M)
  case Nil
  show ?case by auto
next
  case (Cons L M)
  then have a1: "consistent_interp (lits_of_l M)" by auto
  have a2: "atm_of (lit_of L) \<notin> (\<lambda>l. atm_of (lit_of l)) ` set M" using Cons.prems by auto
  have "undefined_lit M (lit_of L)"
    using a2 unfolding defined_lit_map by fastforce
  then show ?case
    using a1 by simp
qed

lemma distinct_get_all_ann_decomposition_no_dup:
  assumes "(a, b) \<in> set (get_all_ann_decomposition M)"
  and "no_dup M"
  shows "no_dup (a @ b)"
  using assms by force

lemma true_annots_lit_of_notin_skip:
  assumes "L # M \<Turnstile>as CNot A"
  and "-lit_of L \<notin># A"
  and "no_dup (L # M)"
  shows "M \<Turnstile>as CNot A"
proof -
  have "\<forall>l \<in># A. -l \<in> lits_of_l (L # M)"
    using assms(1) in_CNot_implies_uminus(2) by blast
  moreover
    have "atm_of (lit_of L) \<notin> atm_of ` lits_of_l M"
      using assms(3) unfolding lits_of_def by force
    then have "- lit_of L \<notin> lits_of_l M" unfolding lits_of_def
      by (metis (no_types) atm_of_uminus imageI)
  ultimately have "\<forall> l \<in># A. -l \<in> lits_of_l M"
    using assms(2) by (metis insert_iff list.simps(15) lits_of_insert uminus_of_uminus_id)
  then show ?thesis by (auto simp add: true_annots_def)
qed

subsection \<open>Extending Entailments to multisets\<close>
text \<open>We have defined previous entailment with respect to sets, but we also need a multiset version
  depending on the context. The conversion is simple using the function @{term set_mset} (in this
  direction, there is no loss of information).\<close>
abbreviation true_annots_mset (infix "\<Turnstile>asm" 50) where
"I \<Turnstile>asm C \<equiv> I \<Turnstile>as (set_mset C)"

abbreviation true_clss_clss_m:: "'v clause multiset \<Rightarrow> 'v clause multiset \<Rightarrow> bool" (infix "\<Turnstile>psm" 50)
where
"I \<Turnstile>psm C \<equiv> set_mset I \<Turnstile>ps (set_mset C)"

text \<open>Analog of @{thm true_clss_clss_subsetE}\<close>
lemma true_clss_clssm_subsetE: "N \<Turnstile>psm B \<Longrightarrow> A \<subseteq># B \<Longrightarrow> N \<Turnstile>psm A"
  using set_mset_mono true_clss_clss_subsetE by blast

abbreviation true_clss_cls_m:: "'a clause multiset \<Rightarrow> 'a clause \<Rightarrow> bool" (infix "\<Turnstile>pm" 50) where
"I \<Turnstile>pm C \<equiv> set_mset I \<Turnstile>p C"

abbreviation distinct_mset_mset :: "'a multiset multiset \<Rightarrow> bool" where
"distinct_mset_mset \<Sigma> \<equiv> distinct_mset_set (set_mset \<Sigma>)"

abbreviation all_decomposition_implies_m where
"all_decomposition_implies_m A B \<equiv> all_decomposition_implies (set_mset A) B"

abbreviation atms_of_mm :: "'a literal multiset multiset \<Rightarrow> 'a set" where
"atms_of_mm U \<equiv> atms_of_ms (set_mset U)"

text \<open>Other definition using @{term "Union_mset"}\<close>
lemma "atms_of_mm U \<equiv> set_mset (\<Union># image_mset (image_mset atm_of) U)"
  unfolding atms_of_ms_def by (auto simp: atms_of_def)

abbreviation true_clss_m:: "'a interp \<Rightarrow> 'a clause multiset \<Rightarrow> bool" (infix "\<Turnstile>sm" 50) where
"I \<Turnstile>sm C \<equiv> I \<Turnstile>s set_mset C"

abbreviation true_clss_ext_m (infix "\<Turnstile>sextm" 49) where
"I \<Turnstile>sextm C \<equiv> I \<Turnstile>sext set_mset C"

end
