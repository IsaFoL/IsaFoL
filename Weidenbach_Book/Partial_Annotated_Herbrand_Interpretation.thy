(* Title:       Partial Clausal Logic
    Author:      Mathias Fleury <mathias.fleury at mpi-inf.mpg.de>, 2014
*)

section \<open>Partial Annotated Herbrand Interpretation\<close>
text \<open>We here define decided literals (that will be used in both DPLL and CDCL) and the entailment
  corresponding to it.\<close>

theory Partial_Annotated_Herbrand_Interpretation
imports
   Partial_Herbrand_Interpretation
begin


subsection \<open>Decided Literals\<close>

subsubsection \<open>Definition\<close>

datatype ('v, 'w, 'mark) annotated_lit =
  is_decided: Decided (lit_dec: 'v) |
  is_proped: Propagated (lit_prop: 'w) (mark_of: 'mark)

type_synonym ('v, 'w, 'mark) annotated_lits = \<open>('v, 'w, 'mark) annotated_lit list\<close>
type_synonym ('v, 'mark) ann_lit = \<open>('v literal, 'v literal, 'mark) annotated_lit\<close>

lemma ann_lit_list_induct[case_names Nil Decided Propagated]:
  assumes
    \<open>P []\<close> and
    \<open>\<And>L xs. P xs \<Longrightarrow> P (Decided L # xs)\<close> and
    \<open>\<And>L m xs. P xs \<Longrightarrow> P (Propagated L m # xs)\<close>
  shows \<open>P xs\<close>
  using assms apply (induction xs, simp)
  by (rename_tac a xs, case_tac a) auto

lemma is_decided_ex_Decided:
  \<open>is_decided L \<Longrightarrow> (\<And>K. L = Decided K \<Longrightarrow> P) \<Longrightarrow> P\<close>
  by (cases L) auto

lemma is_propedE: \<open>is_proped L \<Longrightarrow> (\<And>K C. L = Propagated K C \<Longrightarrow> P) \<Longrightarrow> P\<close>
  by (cases L) auto

lemma is_decided_no_proped_iff: \<open>is_decided L \<longleftrightarrow> \<not>is_proped L\<close>
  by (cases L) auto

lemma not_is_decidedE:
  \<open>\<not>is_decided E \<Longrightarrow> (\<And>K C. E = Propagated K C \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
  by (cases E) auto

type_synonym ('v, 'm) ann_lits = \<open>('v, 'm) ann_lit list\<close>

fun lit_of :: \<open>('a, 'a, 'mark) annotated_lit \<Rightarrow> 'a\<close> where
  \<open>lit_of (Decided L) = L\<close> |
  \<open>lit_of (Propagated L _) = L\<close>

definition lits_of :: \<open>('a, 'b) ann_lit set \<Rightarrow> 'a literal set\<close> where
\<open>lits_of Ls = lit_of ` Ls\<close>

abbreviation lits_of_l :: \<open>('a, 'b) ann_lits \<Rightarrow> 'a literal set\<close> where
\<open>lits_of_l Ls \<equiv> lits_of (set Ls)\<close>

lemma lits_of_l_empty[simp]:
  \<open>lits_of {} = {}\<close>
  unfolding lits_of_def by auto

lemma lits_of_insert[simp]:
  \<open>lits_of (insert L Ls) = insert (lit_of L) (lits_of Ls)\<close>
  unfolding lits_of_def by auto

lemma lits_of_l_Un[simp]:
  \<open>lits_of (l \<union> l') = lits_of l \<union> lits_of l'\<close>
  unfolding lits_of_def by auto

lemma finite_lits_of_def[simp]:
  \<open>finite (lits_of_l L)\<close>
  unfolding lits_of_def by auto

abbreviation unmark where
  \<open>unmark \<equiv> (\<lambda>a. {#lit_of a#})\<close>

abbreviation unmark_s where
  \<open>unmark_s M \<equiv> unmark ` M\<close>

abbreviation unmark_l where
  \<open>unmark_l M \<equiv> unmark_s (set M)\<close>

lemma atms_of_ms_lambda_lit_of_is_atm_of_lit_of[simp]:
  \<open>atms_of_ms (unmark_l M') = atm_of ` lits_of_l M'\<close>
  unfolding atms_of_ms_def lits_of_def by auto

lemma lits_of_l_empty_is_empty[iff]:
  \<open>lits_of_l M = {} \<longleftrightarrow> M = []\<close>
  by (induct M) (auto simp: lits_of_def)

lemma in_unmark_l_in_lits_of_l_iff: \<open>{#L#} \<in> unmark_l M \<longleftrightarrow> L \<in> lits_of_l M\<close>
  by (induction M) auto

lemma atm_lit_of_set_lits_of_l:
  "(\<lambda>l. atm_of (lit_of l)) ` set xs = atm_of ` lits_of_l xs"
  unfolding lits_of_def by auto


subsubsection \<open>Entailment\<close>

definition true_annot :: \<open>('a, 'm) ann_lits \<Rightarrow> 'a clause \<Rightarrow> bool\<close> (infix "\<Turnstile>a" 49) where
  \<open>I \<Turnstile>a C \<longleftrightarrow> (lits_of_l I) \<Turnstile> C\<close>

definition true_annots :: \<open>('a, 'm) ann_lits \<Rightarrow> 'a clause_set \<Rightarrow> bool\<close> (infix "\<Turnstile>as" 49) where
  \<open>I \<Turnstile>as CC \<longleftrightarrow> (\<forall>C \<in> CC. I \<Turnstile>a C)\<close>

lemma true_annot_empty_model[simp]:
  \<open>\<not>[] \<Turnstile>a \<psi>\<close>
  unfolding true_annot_def true_cls_def by simp

lemma true_annot_empty[simp]:
  \<open>\<not>I \<Turnstile>a {#}\<close>
  unfolding true_annot_def true_cls_def by simp

lemma empty_true_annots_def[iff]:
  \<open>[] \<Turnstile>as \<psi> \<longleftrightarrow> \<psi> = {}\<close>
  unfolding true_annots_def by auto

lemma true_annots_empty[simp]:
  \<open>I \<Turnstile>as {}\<close>
  unfolding true_annots_def by auto

lemma true_annots_single_true_annot[iff]:
  \<open>I \<Turnstile>as {C} \<longleftrightarrow> I \<Turnstile>a C\<close>
  unfolding true_annots_def by auto

lemma true_annot_insert_l[simp]:
  \<open>M \<Turnstile>a A \<Longrightarrow> L # M \<Turnstile>a A\<close>
  unfolding true_annot_def by auto

lemma true_annots_insert_l [simp]:
  \<open>M \<Turnstile>as A \<Longrightarrow> L # M \<Turnstile>as A\<close>
  unfolding true_annots_def by auto

lemma true_annots_union[iff]:
  \<open>M \<Turnstile>as A \<union> B \<longleftrightarrow> (M \<Turnstile>as A \<and> M \<Turnstile>as B)\<close>
  unfolding true_annots_def by auto

lemma true_annots_insert[iff]:
  \<open>M \<Turnstile>as insert a A \<longleftrightarrow> (M \<Turnstile>a a \<and> M \<Turnstile>as A)\<close>
  unfolding true_annots_def by auto

lemma true_annot_append_l:
  \<open>M \<Turnstile>a A \<Longrightarrow> M' @ M \<Turnstile>a A\<close>
  unfolding true_annot_def by auto

lemma true_annots_append_l:
  \<open>M \<Turnstile>as A \<Longrightarrow> M' @ M \<Turnstile>as A\<close>
  unfolding true_annots_def by (auto simp: true_annot_append_l)

text \<open>Link between \<open>\<Turnstile>as\<close> and \<open>\<Turnstile>s\<close>:\<close>
lemma true_annots_true_cls:
  \<open>I \<Turnstile>as CC \<longleftrightarrow> lits_of_l I \<Turnstile>s CC\<close>
  unfolding true_annots_def Ball_def true_annot_def true_clss_def by auto

lemma in_lit_of_true_annot:
  \<open>a \<in> lits_of_l M \<longleftrightarrow> M \<Turnstile>a {#a#}\<close>
  unfolding true_annot_def lits_of_def by auto

lemma true_annot_lit_of_notin_skip:
  \<open>L # M \<Turnstile>a A \<Longrightarrow> lit_of L \<notin># A \<Longrightarrow> M \<Turnstile>a A\<close>
  unfolding true_annot_def true_cls_def by auto

lemma true_clss_singleton_lit_of_implies_incl:
  \<open>I \<Turnstile>s unmark_l MLs \<Longrightarrow> lits_of_l MLs \<subseteq> I\<close>
  unfolding true_clss_def lits_of_def by auto

lemma true_annot_true_clss_cls:
  \<open>MLs \<Turnstile>a \<psi> \<Longrightarrow> set (map unmark MLs) \<Turnstile>p \<psi>\<close>
  unfolding true_annot_def true_clss_cls_def true_cls_def
  by (auto dest: true_clss_singleton_lit_of_implies_incl)

lemma true_annots_true_clss_cls:
  \<open>MLs \<Turnstile>as \<psi> \<Longrightarrow> set (map unmark MLs) \<Turnstile>ps \<psi>\<close>
  by (auto
    dest: true_clss_singleton_lit_of_implies_incl
    simp add: true_clss_def true_annots_def true_annot_def lits_of_def true_cls_def
    true_clss_clss_def)

lemma true_annots_decided_true_cls[iff]:
  \<open>map Decided M \<Turnstile>as N \<longleftrightarrow> set M \<Turnstile>s N\<close>
proof -
  have *: \<open>lit_of ` Decided ` set M = set M\<close> unfolding lits_of_def by force
  show ?thesis by (simp add: true_annots_true_cls * lits_of_def)
qed

lemma true_annot_singleton[iff]: \<open>M \<Turnstile>a {#L#} \<longleftrightarrow> L \<in> lits_of_l M\<close>
  unfolding true_annot_def lits_of_def by auto

lemma true_annots_true_clss_clss:
  \<open>A \<Turnstile>as \<Psi> \<Longrightarrow> unmark_l A \<Turnstile>ps \<Psi>\<close>
  unfolding true_clss_clss_def true_annots_def true_clss_def
  by (auto dest!: true_clss_singleton_lit_of_implies_incl
    simp: lits_of_def true_annot_def true_cls_def)

lemma true_annot_commute:
  \<open>M @ M' \<Turnstile>a D \<longleftrightarrow> M' @ M \<Turnstile>a D\<close>
  unfolding true_annot_def by (simp add: Un_commute)

lemma true_annots_commute:
  \<open>M @ M' \<Turnstile>as D \<longleftrightarrow> M' @ M \<Turnstile>as D\<close>
  unfolding true_annots_def by (auto simp: true_annot_commute)

lemma true_annot_mono[dest]:
  \<open>set I \<subseteq> set I' \<Longrightarrow> I \<Turnstile>a N \<Longrightarrow> I' \<Turnstile>a N\<close>
  using true_cls_mono_set_mset_l unfolding true_annot_def lits_of_def
  by (metis (no_types) Un_commute Un_upper1 image_Un sup.orderE)

lemma true_annots_mono:
  \<open>set I \<subseteq> set I' \<Longrightarrow> I \<Turnstile>as N \<Longrightarrow> I' \<Turnstile>as N\<close>
  unfolding true_annots_def by auto


subsubsection \<open>Defined and Undefined Literals\<close>

text \<open>We introduce the functions @{term defined_lit} and @{term undefined_lit} to know whether a
  literal is defined with respect to a list of decided literals (aka a trail in most cases).

  Remark that @{term undefined} already exists and is a completely different Isabelle function.
  \<close>
definition defined_lit :: \<open>('a literal, 'a literal, 'm) annotated_lits \<Rightarrow> 'a literal \<Rightarrow> bool\<close>
  where
\<open>defined_lit I L \<longleftrightarrow> (Decided L \<in> set I) \<or> (\<exists>P. Propagated L P \<in> set I)
  \<or> (Decided (-L) \<in> set I) \<or> (\<exists>P. Propagated (-L) P \<in> set I)\<close>

abbreviation undefined_lit :: \<open>('a literal, 'a literal, 'm) annotated_lits \<Rightarrow> 'a literal \<Rightarrow> bool\<close>
where \<open>undefined_lit I L \<equiv> \<not>defined_lit I L\<close>

lemma defined_lit_rev[simp]:
  \<open>defined_lit (rev M) L \<longleftrightarrow> defined_lit M L\<close>
  unfolding defined_lit_def by auto

lemma atm_imp_decided_or_proped:
  assumes \<open>x \<in> set I\<close>
  shows
    \<open>(Decided (- lit_of x) \<in> set I)
    \<or> (Decided (lit_of x) \<in> set I)
    \<or> (\<exists>l. Propagated (- lit_of x) l \<in> set I)
    \<or> (\<exists>l. Propagated (lit_of x) l \<in> set I)\<close>
  using assms by (metis (full_types) lit_of.elims)

lemma literal_is_lit_of_decided:
  assumes \<open>L = lit_of x\<close>
  shows \<open>(x = Decided L) \<or> (\<exists>l'. x = Propagated L l')\<close>
  using assms by (cases x) auto

lemma true_annot_iff_decided_or_true_lit:
  \<open>defined_lit I L \<longleftrightarrow> (lits_of_l I \<Turnstile>l L \<or> lits_of_l I \<Turnstile>l -L)\<close>
  unfolding defined_lit_def by (auto simp add: lits_of_def rev_image_eqI
    dest!: literal_is_lit_of_decided)

lemma consistent_inter_true_annots_satisfiable:
  \<open>consistent_interp (lits_of_l I) \<Longrightarrow> I \<Turnstile>as N \<Longrightarrow> satisfiable N\<close>
  by (simp add: true_annots_true_cls)

lemma defined_lit_map:
  \<open>defined_lit Ls L \<longleftrightarrow> atm_of L \<in> (\<lambda>l. atm_of (lit_of l)) ` set Ls\<close>
 unfolding defined_lit_def apply (rule iffI)
   using image_iff apply fastforce
 by (fastforce simp add: atm_of_eq_atm_of dest: atm_imp_decided_or_proped)

lemma defined_lit_uminus[iff]:
  \<open>defined_lit I (-L) \<longleftrightarrow> defined_lit I L\<close>
  unfolding defined_lit_def by auto

lemma Decided_Propagated_in_iff_in_lits_of_l:
  \<open>defined_lit I L \<longleftrightarrow> (L \<in> lits_of_l I \<or> -L \<in> lits_of_l I)\<close>
  unfolding lits_of_def by (metis lits_of_def true_annot_iff_decided_or_true_lit true_lit_def)

lemma consistent_add_undefined_lit_consistent[simp]:
  assumes
    \<open>consistent_interp (lits_of_l Ls)\<close> and
    \<open>undefined_lit Ls L\<close>
  shows \<open>consistent_interp (insert L (lits_of_l Ls))\<close>
  using assms unfolding consistent_interp_def by (auto simp: Decided_Propagated_in_iff_in_lits_of_l)

lemma decided_empty[simp]:
  \<open>\<not>defined_lit [] L\<close>
  unfolding defined_lit_def by simp

lemma undefined_lit_single[iff]:
  \<open>defined_lit [L] K \<longleftrightarrow> atm_of (lit_of L) = atm_of K\<close>
  by (auto simp: defined_lit_map)

lemma undefined_lit_cons[iff]:
  \<open>undefined_lit (L # M) K \<longleftrightarrow> atm_of (lit_of L) \<noteq> atm_of K \<and> undefined_lit M K\<close>
  by (auto simp: defined_lit_map)

lemma undefined_lit_append[iff]:
  \<open>undefined_lit (M @ M') K \<longleftrightarrow> undefined_lit M K \<and> undefined_lit M' K\<close>
  by (auto simp: defined_lit_map)

lemma defined_lit_cons:
  \<open>defined_lit (L # M) K \<longleftrightarrow> atm_of (lit_of L) = atm_of K \<or> defined_lit M K\<close>
  by (auto simp: defined_lit_map)

lemma defined_lit_append:
  \<open>defined_lit (M @ M') K \<longleftrightarrow> defined_lit M K \<or> defined_lit M' K\<close>
  by (auto simp: defined_lit_map)

lemma in_lits_of_l_defined_litD: \<open>L_max \<in> lits_of_l M \<Longrightarrow> defined_lit M L_max\<close>
  by (auto simp: Decided_Propagated_in_iff_in_lits_of_l)

lemma undefined_notin: \<open>undefined_lit M (lit_of x) \<Longrightarrow> x \<notin> set M\<close> for x M
  by (metis in_lits_of_l_defined_litD insert_iff lits_of_insert mk_disjoint_insert)

lemma uminus_lits_of_l_definedD:
  \<open>-x \<in> lits_of_l M \<Longrightarrow> defined_lit M x\<close>
  by (simp add: Decided_Propagated_in_iff_in_lits_of_l)

lemma defined_lit_Neg_Pos_iff:
  \<open>defined_lit M (Neg A) \<longleftrightarrow> defined_lit M (Pos A)\<close>
  by (simp add: defined_lit_map)

lemma defined_lit_Pos_atm_iff[simp]:
  \<open>defined_lit M1 (Pos (atm_of x)) \<longleftrightarrow> defined_lit M1 x\<close>
  by (cases x) (auto simp: defined_lit_Neg_Pos_iff)

lemma defined_lit_mono:
  \<open>defined_lit M2 L \<Longrightarrow> set M2 \<subseteq> set M3 \<Longrightarrow> defined_lit M3 L\<close>
  by (auto simp: Decided_Propagated_in_iff_in_lits_of_l)

lemma defined_lit_nth:
  \<open>n < length M2 \<Longrightarrow> defined_lit M2 (lit_of (M2 ! n))\<close>
  by (auto simp: Decided_Propagated_in_iff_in_lits_of_l lits_of_def)


subsection \<open>Backtracking\<close>

fun backtrack_split :: \<open>('a, 'v, 'm) annotated_lits
  \<Rightarrow> ('a, 'v, 'm) annotated_lits \<times> ('a, 'v, 'm) annotated_lits\<close> where
\<open>backtrack_split [] = ([], [])\<close> |
\<open>backtrack_split (Propagated L P # mlits) = apfst ((#) (Propagated L P)) (backtrack_split mlits)\<close> |
\<open>backtrack_split (Decided L # mlits) = ([], Decided L # mlits)\<close>

lemma backtrack_split_fst_not_decided: \<open>a \<in> set (fst (backtrack_split l)) \<Longrightarrow> \<not>is_decided a\<close>
  by (induct l rule: ann_lit_list_induct) auto

lemma backtrack_split_snd_hd_decided:
  \<open>snd (backtrack_split l) \<noteq> [] \<Longrightarrow> is_decided (hd (snd (backtrack_split l)))\<close>
  by (induct l rule: ann_lit_list_induct) auto

lemma backtrack_split_list_eq[simp]:
  \<open>fst (backtrack_split l) @ (snd (backtrack_split l)) = l\<close>
  by (induct l rule: ann_lit_list_induct) auto

lemma backtrack_snd_empty_not_decided:
  \<open>backtrack_split M = (M'', []) \<Longrightarrow> \<forall>l\<in>set M. \<not> is_decided l\<close>
  by (metis append_Nil2 backtrack_split_fst_not_decided backtrack_split_list_eq snd_conv)

lemma backtrack_split_some_is_decided_then_snd_has_hd:
  \<open>\<exists>l\<in>set M. is_decided l \<Longrightarrow> \<exists>M' L' M''. backtrack_split M = (M'', L' # M')\<close>
  by (metis backtrack_snd_empty_not_decided list.exhaust prod.collapse)

text \<open>Another characterisation of the result of @{const backtrack_split}. This view allows some
  simpler proofs, since @{term takeWhile} and @{term dropWhile} are highly automated:\<close>
lemma backtrack_split_takeWhile_dropWhile:
  \<open>backtrack_split M = (takeWhile (Not o is_decided) M, dropWhile (Not o is_decided) M)\<close>
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
text \<open>The pattern @{term \<open>get_all_ann_decomposition [] = [([], [])]\<close>} is necessary otherwise, we
  can call the @{term hd} function in the other pattern. \<close>
fun get_all_ann_decomposition :: \<open>('a, 'b, 'm) annotated_lits
  \<Rightarrow> (('a, 'b, 'm) annotated_lits \<times> ('a, 'b, 'm) annotated_lits) list\<close> where
\<open>get_all_ann_decomposition (Decided L # Ls) =
  (Decided L # Ls, []) # get_all_ann_decomposition Ls\<close> |
\<open>get_all_ann_decomposition (Propagated L P# Ls) =
  (apsnd ((#) (Propagated L P)) (hd (get_all_ann_decomposition Ls)))
    # tl (get_all_ann_decomposition Ls)\<close> |
\<open>get_all_ann_decomposition [] = [([], [])]\<close>

value \<open>get_all_ann_decomposition [Propagated A5 B5, Decided C4, Propagated A3 B3,
  Propagated A2 B2, Decided C1, Propagated A0 B0]\<close>

(*

fun get_all_ann_decomp where
\<open>get_all_ann_decomp [] ls = [([], ls)]\<close> |
\<open>get_all_ann_decomp (L # Ls) ls =
  (if is_decided L then (L # Ls, ls) # get_all_ann_decomp Ls []
   else get_all_ann_decomp Ls (L # ls)) \<close>

abbreviation get_all_ann_decomposition where
\<open>get_all_ann_decomposition l \<equiv> get_all_ann_decomp l []\<close>

lemma get_all_ann_decomposition_never_empty[iff]:
  \<open>get_all_ann_decomp M l = [] \<longleftrightarrow> False\<close>
  by (induct M arbitrary: l, simp) (case_tac a, auto)
*)

text \<open>Now we can prove several simple properties about the function.\<close>

lemma get_all_ann_decomposition_never_empty[iff]:
  \<open>get_all_ann_decomposition M = [] \<longleftrightarrow> False\<close>
  by (induct M, simp) (rename_tac a xs, case_tac a, auto)

lemma get_all_ann_decomposition_never_empty_sym[iff]:
  \<open>[] = get_all_ann_decomposition M \<longleftrightarrow> False\<close>
  using get_all_ann_decomposition_never_empty[of M] by presburger

lemma get_all_ann_decomposition_decomp:
  \<open>hd (get_all_ann_decomposition S) = (a, c) \<Longrightarrow> S = c @ a\<close>
proof (induct S arbitrary: a c)
  case Nil
  then show ?case by simp
next
  case (Cons x A)
  then show ?case by (cases x; cases \<open>hd (get_all_ann_decomposition A)\<close>) auto
qed

lemma get_all_ann_decomposition_backtrack_split:
  \<open>backtrack_split S = (M, M') \<longleftrightarrow> hd (get_all_ann_decomposition S) = (M', M)\<close>
proof (induction S arbitrary: M M')
  case Nil
  then show ?case by auto
next
  case (Cons a S)
  then show ?case using backtrack_split_takeWhile_dropWhile by (cases a) force+
qed

lemma get_all_ann_decomposition_Nil_backtrack_split_snd_Nil:
  \<open>get_all_ann_decomposition S = [([], A)] \<Longrightarrow> snd (backtrack_split S) = []\<close>
  by (simp add: get_all_ann_decomposition_backtrack_split sndI)

text \<open>This functions says that the first element is either empty or starts with a decided element
  of the list.\<close>
lemma get_all_ann_decomposition_length_1_fst_empty_or_length_1:
  assumes \<open>get_all_ann_decomposition M = (a, b) # []\<close>
  shows \<open>a = [] \<or> (length a = 1 \<and> is_decided (hd a) \<and> hd a \<in> set M)\<close>
  using assms
proof (induct M arbitrary: a b rule: ann_lit_list_induct)
  case Nil then show ?case by simp
next
  case (Decided L mark)
  then show ?case by simp
next
  case (Propagated L mark M)
  then show ?case by (cases \<open>get_all_ann_decomposition M\<close>) force+
qed

lemma get_all_ann_decomposition_fst_empty_or_hd_in_M:
  assumes \<open>get_all_ann_decomposition M = (a, b) # l\<close>
  shows \<open>a = [] \<or> (is_decided (hd a) \<and> hd a \<in> set M)\<close>
  using assms
proof (induct M arbitrary: a b rule: ann_lit_list_induct)
  case Nil
  then show ?case by auto
next
  case (Decided L ann xs)
  then show ?case by auto
next
  case (Propagated L m xs) note IH = this(1) and d = this(2)
  then show ?case
    using IH[of \<open>fst (hd (get_all_ann_decomposition xs))\<close> \<open>snd (hd(get_all_ann_decomposition xs))\<close>]
    by (cases \<open>get_all_ann_decomposition xs\<close>; cases a) auto
qed

lemma get_all_ann_decomposition_snd_not_decided:
  assumes \<open>(a, b) \<in> set (get_all_ann_decomposition M)\<close>
  and \<open>L \<in> set b\<close>
  shows \<open>\<not>is_decided L\<close>
  using assms apply (induct M arbitrary: a b rule: ann_lit_list_induct, simp)
  by (rename_tac L' xs a b, case_tac \<open>get_all_ann_decomposition xs\<close>; fastforce)+

lemma tl_get_all_ann_decomposition_skip_some:
  assumes \<open>x \<in> set (tl (get_all_ann_decomposition M1))\<close>
  shows \<open>x \<in> set (tl (get_all_ann_decomposition (M0 @ M1)))\<close>
  using assms
  by (induct M0 rule: ann_lit_list_induct)
     (auto simp add: list.set_sel(2))

lemma hd_get_all_ann_decomposition_skip_some:
  assumes \<open>(x, y) = hd (get_all_ann_decomposition M1)\<close>
  shows \<open>(x, y) \<in> set (get_all_ann_decomposition (M0 @ Decided K # M1))\<close>
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
    by (cases \<open>get_all_ann_decomposition (M0 @ Decided K # M1)\<close>)
       (auto dest!: get_all_ann_decomposition_decomp
          arg_cong[of \<open>get_all_ann_decomposition _\<close> _ hd])
qed

lemma in_get_all_ann_decomposition_in_get_all_ann_decomposition_prepend:
  \<open>(a, b) \<in> set (get_all_ann_decomposition M') \<Longrightarrow>
    \<exists>b'. (a, b' @ b) \<in> set (get_all_ann_decomposition (M @ M'))\<close>
  apply (induction M rule: ann_lit_list_induct)
    apply (metis append_Nil)
   apply auto[]
  by (rename_tac L' m xs, case_tac \<open>get_all_ann_decomposition (xs @ M')\<close>) auto

lemma in_get_all_ann_decomposition_decided_or_empty:
  assumes \<open>(a, b) \<in> set (get_all_ann_decomposition M)\<close>
  shows \<open>a = [] \<or> (is_decided (hd a))\<close>
  using assms
proof (induct M arbitrary: a b rule: ann_lit_list_induct)
  case Nil then show ?case by simp
next
  case (Decided l M)
  then show ?case by auto
next
  case (Propagated l mark M)
  then show ?case by (cases \<open>get_all_ann_decomposition M\<close>) force+
qed

lemma get_all_ann_decomposition_remove_undecided_length:
  assumes \<open>\<forall>l \<in> set M'. \<not>is_decided l\<close>
  shows \<open>length (get_all_ann_decomposition (M' @ M'')) = length (get_all_ann_decomposition M'')\<close>
  using assms by (induct M' arbitrary: M'' rule: ann_lit_list_induct) auto

lemma get_all_ann_decomposition_not_is_decided_length:
  assumes \<open>\<forall>l \<in> set M'. \<not>is_decided l\<close>
  shows \<open>1 + length (get_all_ann_decomposition (Propagated (-L) P # M))
 = length (get_all_ann_decomposition (M' @ Decided L # M))\<close>
 using assms get_all_ann_decomposition_remove_undecided_length by fastforce

lemma get_all_ann_decomposition_last_choice:
  assumes \<open>tl (get_all_ann_decomposition (M' @ Decided L # M)) \<noteq> []\<close>
  and \<open>\<forall>l \<in> set M'. \<not>is_decided l\<close>
  and \<open>hd (tl (get_all_ann_decomposition (M' @ Decided L # M))) = (M0', M0)\<close>
  shows \<open>hd (get_all_ann_decomposition (Propagated (-L) P # M)) = (M0', Propagated (-L) P # M0)\<close>
  using assms by (induct M' rule: ann_lit_list_induct) auto

lemma get_all_ann_decomposition_except_last_choice_equal:
  assumes \<open>\<forall>l \<in> set M'. \<not>is_decided l\<close>
  shows \<open>tl (get_all_ann_decomposition (Propagated (-L) P # M))
 = tl (tl (get_all_ann_decomposition (M' @ Decided L # M)))\<close>
  using assms by (induct M' rule: ann_lit_list_induct) auto

lemma get_all_ann_decomposition_hd_hd:
  assumes \<open>get_all_ann_decomposition Ls = (M, C) # (M0, M0') # l\<close>
  shows \<open>tl M = M0' @ M0 \<and> is_decided (hd M)\<close>
  using assms
proof (induct Ls arbitrary: M C M0 M0' l)
  case Nil
  then show ?case by simp
next
  case (Cons a Ls M C M0 M0' l) note IH = this(1) and g = this(2)
  { fix L ann level
    assume a: \<open>a = Decided L\<close>
    have \<open>Ls = M0' @ M0\<close>
      using g a by (force intro: get_all_ann_decomposition_decomp)
    then have \<open>tl M = M0' @ M0 \<and> is_decided (hd M)\<close> using g a by auto
  }
  moreover {
    fix L P
    assume a: \<open>a = Propagated L P\<close>
    have \<open>tl M = M0' @ M0 \<and> is_decided (hd M)\<close>
      using IH Cons.prems unfolding a by (cases \<open>get_all_ann_decomposition Ls\<close>) auto
  }
  ultimately show ?case by (cases a) auto
qed

lemma get_all_ann_decomposition_exists_prepend[dest]:
  assumes \<open>(a, b) \<in> set (get_all_ann_decomposition M)\<close>
  shows \<open>\<exists>c. M = c @ b @ a\<close>
  using assms apply (induct M rule: ann_lit_list_induct)
    apply simp
  by (rename_tac L' xs, case_tac \<open>get_all_ann_decomposition xs\<close>;
    auto dest!: arg_cong[of \<open>get_all_ann_decomposition _\<close> _ hd]
      get_all_ann_decomposition_decomp)+

lemma get_all_ann_decomposition_incl:
  assumes \<open>(a, b) \<in> set (get_all_ann_decomposition M)\<close>
  shows \<open>set b \<subseteq> set M\<close> and \<open>set a \<subseteq> set M\<close>
  using assms get_all_ann_decomposition_exists_prepend by fastforce+

lemma get_all_ann_decomposition_exists_prepend':
  assumes \<open>(a, b) \<in> set (get_all_ann_decomposition M)\<close>
  obtains c where \<open>M = c @ b @ a\<close>
  using assms apply (induct M rule: ann_lit_list_induct)
    apply auto[1]
  by (rename_tac L' xs, case_tac \<open>hd (get_all_ann_decomposition xs)\<close>,
    auto dest!: get_all_ann_decomposition_decomp simp add: list.set_sel(2))+

lemma union_in_get_all_ann_decomposition_is_subset:
  assumes \<open>(a, b) \<in> set (get_all_ann_decomposition M)\<close>
  shows \<open>set a \<union> set b \<subseteq> set M\<close>
  using assms by force

lemma Decided_cons_in_get_all_ann_decomposition_append_Decided_cons:
  \<open>\<exists>c''. (Decided K # c, c'') \<in> set (get_all_ann_decomposition (c' @ Decided K # c))\<close>
  apply (induction c' rule: ann_lit_list_induct)
    apply auto[2]
  apply (rename_tac L xs,
      case_tac \<open>hd (get_all_ann_decomposition (xs @ Decided K # c))\<close>)
  apply (case_tac \<open>get_all_ann_decomposition (xs @ Decided K # c)\<close>)
  by auto

lemma fst_get_all_ann_decomposition_prepend_not_decided:
  assumes \<open>\<forall>m\<in>set MS. \<not> is_decided m\<close>
  shows \<open>set (map fst (get_all_ann_decomposition M))
    = set (map fst (get_all_ann_decomposition (MS @ M)))\<close>
  using assms apply (induction MS rule: ann_lit_list_induct)
  apply auto[2]
  by (rename_tac L m xs; case_tac \<open>get_all_ann_decomposition (xs @ M)\<close>) simp_all

lemma no_decision_get_all_ann_decomposition:
  \<open>\<forall>l\<in>set M. \<not> is_decided l \<Longrightarrow>  get_all_ann_decomposition M = [([], M)]\<close>
  by (induction M rule: ann_lit_list_induct) auto


subsubsection \<open>Entailment of the Propagated by the Decided Literal\<close>

lemma get_all_ann_decomposition_snd_union:
  \<open>set M = \<Union>(set ` snd ` set (get_all_ann_decomposition M)) \<union> {L |L. is_decided L \<and> L \<in> set M}\<close>
  (is \<open>?M M = ?U M \<union> ?Ls M\<close>)
proof (induct M rule: ann_lit_list_induct)
  case Nil
  then show ?case by simp
next
  case (Decided L M) note IH = this(1)
  then have \<open>Decided L \<in> ?Ls (Decided L # M)\<close> by auto
  moreover have \<open>?U (Decided L # M) = ?U M\<close> by auto
  moreover have \<open>?M M = ?U M \<union> ?Ls M\<close> using IH by auto
  ultimately show ?case by auto
next
  case (Propagated L m M)
  then show ?case by (cases \<open>(get_all_ann_decomposition M)\<close>) auto
qed



definition all_decomposition_implies :: \<open>'a clause set
  \<Rightarrow> (('a, 'm) ann_lits \<times> ('a, 'm) ann_lits) list \<Rightarrow> bool\<close> where
 \<open>all_decomposition_implies N S \<longleftrightarrow> (\<forall>(Ls, seen) \<in> set S. unmark_l Ls \<union> N \<Turnstile>ps unmark_l seen)\<close>

lemma all_decomposition_implies_empty[iff]:
  \<open>all_decomposition_implies N []\<close> unfolding all_decomposition_implies_def by auto

lemma all_decomposition_implies_single[iff]:
  \<open>all_decomposition_implies N [(Ls, seen)] \<longleftrightarrow> unmark_l Ls \<union> N \<Turnstile>ps unmark_l seen\<close>
  unfolding all_decomposition_implies_def by auto

lemma all_decomposition_implies_append[iff]:
  \<open>all_decomposition_implies N (S @ S')
    \<longleftrightarrow> (all_decomposition_implies N S \<and> all_decomposition_implies N S')\<close>
  unfolding all_decomposition_implies_def by auto

lemma all_decomposition_implies_cons_pair[iff]:
  \<open>all_decomposition_implies N ((Ls, seen) # S')
    \<longleftrightarrow> (all_decomposition_implies N [(Ls, seen)] \<and> all_decomposition_implies N S')\<close>
  unfolding all_decomposition_implies_def by auto

lemma all_decomposition_implies_cons_single[iff]:
  \<open>all_decomposition_implies N (l # S') \<longleftrightarrow>
    (unmark_l (fst l) \<union> N \<Turnstile>ps unmark_l (snd l) \<and>
      all_decomposition_implies N S')\<close>
  unfolding all_decomposition_implies_def by auto

lemma all_decomposition_implies_trail_is_implied:
  assumes \<open>all_decomposition_implies N (get_all_ann_decomposition M)\<close>
  shows \<open>N \<union> {unmark L |L. is_decided L \<and> L \<in> set M}
    \<Turnstile>ps unmark ` \<Union>(set ` snd ` set (get_all_ann_decomposition M))\<close>
using assms
proof (induct \<open>length (get_all_ann_decomposition M)\<close> arbitrary: M)
  case 0
  then show ?case by auto
next
  case (Suc n) note IH = this(1) and length = this(2) and decomp = this(3)
  consider
      (le1) \<open>length (get_all_ann_decomposition M) \<le> 1\<close>
    | (gt1) \<open>length (get_all_ann_decomposition M) > 1\<close>
    by arith
  then show ?case
    proof cases
      case le1
      then obtain a b where g: \<open>get_all_ann_decomposition M = (a, b) # []\<close>
        by (cases \<open>get_all_ann_decomposition M\<close>) auto
      moreover {
        assume \<open>a = []\<close>
        then have ?thesis using Suc.prems g by auto
      }
      moreover {
        assume l: \<open>length a = 1\<close> and m: \<open>is_decided (hd a)\<close> and hd: \<open>hd a \<in> set M\<close>
        then have \<open>unmark (hd a) \<in> {unmark L |L. is_decided L \<and> L \<in> set M}\<close> by auto
        then have H: \<open>unmark_l a \<union> N \<subseteq> N \<union> {unmark L |L. is_decided L \<and> L \<in> set M}\<close>
          using l by (cases a) auto
        have f1: \<open>unmark_l a \<union> N \<Turnstile>ps unmark_l b\<close>
          using decomp unfolding all_decomposition_implies_def g by simp
        have ?thesis
          apply (rule true_clss_clss_subset) using f1 H g by auto
      }
      ultimately show ?thesis
        using get_all_ann_decomposition_length_1_fst_empty_or_length_1 by blast
    next
      case gt1
      then obtain Ls0 seen0 M' where
        Ls0: \<open>get_all_ann_decomposition M = (Ls0, seen0) # get_all_ann_decomposition M'\<close> and
        length': \<open>length (get_all_ann_decomposition M') = n\<close> and
        M'_in_M: \<open>set M' \<subseteq> set M\<close>
        using length by (induct M rule: ann_lit_list_induct) (auto simp: subset_insertI2)
      let ?d = \<open>\<Union>(set ` snd ` set (get_all_ann_decomposition M'))\<close>
      let ?unM = \<open>{unmark L |L. is_decided L \<and> L \<in> set M}\<close>
      let ?unM' = \<open>{unmark L |L. is_decided L \<and> L \<in> set M'}\<close>
      {
        assume \<open>n = 0\<close>
        then have \<open>get_all_ann_decomposition M' = []\<close> using length' by auto
        then have ?thesis using Suc.prems unfolding all_decomposition_implies_def Ls0 by auto
      }
      moreover {
        assume n: \<open>n > 0\<close>
        then obtain Ls1 seen1 l where
          Ls1: \<open>get_all_ann_decomposition M' = (Ls1, seen1) # l\<close>
          using length' by (induct M' rule: ann_lit_list_induct) auto

        have \<open>all_decomposition_implies N (get_all_ann_decomposition M')\<close>
          using decomp unfolding Ls0 by auto
        then have N: \<open>N \<union> ?unM' \<Turnstile>ps unmark_s ?d\<close>
          using IH length' by auto
        have l: \<open>N \<union> ?unM' \<subseteq> N \<union> ?unM\<close>
          using M'_in_M by auto
        from true_clss_clss_subset[OF this N]
        have \<Psi>N: \<open>N \<union> ?unM \<Turnstile>ps unmark_s ?d\<close> by auto
        have \<open>is_decided (hd Ls0)\<close> and LS: \<open>tl Ls0 = seen1 @ Ls1\<close>
          using get_all_ann_decomposition_hd_hd[of M] unfolding Ls0 Ls1 by auto

        have LSM: \<open>seen1 @ Ls1 = M'\<close> using get_all_ann_decomposition_decomp[of M'] Ls1 by auto
        have M': \<open>set M' = ?d \<union> {L |L. is_decided L \<and> L \<in> set M'}\<close>
          using get_all_ann_decomposition_snd_union by auto

        {
          assume \<open>Ls0 \<noteq> []\<close>
          then have \<open>hd Ls0 \<in> set M\<close>
            using get_all_ann_decomposition_fst_empty_or_hd_in_M Ls0 by blast
          then have \<open>N \<union> ?unM \<Turnstile>p unmark (hd Ls0)\<close>
            using \<open>is_decided (hd Ls0)\<close> by (metis (mono_tags, lifting) UnCI mem_Collect_eq
              true_clss_cls_in)
        } note hd_Ls0 = this

        have l: \<open>unmark ` (?d \<union> {L |L. is_decided L \<and> L \<in> set M'}) = unmark_s ?d \<union> ?unM'\<close>
          by auto
        have \<open>N \<union> ?unM' \<Turnstile>ps unmark ` (?d \<union> {L |L. is_decided L \<and> L \<in> set M'})\<close>
          unfolding l using N by (auto simp: all_in_true_clss_clss)
        then have t: \<open>N \<union> ?unM' \<Turnstile>ps unmark_l (tl Ls0)\<close>
          using M' unfolding LS LSM by auto
        then have \<open>N \<union> ?unM \<Turnstile>ps unmark_l (tl Ls0)\<close>
          using M'_in_M true_clss_clss_subset[OF _ t, of \<open>N \<union> ?unM\<close>] by auto
        then have \<open>N \<union> ?unM \<Turnstile>ps unmark_l Ls0\<close>
          using hd_Ls0 by (cases Ls0) auto

        moreover have \<open>unmark_l Ls0 \<union> N \<Turnstile>ps unmark_l seen0\<close>
          using decomp unfolding Ls0 by simp
        moreover have \<open>\<And>M Ma. (M::'a clause set) \<union> Ma \<Turnstile>ps M\<close>
          by (simp add: all_in_true_clss_clss)
        ultimately have \<Psi>: \<open>N \<union> ?unM \<Turnstile>ps unmark_l seen0\<close>
          by (meson true_clss_clss_left_right true_clss_clss_union_and true_clss_clss_union_l_r)

        moreover have \<open>unmark ` (set seen0 \<union> ?d) = unmark_l seen0 \<union> unmark_s ?d\<close>
          by auto
        ultimately have ?thesis using \<Psi>N unfolding Ls0 by simp
      }
      ultimately show ?thesis by auto
    qed
qed

lemma all_decomposition_implies_propagated_lits_are_implied:
  assumes \<open>all_decomposition_implies N (get_all_ann_decomposition M)\<close>
  shows \<open>N \<union> {unmark L |L. is_decided L \<and> L \<in> set M} \<Turnstile>ps unmark_l M\<close>
    (is \<open>?I \<Turnstile>ps ?A\<close>)
proof -
  have \<open>?I \<Turnstile>ps unmark_s {L |L. is_decided L \<and> L \<in> set M}\<close>
    by (auto intro: all_in_true_clss_clss)
  moreover have \<open>?I \<Turnstile>ps unmark ` \<Union>(set ` snd ` set (get_all_ann_decomposition M))\<close>
    using all_decomposition_implies_trail_is_implied assms by blast
  ultimately have \<open>N \<union> {unmark m |m. is_decided m \<and> m \<in> set M}
    \<Turnstile>ps unmark ` \<Union>(set ` snd ` set (get_all_ann_decomposition M))
      \<union> unmark ` {m |m. is_decided m \<and> m \<in> set M}\<close>
      by blast
  then show ?thesis
    by (metis (no_types) get_all_ann_decomposition_snd_union[of M] image_Un)
qed

lemma all_decomposition_implies_insert_single:
  \<open>all_decomposition_implies N M \<Longrightarrow> all_decomposition_implies (insert C N) M\<close>
  unfolding all_decomposition_implies_def by auto

lemma all_decomposition_implies_union:
  \<open>all_decomposition_implies N M \<Longrightarrow> all_decomposition_implies (N \<union> N') M\<close>
  unfolding all_decomposition_implies_def sup.assoc[symmetric] by (auto intro: true_clss_clss_union_l)

lemma all_decomposition_implies_mono:
  \<open>N \<subseteq> N' \<Longrightarrow> all_decomposition_implies N M \<Longrightarrow> all_decomposition_implies N' M\<close>
  by (metis all_decomposition_implies_union le_iff_sup)

lemma all_decomposition_implies_mono_right:
  \<open>all_decomposition_implies I (get_all_ann_decomposition (M' @ M)) \<Longrightarrow>
    all_decomposition_implies I (get_all_ann_decomposition M)\<close>
  apply (induction M' arbitrary: M rule: ann_lit_list_induct)
  subgoal by auto
  subgoal by auto
  subgoal for L C M' M
    by (cases \<open>get_all_ann_decomposition (M' @ M)\<close>) auto
  done


subsection \<open>Negation of a Clause\<close>

text \<open>
  We define the negation of a @{typ \<open>'a clause\<close>}: it converts a single clause to a set of clauses,
  where each clause is a single literal (whose negation is in the original clause).\<close>
definition CNot :: \<open>'v clause \<Rightarrow> 'v clause_set\<close> where
\<open>CNot \<psi> = { {#-L#} | L. L \<in># \<psi> }\<close>

lemma finite_CNot[simp]: \<open>finite (CNot C)\<close>
  by (auto simp: CNot_def)

lemma in_CNot_uminus[iff]:
  shows \<open>{#L#} \<in> CNot \<psi> \<longleftrightarrow> -L \<in># \<psi>\<close>
  unfolding CNot_def by force

lemma
  shows
    CNot_add_mset[simp]: \<open>CNot (add_mset L \<psi>) = insert {#-L#} (CNot \<psi>)\<close> and
    CNot_empty[simp]: \<open>CNot {#} = {}\<close> and
    CNot_plus[simp]: \<open>CNot (A + B) = CNot A \<union> CNot B\<close>
  unfolding CNot_def by auto

lemma CNot_eq_empty[iff]:
  \<open>CNot D = {} \<longleftrightarrow> D = {#}\<close>
  unfolding CNot_def by (auto simp add: multiset_eqI)

lemma in_CNot_implies_uminus:
  assumes \<open>L \<in># D\<close> and \<open>M \<Turnstile>as CNot D\<close>
  shows \<open>M \<Turnstile>a {#-L#}\<close> and \<open>-L \<in> lits_of_l M\<close>
  using assms by (auto simp: true_annots_def true_annot_def CNot_def)

lemma CNot_remdups_mset[simp]:
  \<open>CNot (remdups_mset A) = CNot A\<close>
  unfolding CNot_def by auto

lemma Ball_CNot_Ball_mset[simp]:
  \<open>(\<forall>x\<in>CNot D. P x) \<longleftrightarrow> (\<forall>L\<in># D. P {#-L#})\<close>
 unfolding CNot_def by auto

lemma consistent_CNot_not:
  assumes \<open>consistent_interp I\<close>
  shows \<open>I \<Turnstile>s CNot \<phi> \<Longrightarrow> \<not>I \<Turnstile> \<phi>\<close>
  using assms unfolding consistent_interp_def true_clss_def true_cls_def by auto

lemma total_not_true_cls_true_clss_CNot:
  assumes \<open>total_over_m I {\<phi>}\<close> and \<open>\<not>I \<Turnstile> \<phi>\<close>
  shows \<open>I \<Turnstile>s CNot \<phi>\<close>
  using assms unfolding total_over_m_def total_over_set_def true_clss_def true_cls_def CNot_def
    apply clarify
  by (rename_tac x L, case_tac L) (force intro: pos_lit_in_atms_of neg_lit_in_atms_of)+

lemma total_not_CNot:
  assumes \<open>total_over_m I {\<phi>}\<close> and \<open>\<not>I \<Turnstile>s CNot \<phi>\<close>
  shows \<open>I \<Turnstile> \<phi>\<close>
  using assms total_not_true_cls_true_clss_CNot by auto

lemma atms_of_ms_CNot_atms_of[simp]:
  \<open>atms_of_ms (CNot C) = atms_of C\<close>
  unfolding atms_of_ms_def atms_of_def CNot_def by fastforce

lemma true_clss_clss_contradiction_true_clss_cls_false:
  \<open>C \<in> D \<Longrightarrow> D \<Turnstile>ps CNot C \<Longrightarrow> D \<Turnstile>p {#}\<close>
  unfolding true_clss_clss_def true_clss_cls_def total_over_m_def
  by (metis Un_commute atms_of_empty atms_of_ms_CNot_atms_of atms_of_ms_insert atms_of_ms_union
    consistent_CNot_not insert_absorb sup_bot.left_neutral true_clss_def)

lemma true_annots_CNot_all_atms_defined:
  assumes \<open>M \<Turnstile>as CNot T\<close> and a1: \<open>L \<in># T\<close>
  shows \<open>atm_of L \<in> atm_of ` lits_of_l M\<close>
  by (metis assms atm_of_uminus image_eqI in_CNot_implies_uminus(1) true_annot_singleton)

lemma true_annots_CNot_all_uminus_atms_defined:
  assumes \<open>M \<Turnstile>as CNot T\<close> and a1: \<open>-L \<in># T\<close>
  shows \<open>atm_of L \<in> atm_of ` lits_of_l M\<close>
  by (metis assms atm_of_uminus image_eqI in_CNot_implies_uminus(1) true_annot_singleton)

lemma true_clss_clss_false_left_right:
  assumes \<open>{{#L#}} \<union> B \<Turnstile>p {#}\<close>
  shows \<open>B \<Turnstile>ps CNot {#L#}\<close>
  unfolding true_clss_clss_def true_clss_cls_def
proof (intro allI impI)
  fix I
  assume
    tot: \<open>total_over_m I (B \<union> CNot {#L#})\<close> and
    cons: \<open>consistent_interp I\<close> and
    I: \<open>I \<Turnstile>s B\<close>
  have \<open>total_over_m I ({{#L#}} \<union> B)\<close> using tot by auto
  then have \<open>\<not>I \<Turnstile>s insert {#L#} B\<close>
    using assms cons unfolding true_clss_cls_def by simp
  then show \<open>I \<Turnstile>s CNot {#L#}\<close>
    using tot I by (cases L) auto
qed

lemma true_annots_true_cls_def_iff_negation_in_model:
  \<open>M \<Turnstile>as CNot C \<longleftrightarrow> (\<forall>L \<in># C. -L \<in> lits_of_l M)\<close>
  unfolding CNot_def true_annots_true_cls true_clss_def by auto

lemma true_clss_def_iff_negation_in_model:
  \<open>M \<Turnstile>s CNot C \<longleftrightarrow> (\<forall>l \<in># C. -l \<in> M)\<close>
  by (auto simp: CNot_def true_clss_def)

lemma true_annots_CNot_definedD:
  \<open>M \<Turnstile>as CNot C \<Longrightarrow> \<forall>L \<in># C. defined_lit M L\<close>
  unfolding true_annots_true_cls_def_iff_negation_in_model
  by (auto simp: Decided_Propagated_in_iff_in_lits_of_l)

(* TODO Mark as [simp]? *)
lemma true_annot_CNot_diff:
  \<open>I \<Turnstile>as CNot C \<Longrightarrow> I \<Turnstile>as CNot (C - C')\<close>
  by (auto simp: true_annots_true_cls_def_iff_negation_in_model dest: in_diffD)

lemma CNot_mset_replicate[simp]:
  \<open>CNot (mset (replicate n L)) = (if n = 0 then {} else {{#-L#}})\<close>
  by (induction n) auto

lemma consistent_CNot_not_tautology:
  \<open>consistent_interp M \<Longrightarrow> M \<Turnstile>s CNot D \<Longrightarrow> \<not>tautology D\<close>
  by (metis atms_of_ms_CNot_atms_of consistent_CNot_not satisfiable_carac' satisfiable_def
    tautology_def total_over_m_def)

lemma atms_of_ms_CNot_atms_of_ms: \<open>atms_of_ms (CNot CC) = atms_of_ms {CC}\<close>
  by simp

lemma total_over_m_CNot_toal_over_m[simp]:
  \<open>total_over_m I (CNot C) = total_over_set I (atms_of C)\<close>
  unfolding total_over_m_def total_over_set_def by auto

lemma true_clss_cls_plus_CNot:
  assumes
    CC_L: \<open>A \<Turnstile>p add_mset L CC\<close> and
    CNot_CC: \<open>A \<Turnstile>ps CNot CC\<close>
  shows \<open>A \<Turnstile>p {#L#}\<close>
  unfolding true_clss_clss_def true_clss_cls_def CNot_def total_over_m_def
proof (intro allI impI)
  fix I
  assume
    tot: \<open>total_over_set I (atms_of_ms (A \<union> {{#L#}}))\<close> and
    cons: \<open>consistent_interp I\<close> and
    I: \<open>I \<Turnstile>s A\<close>
  let ?I = \<open>I \<union> {Pos P|P. P \<in> atms_of CC \<and> P \<notin> atm_of ` I}\<close>
  have cons': \<open>consistent_interp ?I\<close>
    using cons unfolding consistent_interp_def
    by (auto simp: uminus_lit_swap atms_of_def rev_image_eqI)
  have I': \<open>?I \<Turnstile>s A\<close>
    using I true_clss_union_increase by blast
  have tot_CNot: \<open>total_over_m ?I (A \<union> CNot CC)\<close>
    using tot atms_of_s_def by (fastforce simp: total_over_m_def total_over_set_def)

  then have tot_I_A_CC_L: \<open>total_over_m ?I (A \<union> {add_mset L CC})\<close>
    using tot unfolding total_over_m_def total_over_set_atm_of by auto
  then have \<open>?I \<Turnstile> add_mset L CC\<close> using CC_L cons' I' unfolding true_clss_cls_def by blast
  moreover
    have \<open>?I \<Turnstile>s CNot CC\<close> using CNot_CC cons' I' tot_CNot unfolding true_clss_clss_def by auto
    then have \<open>\<not>A \<Turnstile>p CC\<close>
      by (metis (no_types, lifting) I' atms_of_ms_CNot_atms_of_ms atms_of_ms_union cons'
        consistent_CNot_not tot_CNot total_over_m_def true_clss_cls_def)
    then have \<open>\<not>?I \<Turnstile> CC\<close> using \<open>?I \<Turnstile>s CNot CC\<close> cons' consistent_CNot_not by blast
  ultimately have \<open>?I \<Turnstile> {#L#}\<close> by blast
  then show \<open>I \<Turnstile> {#L#}\<close>
    by (metis (no_types, lifting) atms_of_ms_union cons' consistent_CNot_not tot total_not_CNot
      total_over_m_def total_over_set_union true_clss_union_increase)
qed

lemma true_annots_CNot_lit_of_notin_skip:
  assumes LM: \<open>L # M \<Turnstile>as CNot A\<close> and LA: \<open>lit_of L \<notin># A\<close> \<open>-lit_of L \<notin># A\<close>
  shows \<open>M \<Turnstile>as CNot A\<close>
  using LM unfolding true_annots_def Ball_def
proof (intro allI impI)
  fix l
  assume H: \<open>\<forall>x. x \<in> CNot A \<longrightarrow> L # M \<Turnstile>a x \<close> and l: \<open>l \<in> CNot A\<close>
  then have \<open>L # M \<Turnstile>a l\<close> by auto
  then show \<open>M \<Turnstile>a l\<close> using LA l by (cases L) (auto simp: CNot_def)
 qed

lemma true_clss_clss_union_false_true_clss_clss_cnot:
  \<open>A \<union> {B} \<Turnstile>ps {{#}} \<longleftrightarrow> A \<Turnstile>ps CNot B\<close>
  using total_not_CNot consistent_CNot_not unfolding total_over_m_def true_clss_clss_def
  by fastforce

lemma true_annot_remove_hd_if_notin_vars:
  assumes \<open>a # M'\<Turnstile>a D\<close> and \<open>atm_of (lit_of a) \<notin> atms_of D\<close>
  shows \<open>M' \<Turnstile>a D\<close>
  using assms true_cls_remove_hd_if_notin_vars unfolding true_annot_def by auto

lemma true_annot_remove_if_notin_vars:
  assumes \<open>M @ M'\<Turnstile>a D\<close> and \<open>\<forall>x\<in>atms_of D. x \<notin> atm_of ` lits_of_l M\<close>
  shows \<open>M' \<Turnstile>a D\<close>
  using assms by (induct M) (auto dest: true_annot_remove_hd_if_notin_vars)

lemma true_annots_remove_if_notin_vars:
  assumes \<open>M @ M'\<Turnstile>as D\<close> and \<open>\<forall>x\<in>atms_of_ms D. x \<notin> atm_of ` lits_of_l M\<close>
  shows \<open>M' \<Turnstile>as D\<close> unfolding true_annots_def
  using assms unfolding true_annots_def atms_of_ms_def
  by (force dest: true_annot_remove_if_notin_vars)

lemma all_variables_defined_not_imply_cnot:
  assumes
    \<open>\<forall>s \<in> atms_of_ms {B}. s \<in> atm_of ` lits_of_l A\<close> and
    \<open>\<not> A \<Turnstile>a B\<close>
  shows \<open>A \<Turnstile>as CNot B\<close>
  unfolding true_annot_def true_annots_def Ball_def CNot_def true_lit_def
proof (clarify, rule ccontr)
  fix L
  assume LB: \<open>L \<in># B\<close> and L_false: \<open>\<not> lits_of_l A \<Turnstile> {#}\<close> and L_A: \<open>- L \<notin> lits_of_l A\<close>
  then have \<open>atm_of L \<in> atm_of ` lits_of_l A\<close>
    using assms(1) by (simp add: atm_of_lit_in_atms_of lits_of_def)
  then have \<open>L \<in> lits_of_l A \<or> -L \<in> lits_of_l A\<close>
    using atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set by metis
  then have \<open>L \<in> lits_of_l A\<close> using L_A by auto
  then show False
    using LB assms(2) unfolding true_annot_def true_lit_def true_cls_def Bex_def
    by blast
qed

lemma CNot_union_mset[simp]:
  \<open>CNot (A \<union># B) = CNot A \<union> CNot B\<close>
  unfolding CNot_def by auto

lemma true_clss_clss_true_clss_cls_true_clss_clss:
  assumes
    \<open>A \<Turnstile>ps unmark_l M\<close> and \<open>M \<Turnstile>as D\<close>
  shows \<open>A \<Turnstile>ps D\<close>
  by (meson assms total_over_m_union true_annots_true_cls true_annots_true_clss_clss
      true_clss_clss_def true_clss_clss_left_right true_clss_clss_union_and
      true_clss_clss_union_l_r)

lemma true_clss_clss_CNot_true_clss_cls_unsatisfiable:
  assumes \<open>A \<Turnstile>ps CNot D\<close> and \<open>A \<Turnstile>p D\<close>
  shows \<open>unsatisfiable A\<close>
  using assms(2) unfolding true_clss_clss_def true_clss_cls_def satisfiable_def
  by (metis (full_types) Un_absorb Un_empty_right assms(1) atms_of_empty
      atms_of_ms_emtpy_set total_over_m_def total_over_m_insert total_over_m_union
      true_cls_empty true_clss_cls_def true_clss_clss_generalise_true_clss_clss
      true_clss_clss_true_clss_cls true_clss_clss_union_false_true_clss_clss_cnot)

lemma true_clss_cls_neg:
  \<open>N \<Turnstile>p I \<longleftrightarrow> N \<union> (\<lambda>L. {#-L#}) ` set_mset I \<Turnstile>p {#}\<close>
proof -
  have [simp]: \<open>(\<lambda>L. {#- L#}) ` set_mset I = CNot I\<close> for I
    by (auto simp: CNot_def)
  have [iff]: \<open> total_over_m Ia ((\<lambda>L. {#- L#}) ` set_mset I) \<longleftrightarrow>
     total_over_set Ia (atms_of I)\<close> for Ia
    by (auto simp: total_over_m_def
       total_over_set_def atms_of_ms_def atms_of_def)
  show ?thesis
    by (auto simp: true_clss_cls_def consistent_CNot_not
       total_not_CNot)
qed

lemma all_decomposition_implies_conflict_DECO_clause:
  assumes \<open>all_decomposition_implies N (get_all_ann_decomposition M)\<close> and
    \<open>M \<Turnstile>as CNot C\<close> and
    \<open>C \<in> N\<close>
  shows \<open>N \<Turnstile>p (uminus o lit_of) `# (filter_mset is_decided (mset M))\<close>
    (is \<open>?I \<Turnstile>p ?A\<close>)
proof -
  have \<open>{unmark m |m. is_decided m \<and> m \<in> set M} =
       unmark_s {L \<in> set M. is_decided L}\<close>
     by auto
  have \<open>N \<union> unmark_s {L \<in> set M. is_decided L} \<Turnstile>p {#}\<close>
    by (metis (mono_tags, lifting) UnCI
      \<open>{unmark m |m. is_decided m \<and> m \<in> set M} = unmark_s {L \<in> set M. is_decided L}\<close>
      all_decomposition_implies_propagated_lits_are_implied assms
      true_clss_clss_contradiction_true_clss_cls_false true_clss_clss_true_clss_cls_true_clss_clss)
  then show ?thesis
    apply (subst true_clss_cls_neg)
    by (auto simp: image_image)
qed


subsection \<open>Other\<close>

definition \<open>no_dup L \<equiv> distinct (map (\<lambda>l. atm_of (lit_of l)) L)\<close>

lemma no_dup_nil[simp]:
  \<open>no_dup []\<close>
  by (auto simp: no_dup_def)

lemma no_dup_cons[simp]:
  \<open>no_dup (L # M) \<longleftrightarrow> undefined_lit M (lit_of L) \<and> no_dup M\<close>
  by (auto simp: no_dup_def defined_lit_map)

lemma no_dup_append_cons[iff]:
  \<open>no_dup (M @ L # M') \<longleftrightarrow> undefined_lit (M @ M') (lit_of L) \<and> no_dup (M @ M')\<close>
  by (auto simp: no_dup_def defined_lit_map)

lemma no_dup_append_append_cons[iff]:
  \<open>no_dup (M0 @ M @ L # M') \<longleftrightarrow> undefined_lit (M0 @ M @ M') (lit_of L) \<and> no_dup (M0 @ M @ M')\<close>
  by (auto simp: no_dup_def defined_lit_map)

lemma no_dup_rev[simp]:
  \<open>no_dup (rev M) \<longleftrightarrow> no_dup M\<close>
  by (auto simp: rev_map[symmetric] no_dup_def)

lemma no_dup_appendD:
  \<open>no_dup (a @ b) \<Longrightarrow> no_dup b\<close>
  by (auto simp: no_dup_def)

lemma no_dup_appendD1:
  \<open>no_dup (a @ b) \<Longrightarrow> no_dup a\<close>
  by (auto simp: no_dup_def)

lemma no_dup_length_eq_card_atm_of_lits_of_l:
  assumes \<open>no_dup M\<close>
  shows \<open>length M = card (atm_of ` lits_of_l M)\<close>
  using assms unfolding lits_of_def by (induct M) (auto simp add: image_image no_dup_def)

lemma distinct_consistent_interp:
  \<open>no_dup M \<Longrightarrow> consistent_interp (lits_of_l M)\<close>
proof (induct M)
  case Nil
  show ?case by auto
next
  case (Cons L M)
  then have a1: \<open>consistent_interp (lits_of_l M)\<close> by auto
  have \<open>undefined_lit M (lit_of L)\<close>
      using Cons.prems by auto
  then show ?case
    using a1 by simp
qed

lemma same_mset_no_dup_iff:
  \<open>mset M = mset M' \<Longrightarrow> no_dup M \<longleftrightarrow> no_dup M'\<close>
  by (auto simp: no_dup_def same_mset_distinct_iff)

lemma distinct_get_all_ann_decomposition_no_dup:
  assumes \<open>(a, b) \<in> set (get_all_ann_decomposition M)\<close>
  and \<open>no_dup M\<close>
  shows \<open>no_dup (a @ b)\<close>
  using assms by (force simp: no_dup_def)

lemma true_annots_lit_of_notin_skip:
  assumes \<open>L # M \<Turnstile>as CNot A\<close>
  and \<open>-lit_of L \<notin># A\<close>
  and \<open>no_dup (L # M)\<close>
  shows \<open>M \<Turnstile>as CNot A\<close>
proof -
  have \<open>\<forall>l \<in># A. -l \<in> lits_of_l (L # M)\<close>
    using assms(1) in_CNot_implies_uminus(2) by blast
  moreover {
    have \<open>undefined_lit M (lit_of L)\<close>
      using assms(3) by force
    then have \<open>- lit_of L \<notin> lits_of_l M\<close>
      by (simp add: Decided_Propagated_in_iff_in_lits_of_l) }
  ultimately have \<open>\<forall> l \<in># A. -l \<in> lits_of_l M\<close>
    using assms(2) by (metis insert_iff list.simps(15) lits_of_insert uminus_of_uminus_id)
  then show ?thesis by (auto simp add: true_annots_def)
qed

lemma no_dup_imp_distinct: \<open>no_dup M \<Longrightarrow> distinct M\<close>
  by (induction M) (auto simp: defined_lit_map)

lemma no_dup_tlD: \<open>no_dup a \<Longrightarrow> no_dup (tl a)\<close>
  unfolding no_dup_def by (cases a) auto

lemma defined_lit_no_dupD:
  \<open>defined_lit M1 L \<Longrightarrow> no_dup (M2 @ M1) \<Longrightarrow> undefined_lit M2 L\<close>
  \<open>defined_lit M1 L \<Longrightarrow> no_dup (M2' @ M2 @ M1) \<Longrightarrow> undefined_lit M2' L\<close>
  \<open>defined_lit M1 L \<Longrightarrow> no_dup (M2' @ M2 @ M1) \<Longrightarrow> undefined_lit M2 L\<close>
  by (auto simp: defined_lit_map no_dup_def)

lemma no_dup_consistentD:
  \<open>no_dup M \<Longrightarrow> L \<in> lits_of_l M \<Longrightarrow> -L \<notin> lits_of_l M\<close>
  using consistent_interp_def distinct_consistent_interp by blast

lemma no_dup_not_tautology: \<open>no_dup M \<Longrightarrow> \<not>tautology (image_mset lit_of (mset M))\<close>
  by (induction M) (auto simp: tautology_add_mset uminus_lit_swap defined_lit_def
      dest: atm_imp_decided_or_proped)

lemma no_dup_distinct: \<open>no_dup M \<Longrightarrow> distinct_mset (image_mset lit_of (mset M))\<close>
  by (induction M) (auto simp: uminus_lit_swap defined_lit_def
      dest: atm_imp_decided_or_proped)

lemma no_dup_not_tautology_uminus: \<open>no_dup M \<Longrightarrow> \<not>tautology {#-lit_of L. L \<in># mset M#}\<close>
  by (induction M) (auto simp: tautology_add_mset uminus_lit_swap defined_lit_def
      dest: atm_imp_decided_or_proped)

lemma no_dup_distinct_uminus: \<open>no_dup M \<Longrightarrow> distinct_mset {#-lit_of L. L \<in># mset M#}\<close>
  by (induction M) (auto simp: uminus_lit_swap defined_lit_def
      dest: atm_imp_decided_or_proped)

lemma no_dup_map_lit_of: \<open>no_dup M \<Longrightarrow> distinct (map lit_of M)\<close>
  apply (induction M)
   apply (auto simp: dest: no_dup_imp_distinct)
  by (meson distinct.simps(2) no_dup_cons no_dup_imp_distinct)

lemma no_dup_alt_def:
  \<open>no_dup M \<longleftrightarrow> distinct_mset {#atm_of (lit_of x). x \<in># mset M#}\<close>
  by (auto simp: no_dup_def simp flip: distinct_mset_mset_distinct)

lemma no_dup_append_in_atm_notin:
   assumes \<open>no_dup (M @ M')\<close> and \<open>L \<in> lits_of_l M'\<close>
     shows \<open>undefined_lit M L\<close>
  using assms by (auto simp add: atm_lit_of_set_lits_of_l no_dup_def
      defined_lit_map)

lemma no_dup_uminus_append_in_atm_notin:
   assumes \<open>no_dup (M @ M')\<close> and \<open>-L \<in> lits_of_l M'\<close>
     shows \<open>undefined_lit M L\<close>
  using Decided_Propagated_in_iff_in_lits_of_l assms defined_lit_no_dupD(1) by blast


subsection \<open>Extending Entailments to multisets\<close>

text \<open>We have defined previous entailment with respect to sets, but we also need a multiset version
  depending on the context. The conversion is simple using the function @{term set_mset} (in this
  direction, there is no loss of information).\<close>
abbreviation true_annots_mset (infix "\<Turnstile>asm" 50) where
\<open>I \<Turnstile>asm C \<equiv> I \<Turnstile>as (set_mset C)\<close>

abbreviation true_clss_clss_m :: \<open>'v clause multiset \<Rightarrow> 'v clause multiset \<Rightarrow> bool\<close> (infix "\<Turnstile>psm" 50)
  where
\<open>I \<Turnstile>psm C \<equiv> set_mset I \<Turnstile>ps (set_mset C)\<close>

text \<open>Analog of theorem @{thm [source] true_clss_clss_subsetE}\<close>
lemma true_clss_clssm_subsetE: \<open>N \<Turnstile>psm B \<Longrightarrow> A \<subseteq># B \<Longrightarrow> N \<Turnstile>psm A\<close>
  using set_mset_mono true_clss_clss_subsetE by blast

abbreviation true_clss_cls_m:: \<open>'a clause multiset \<Rightarrow> 'a clause \<Rightarrow> bool\<close> (infix "\<Turnstile>pm" 50) where
\<open>I \<Turnstile>pm C \<equiv> set_mset I \<Turnstile>p C\<close>

abbreviation distinct_mset_mset :: \<open>'a multiset multiset \<Rightarrow> bool\<close> where
\<open>distinct_mset_mset \<Sigma> \<equiv> distinct_mset_set (set_mset \<Sigma>)\<close>

abbreviation all_decomposition_implies_m where
\<open>all_decomposition_implies_m A B \<equiv> all_decomposition_implies (set_mset A) B\<close>

abbreviation atms_of_mm :: \<open>'a clause multiset \<Rightarrow> 'a set\<close> where
\<open>atms_of_mm U \<equiv> atms_of_ms (set_mset U)\<close>

text \<open>Other definition using @{term \<open>Union_mset\<close>}\<close>
lemma \<open>atms_of_mm U \<equiv> set_mset (\<Union># image_mset (image_mset atm_of) U)\<close>
  unfolding atms_of_ms_def by (auto simp: atms_of_def)

abbreviation true_clss_m:: \<open>'a partial_interp \<Rightarrow> 'a clause multiset \<Rightarrow> bool\<close> (infix "\<Turnstile>sm" 50) where
\<open>I \<Turnstile>sm C \<equiv> I \<Turnstile>s set_mset C\<close>

abbreviation true_clss_ext_m (infix "\<Turnstile>sextm" 49) where
\<open>I \<Turnstile>sextm C \<equiv> I \<Turnstile>sext set_mset C\<close>

lemma true_clss_cls_cong_set_mset:
  \<open>N \<Turnstile>pm D \<Longrightarrow> set_mset D = set_mset D' \<Longrightarrow> N \<Turnstile>pm D'\<close>
  by (auto simp add: true_clss_cls_def true_cls_def atms_of_cong_set_mset[of D D'])


subsection \<open>More Lemmas\<close>

lemma no_dup_cannot_not_lit_and_uminus:
  \<open>no_dup M \<Longrightarrow> - lit_of xa = lit_of x \<Longrightarrow> x \<in> set M \<Longrightarrow> xa \<notin> set M\<close>
  by (metis atm_of_uminus distinct_map inj_on_eq_iff uminus_not_id' no_dup_def)

lemma atms_of_ms_single_atm_of[simp]:
  \<open>atms_of_ms {unmark L |L. P L} = atm_of ` {lit_of L |L. P L}\<close>
  unfolding atms_of_ms_def by force

lemma true_cls_mset_restrict:
  \<open>{L \<in> I. atm_of L \<in> atms_of_mm N} \<Turnstile>m N \<longleftrightarrow> I \<Turnstile>m N\<close>
  by (auto simp: true_cls_mset_def true_cls_def
    dest!: multi_member_split)

lemma true_clss_restrict:
  \<open>{L \<in> I. atm_of L \<in> atms_of_mm N} \<Turnstile>sm N \<longleftrightarrow> I \<Turnstile>sm N\<close>
  by (auto simp: true_clss_def true_cls_def
    dest!: multi_member_split)


lemma true_clss_restrict_iff:
  assumes \<open>\<not>tautology \<chi>\<close>
  shows \<open>N \<Turnstile>p \<chi> \<longleftrightarrow> N \<Turnstile>p {#L \<in># \<chi>. atm_of L \<in> atms_of_ms N#}\<close> (is \<open>?A \<longleftrightarrow> ?B\<close>)
  apply (subst true_clss_alt_def2[OF assms])
  apply (subst true_clss_alt_def2)
  subgoal using not_tautology_mono[OF _ assms] by (auto dest: not_tautology_minus)
  apply (rule HOL.iff_allI)
  apply (auto 5 5 simp: true_cls_def atms_of_s_def dest!: multi_member_split)
  done


subsection \<open>Negation of annotated clauses\<close>

definition negate_ann_lits :: \<open>('v, 'v clause) ann_lits \<Rightarrow> 'v literal multiset\<close> where
  \<open>negate_ann_lits M = (\<lambda>L. - lit_of L) `# mset M\<close>

lemma negate_ann_lits_empty[simp]: \<open>negate_ann_lits [] = {#}\<close>
  by (auto simp: negate_ann_lits_def)

lemma entails_CNot_negate_ann_lits:
  \<open>M \<Turnstile>as CNot D \<longleftrightarrow> set_mset D \<subseteq> set_mset (negate_ann_lits M)\<close>
  by (auto simp: true_annots_true_cls_def_iff_negation_in_model
      negate_ann_lits_def lits_of_def uminus_lit_swap
    dest!: multi_member_split)

text \<open>Pointwise negation of a clause:\<close>
definition pNeg :: \<open>'v clause \<Rightarrow> 'v clause\<close> where
  \<open>pNeg C = {#-D. D \<in># C#}\<close>

lemma pNeg_simps:
  \<open>pNeg (add_mset A C) = add_mset (-A) (pNeg C)\<close>
  \<open>pNeg (C + D) = pNeg C + pNeg D\<close>
  by (auto simp: pNeg_def)

lemma atms_of_pNeg[simp]: \<open>atms_of (pNeg C) = atms_of C\<close>
  by (auto simp: pNeg_def atms_of_def image_image)

lemma negate_ann_lits_pNeg_lit_of: \<open>negate_ann_lits = pNeg o image_mset lit_of o mset\<close>
  by (intro ext) (auto simp: negate_ann_lits_def pNeg_def)

lemma negate_ann_lits_empty_iff: \<open>negate_ann_lits M \<noteq> {#} \<longleftrightarrow> M \<noteq> []\<close>
  by (auto simp: negate_ann_lits_def)

lemma atms_of_negate_ann_lits[simp]: \<open>atms_of (negate_ann_lits M) = atm_of ` (lits_of_l M)\<close>
  unfolding negate_ann_lits_def lits_of_def atms_of_def by (auto simp: image_image)

lemma tautology_pNeg[simp]:
  \<open>tautology (pNeg C) \<longleftrightarrow> tautology C\<close>
  by (auto 5 5 simp: tautology_decomp pNeg_def
      uminus_lit_swap add_mset_eq_add_mset eq_commute[of \<open>Neg _\<close> \<open>- _\<close>] eq_commute[of \<open>Pos _\<close> \<open>- _\<close>]
    dest!: multi_member_split)

lemma pNeg_convolution[simp]:
  \<open>pNeg (pNeg C) = C\<close>
  by (auto simp: pNeg_def)

lemma pNeg_minus[simp]: \<open>pNeg (A - B) = pNeg A - pNeg B\<close>
  unfolding pNeg_def
  by (subst image_mset_minus_inj_on) (auto simp: inj_on_def)

lemma pNeg_empty[simp]: \<open>pNeg {#} = {#}\<close>
  unfolding pNeg_def
  by (auto simp: inj_on_def)

lemma pNeg_replicate_mset[simp]: \<open>pNeg (replicate_mset n L) = replicate_mset n (-L)\<close>
  unfolding pNeg_def by auto

lemma distinct_mset_pNeg_iff[iff]: \<open>distinct_mset (pNeg x) \<longleftrightarrow> distinct_mset x\<close>
  unfolding pNeg_def
  by (rule distinct_image_mset_inj) (auto simp: inj_on_def)

lemma pNeg_simple_clss_iff[simp]:
  \<open>pNeg M \<in> simple_clss N \<longleftrightarrow> M \<in> simple_clss N\<close>
  by (auto simp: simple_clss_def)


definition DECO_clause :: \<open>('v, 'a) ann_lits \<Rightarrow> 'v clause\<close> where
  \<open>DECO_clause M = (uminus o lit_of) `# (filter_mset is_decided (mset M))\<close>

lemma
  DECO_clause_cons_Decide[simp]:
    \<open>DECO_clause (Decided L # M) = add_mset (-L) (DECO_clause M)\<close> and
  DECO_clause_cons_Proped[simp]:
    \<open>DECO_clause (Propagated L C # M) = DECO_clause M\<close>
  by (auto simp: DECO_clause_def)

end
