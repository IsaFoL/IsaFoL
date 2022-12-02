theory Initial_Literals_Generalize_Learned_Literals
  imports Simple_Clause_Learning
begin

syntax (input)
  "_fBall"       :: "pttrn \<Rightarrow> 'a fset \<Rightarrow> bool \<Rightarrow> bool"      ("(3! (_/|:|_)./ _)" [0, 0, 10] 10)
  "_fBex"        :: "pttrn \<Rightarrow> 'a fset \<Rightarrow> bool \<Rightarrow> bool"      ("(3? (_/|:|_)./ _)" [0, 0, 10] 10)

syntax
  "_fBall"       :: "pttrn \<Rightarrow> 'a fset \<Rightarrow> bool \<Rightarrow> bool"      ("(3\<forall>(_/|\<in>|_)./ _)" [0, 0, 10] 10)
  "_fBex"        :: "pttrn \<Rightarrow> 'a fset \<Rightarrow> bool \<Rightarrow> bool"      ("(3\<exists>(_/|\<in>|_)./ _)" [0, 0, 10] 10)

translations
  "\<forall>x|\<in>|A. P" \<rightleftharpoons> "CONST fBall A (\<lambda>x. P)"
  "\<exists>x|\<in>|A. P" \<rightleftharpoons> "CONST fBex A (\<lambda>x. P)"

print_translation \<open>
 [Syntax_Trans.preserve_binder_abs2_tr' \<^const_syntax>\<open>fBall\<close> \<^syntax_const>\<open>_fBall\<close>,
  Syntax_Trans.preserve_binder_abs2_tr' \<^const_syntax>\<open>fBex\<close> \<^syntax_const>\<open>_fBex\<close>]
\<close> \<comment> \<open>to avoid eta-contraction of body\<close>

global_interpretation comp_finsert_commute: comp_fun_commute finsert
proof (unfold_locales)
  show "\<And>y x. finsert y \<circ> finsert x = finsert x \<circ> finsert y"
    by auto
qed

definition fset_mset :: "'a multiset \<Rightarrow> 'a fset"
  where "fset_mset = fold_mset finsert {||}"

lemma fset_mset_mempty[simp]: "fset_mset {#} = {||}"
  by (simp add: fset_mset_def)

lemma fset_mset_add_mset[simp]: "fset_mset (add_mset x M) = finsert x (fset_mset M)"
  by (simp add: fset_mset_def)

lemma fset_fset_mset[simp]: "fset (fset_mset M) = set_mset M"
  by (induction M rule: multiset_induct) simp_all

lemma fmember_fset_mset_iff[simp]: "x |\<in>| fset_mset M \<longleftrightarrow> x \<in># M"
  by (induction M rule: multiset_induct) simp_all

lemma fBall_fset_mset_iff[simp]: "(\<forall>x |\<in>| fset_mset M. P x) \<longleftrightarrow> (\<forall>x \<in># M. P x)"
  by (simp add: fBall_def)

lemma fBex_fset_mset_iff[simp]: "(\<exists>x |\<in>| fset_mset M. P x) \<longleftrightarrow> (\<exists>x \<in># M. P x)"
  by (simp add: fBex_def)

lemma fmember_ffUnion_iff: "a |\<in>| ffUnion (f |`| A) \<longleftrightarrow> (\<exists>x |\<in>| A. a |\<in>| f x)"
  unfolding fmember.rep_eq ffUnion.rep_eq fBex.rep_eq by simp

lemma fBex_ffUnion_iff: "(\<exists>z |\<in>| ffUnion (f |`| A). P z) \<longleftrightarrow> (\<exists>x |\<in>| A. \<exists>z |\<in>| f x. P z)"
  unfolding fBex.rep_eq ffUnion.rep_eq fimage.rep_eq by blast

lemma fBall_ffUnion_iff: "(\<forall>z |\<in>| ffUnion (f |`| A). P z) \<longleftrightarrow> (\<forall>x |\<in>| A. \<forall>z |\<in>| f x. P z)"
  unfolding fBall.rep_eq ffUnion.rep_eq fimage.rep_eq by blast


abbreviation grounding_lits_of_clss where
  "grounding_lits_of_clss N \<equiv> {L \<cdot>l \<gamma> | L \<gamma>. L \<in> \<Union>(set_mset ` N) \<and> is_ground_lit (L \<cdot>l \<gamma>)}"

context scl begin

corollary
  assumes "initial_lits_generalize_learned_trail_conflict N S"
  shows "grounding_lits_of_clss (fset (state_learned S)) \<subseteq> grounding_lits_of_clss (fset N)"
  (is "?lhs \<subseteq> ?rhs")
proof (rule subsetI)
  from assms(1) have N_lits_sup: "clss_lits_generalize_clss_lits (fset N) (fset (state_learned S))"
    unfolding initial_lits_generalize_learned_trail_conflict_def
    using clss_lits_generalize_clss_lits_subset by auto

  fix L
  assume "L \<in> ?lhs"
  then obtain L' \<gamma> where
    L_def: "L = L' \<cdot>l \<gamma>" and
    "L' \<in> \<Union> (set_mset ` fset (state_learned S))" and
    "is_ground_lit (L' \<cdot>l \<gamma>)"
    by auto
  then obtain L\<^sub>N \<sigma>\<^sub>N where "L\<^sub>N \<in> \<Union>(set_mset ` fset N)" and "L\<^sub>N \<cdot>l \<sigma>\<^sub>N = L'"
    using N_lits_sup[unfolded clss_lits_generalize_clss_lits_def]
    unfolding fBex_ffUnion_iff fBall_ffUnion_iff fBex_fset_mset_iff fBall_fset_mset_iff
      generalizes_lit_def by meson
  then show "L \<in> ?rhs"
    unfolding mem_Collect_eq
    using \<open>is_ground_lit (L' \<cdot>l \<gamma>)\<close>
    unfolding L_def \<open>L\<^sub>N \<cdot>l \<sigma>\<^sub>N = L'\<close>[symmetric]
    by (metis subst_lit_comp_subst)
qed

end

end