theory Watched_Literals_All_Literals
imports Watched_Literals_Clauses
begin

chapter \<open>Set of all literals\<close>

type_synonym ann_lits_l = \<open>(nat, nat) ann_lits\<close>
type_synonym clauses_to_update_ll = \<open>nat list\<close>


section \<open>Refinement\<close>

subsection \<open>Set of all literals of the problem\<close>

definition all_lits_of_mm :: \<open>'a clauses \<Rightarrow> 'a literal multiset\<close> where
\<open>all_lits_of_mm Ls = Pos `# (atm_of `# (\<Union># Ls)) + Neg `# (atm_of `# (\<Union># Ls))\<close>

lemma all_lits_of_mm_empty[simp]: \<open>all_lits_of_mm {#} = {#}\<close>
  by (auto simp: all_lits_of_mm_def)
lemma in_all_lits_of_mm_ain_atms_of_iff:
  \<open>L \<in># all_lits_of_mm N \<longleftrightarrow> atm_of L \<in> atms_of_mm N\<close>
  by (cases L) (auto simp: all_lits_of_mm_def atms_of_ms_def atms_of_def)

lemma all_lits_of_mm_union:
  \<open>all_lits_of_mm (M + N) = all_lits_of_mm M + all_lits_of_mm N\<close>
  unfolding all_lits_of_mm_def by auto

definition all_lits_of_m :: \<open>'a clause \<Rightarrow> 'a literal multiset\<close> where
  \<open>all_lits_of_m Ls = Pos `# (atm_of `# Ls) + Neg `# (atm_of `# Ls)\<close>

lemma all_lits_of_m_empty[simp]: \<open>all_lits_of_m {#} = {#}\<close>
  by (auto simp: all_lits_of_m_def)

lemma all_lits_of_m_empty_iff[iff]: \<open>all_lits_of_m A = {#} \<longleftrightarrow> A = {#}\<close>
  by (cases A) (auto simp: all_lits_of_m_def)

lemma in_all_lits_of_m_ain_atms_of_iff: \<open>L \<in># all_lits_of_m N \<longleftrightarrow> atm_of L \<in> atms_of N\<close>
  by (cases L) (auto simp: all_lits_of_m_def atms_of_ms_def atms_of_def)

lemma in_clause_in_all_lits_of_m: \<open>x \<in># C \<Longrightarrow> x \<in># all_lits_of_m C\<close>
  using atm_of_lit_in_atms_of in_all_lits_of_m_ain_atms_of_iff by blast

lemma all_lits_of_mm_add_mset:
  \<open>all_lits_of_mm (add_mset C N) = (all_lits_of_m C) + (all_lits_of_mm N)\<close>
  by (auto simp: all_lits_of_mm_def all_lits_of_m_def)

lemma all_lits_of_m_add_mset:
  \<open>all_lits_of_m (add_mset L C) = add_mset L (add_mset (-L) (all_lits_of_m C))\<close>
  by (cases L) (auto simp: all_lits_of_m_def)

lemma all_lits_of_m_union:
  \<open>all_lits_of_m (A + B) = all_lits_of_m A + all_lits_of_m B\<close>
  by (auto simp: all_lits_of_m_def)

lemma all_lits_of_m_mono:
  \<open>D \<subseteq># D' \<Longrightarrow> all_lits_of_m D \<subseteq># all_lits_of_m D'\<close>
  by (auto elim!: mset_le_addE simp: all_lits_of_m_union)

lemma all_lits_of_m_diffD: \<open>x \<in># all_lits_of_m (D - D') \<Longrightarrow> x \<in># all_lits_of_m D\<close>
  by (auto simp: all_lits_of_m_def dest: in_diffD)


lemma in_all_lits_of_mm_uminusD: \<open>x2 \<in># all_lits_of_mm N \<Longrightarrow> -x2 \<in># all_lits_of_mm N\<close>
  by (auto simp: all_lits_of_mm_def)

lemma in_all_lits_of_mm_uminus_iff: \<open>-x2 \<in># all_lits_of_mm N \<longleftrightarrow> x2 \<in># all_lits_of_mm N\<close>
  by (cases x2) (auto simp: all_lits_of_mm_def)

lemma all_lits_of_mm_diffD:
  \<open>L \<in># all_lits_of_mm (A - B) \<Longrightarrow> L \<in># all_lits_of_mm A\<close>
  apply (induction A arbitrary: B)
  subgoal by auto
  subgoal for a A' B
    by (cases \<open>a \<in># B\<close>)
      (fastforce dest!: multi_member_split[of a B] simp: all_lits_of_mm_add_mset)+
  done

lemma all_lits_of_mm_mono:
  \<open>set_mset A \<subseteq> set_mset B \<Longrightarrow> set_mset (all_lits_of_mm A) \<subseteq> set_mset (all_lits_of_mm B)\<close>
  by (auto simp: all_lits_of_mm_def)


section \<open>Conversion from set of atoms to set of literals\<close>

text \<open>We start in a context where we have an initial set of atoms. We later extend the locale to
  include a bound on the largest atom (in order to generate more efficient code).
\<close>
context
  fixes \<A>\<^sub>i\<^sub>n :: \<open>'v multiset\<close>
begin

text \<open>This is the \<^emph>\<open>completion\<close> of \<^term>\<open>\<A>\<^sub>i\<^sub>n\<close>, containing the positive and the negation of every
  literal of \<^term>\<open>\<A>\<^sub>i\<^sub>n\<close>:\<close>
definition \<L>\<^sub>a\<^sub>l\<^sub>l where \<open>\<L>\<^sub>a\<^sub>l\<^sub>l = poss \<A>\<^sub>i\<^sub>n + negs \<A>\<^sub>i\<^sub>n\<close>

lemma atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n: \<open>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l = set_mset \<A>\<^sub>i\<^sub>n\<close>
  unfolding \<L>\<^sub>a\<^sub>l\<^sub>l_def by (auto simp: atms_of_def image_Un image_image)

definition is_\<L>\<^sub>a\<^sub>l\<^sub>l :: \<open>'v literal multiset \<Rightarrow> bool\<close> where
  \<open>is_\<L>\<^sub>a\<^sub>l\<^sub>l S \<longleftrightarrow> set_mset \<L>\<^sub>a\<^sub>l\<^sub>l = set_mset S\<close>

definition literals_are_in_\<L>\<^sub>i\<^sub>n :: \<open>'v clause \<Rightarrow> bool\<close> where
  \<open>literals_are_in_\<L>\<^sub>i\<^sub>n C \<longleftrightarrow> set_mset (all_lits_of_m C) \<subseteq> set_mset \<L>\<^sub>a\<^sub>l\<^sub>l\<close>

lemma literals_are_in_\<L>\<^sub>i\<^sub>n_empty[simp]: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n {#}\<close>
  by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_def)

lemma in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff: \<open>x \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<longleftrightarrow> atm_of x \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
  by (cases x) (auto simp: \<L>\<^sub>a\<^sub>l\<^sub>l_def atms_of_def atm_of_eq_atm_of image_Un image_image)

lemma literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset:
  \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (add_mset L A) \<longleftrightarrow> literals_are_in_\<L>\<^sub>i\<^sub>n A \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
  by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_def all_lits_of_m_add_mset in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)

lemma literals_are_in_\<L>\<^sub>i\<^sub>n_mono:
  assumes N: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n D'\<close> and D: \<open>D \<subseteq># D'\<close>
  shows \<open>literals_are_in_\<L>\<^sub>i\<^sub>n D\<close>
proof -
  have \<open>set_mset (all_lits_of_m D) \<subseteq> set_mset (all_lits_of_m D')\<close>
    using D by (auto simp: in_all_lits_of_m_ain_atms_of_iff atm_iff_pos_or_neg_lit)
  then show ?thesis
     using N unfolding literals_are_in_\<L>\<^sub>i\<^sub>n_def by fast
qed

lemma literals_are_in_\<L>\<^sub>i\<^sub>n_sub:
  \<open>literals_are_in_\<L>\<^sub>i\<^sub>n y \<Longrightarrow> literals_are_in_\<L>\<^sub>i\<^sub>n (y - z)\<close>
  using literals_are_in_\<L>\<^sub>i\<^sub>n_mono[of y \<open>y - z\<close>] by auto

lemma all_lits_of_m_subset_all_lits_of_mmD:
  \<open>a \<in># b \<Longrightarrow> set_mset (all_lits_of_m a) \<subseteq> set_mset (all_lits_of_mm b)\<close>
  by (auto simp: all_lits_of_m_def all_lits_of_mm_def)

lemma all_lits_of_m_remdups_mset:
  \<open>set_mset (all_lits_of_m (remdups_mset N)) = set_mset (all_lits_of_m N)\<close>
  by (auto simp: all_lits_of_m_def)

lemma literals_are_in_\<L>\<^sub>i\<^sub>n_remdups[simp]:
  \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (remdups_mset N) = literals_are_in_\<L>\<^sub>i\<^sub>n N\<close>
  by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_def all_lits_of_m_remdups_mset)

lemma uminus_\<A>\<^sub>i\<^sub>n_iff: \<open>- L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<longleftrightarrow> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
  by (simp add: in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)

definition literals_are_in_\<L>\<^sub>i\<^sub>n_mm :: \<open>'v clauses \<Rightarrow> bool\<close> where
  \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_mm C \<longleftrightarrow> set_mset (all_lits_of_mm C) \<subseteq> set_mset \<L>\<^sub>a\<^sub>l\<^sub>l\<close>

lemma literals_are_in_\<L>\<^sub>i\<^sub>n_mm_add_msetD:
  \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_mm (add_mset C N) \<Longrightarrow> L \<in># C \<Longrightarrow> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
  by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_mm_def all_lits_of_mm_add_mset
      all_lits_of_m_add_mset
    dest!: multi_member_split)

lemma literals_are_in_\<L>\<^sub>i\<^sub>n_mm_add_mset:
  \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_mm (add_mset C N) \<longleftrightarrow>
    literals_are_in_\<L>\<^sub>i\<^sub>n_mm N \<and> literals_are_in_\<L>\<^sub>i\<^sub>n C\<close>
  unfolding literals_are_in_\<L>\<^sub>i\<^sub>n_mm_def  literals_are_in_\<L>\<^sub>i\<^sub>n_def
  by (auto simp: all_lits_of_mm_add_mset)

definition literals_are_in_\<L>\<^sub>i\<^sub>n_trail :: \<open>('v, 'mark) ann_lits \<Rightarrow> bool\<close> where
  \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail M \<longleftrightarrow> set_mset (lit_of `# mset M) \<subseteq> set_mset \<L>\<^sub>a\<^sub>l\<^sub>l\<close>

lemma literals_are_in_\<L>\<^sub>i\<^sub>n_trail_in_lits_of_l:
  \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail M \<Longrightarrow> a \<in> lits_of_l M \<Longrightarrow> a \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
  by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_def lits_of_def)

lemma literals_are_in_\<L>\<^sub>i\<^sub>n_trail_uminus_in_lits_of_l:
  \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail M \<Longrightarrow> -a \<in> lits_of_l M \<Longrightarrow> a \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
  by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_def lits_of_def uminus_lit_swap uminus_\<A>\<^sub>i\<^sub>n_iff)

lemma literals_are_in_\<L>\<^sub>i\<^sub>n_trail_uminus_in_lits_of_l_atms:
  \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail M \<Longrightarrow> -a \<in> lits_of_l M \<Longrightarrow> atm_of a \<in># \<A>\<^sub>i\<^sub>n\<close>
  using literals_are_in_\<L>\<^sub>i\<^sub>n_trail_uminus_in_lits_of_l[of M a]
  unfolding in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff[symmetric] atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n[symmetric]
  .
end

lemma isasat_input_ops_\<L>\<^sub>a\<^sub>l\<^sub>l_empty[simp]:
  \<open>\<L>\<^sub>a\<^sub>l\<^sub>l {#} = {#}\<close>
  unfolding \<L>\<^sub>a\<^sub>l\<^sub>l_def
  by auto

lemma \<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_all_lits_of_mm: \<open>set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (atm_of `#  all_lits_of_mm A)) = set_mset (all_lits_of_mm A)\<close>
  apply (auto simp: \<L>\<^sub>a\<^sub>l\<^sub>l_def in_all_lits_of_mm_ain_atms_of_iff)
  by (metis (no_types, lifting) image_iff in_all_lits_of_mm_ain_atms_of_iff literal.exhaust_sel)


definition all_lits :: \<open>('a, 'v literal list \<times> 'b) fmap \<Rightarrow> 'v literal multiset multiset \<Rightarrow>
   'v literal multiset\<close> where
  \<open>all_lits S NUE = all_lits_of_mm ((\<lambda>C. mset (fst C)) `# ran_m S + NUE)\<close>

lemma all_lits_alt_def:
  \<open>all_lits S NUE = all_lits_of_mm (mset `# ran_mf S + NUE)\<close>
  unfolding all_lits_def
  by auto

lemma all_lits_alt_def2:
  \<open>all_lits S (NUE + NUS) = all_lits_of_mm (mset `# ran_mf S + NUE + NUS)\<close>
  \<open>all_lits S (NUE + NUS) = all_lits_of_mm ((\<lambda>C. mset (fst C)) `# ran_m S + NUE + NUS)\<close>
  unfolding all_lits_def
  by (auto simp: ac_simps)

lemma literals_are_in_\<L>\<^sub>i\<^sub>n_mm_in_\<L>\<^sub>a\<^sub>l\<^sub>l:
  assumes
    N1: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_mm \<A> (mset `# ran_mf xs)\<close> and
    i_xs: \<open>i \<in># dom_m xs\<close> and j_xs: \<open>j < length (xs \<propto> i)\<close>
  shows \<open>xs \<propto> i ! j \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close>
proof -
  have \<open>xs \<propto> i \<in># ran_mf xs\<close>
    using i_xs by auto
  then have \<open>xs \<propto> i ! j \<in> set_mset (all_lits_of_mm (mset `# ran_mf xs))\<close>
    using j_xs by (auto simp: in_all_lits_of_mm_ain_atms_of_iff atms_of_ms_def Bex_def
      intro!: exI[of _ \<open>xs \<propto> i\<close>])
  then show ?thesis
    using N1 unfolding literals_are_in_\<L>\<^sub>i\<^sub>n_mm_def by blast
qed


lemma literals_are_in_\<L>\<^sub>i\<^sub>n_trail_in_lits_of_l_atms:
  \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail \<A>\<^sub>i\<^sub>n M \<Longrightarrow> a \<in> lits_of_l M \<Longrightarrow> atm_of a \<in># \<A>\<^sub>i\<^sub>n\<close>
  using literals_are_in_\<L>\<^sub>i\<^sub>n_trail_in_lits_of_l[of \<A>\<^sub>i\<^sub>n M a]
  unfolding in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff[symmetric] atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n[symmetric]
  .

lemma literals_are_in_\<L>\<^sub>i\<^sub>n_trail_Cons:
  \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail \<A>\<^sub>i\<^sub>n (L # M) \<longleftrightarrow>
      literals_are_in_\<L>\<^sub>i\<^sub>n_trail \<A>\<^sub>i\<^sub>n M \<and> lit_of L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<^sub>i\<^sub>n\<close>
  by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_def)

lemma literals_are_in_\<L>\<^sub>i\<^sub>n_trail_empty[simp]:
  \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail \<A> []\<close>
  by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_def)

lemma literals_are_in_\<L>\<^sub>i\<^sub>n_trail_lit_of_mset:
  \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail \<A> M = literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (lit_of `# mset M)\<close>
  by (induction M) (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset literals_are_in_\<L>\<^sub>i\<^sub>n_trail_Cons)

lemma literals_are_in_\<L>\<^sub>i\<^sub>n_in_mset_\<L>\<^sub>a\<^sub>l\<^sub>l:
  \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A> C \<Longrightarrow> L \<in># C \<Longrightarrow> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close>
  unfolding literals_are_in_\<L>\<^sub>i\<^sub>n_def
  by (auto dest!: multi_member_split simp: all_lits_of_m_add_mset)

lemma literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l:
  assumes
    N1: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (mset xs)\<close> and
    i_xs: \<open>i < length xs\<close>
  shows \<open>xs ! i \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close>
  using literals_are_in_\<L>\<^sub>i\<^sub>n_in_mset_\<L>\<^sub>a\<^sub>l\<^sub>l[of \<A> \<open>mset xs\<close> \<open>xs!i\<close>] assms by auto

lemma is_\<L>\<^sub>a\<^sub>l\<^sub>l_\<L>\<^sub>a\<^sub>l\<^sub>l_rewrite[simp]:
  \<open>is_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> (all_lits_of_mm \<A>') \<Longrightarrow>
    set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (atm_of `# all_lits_of_mm \<A>')) = set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close>
  using in_all_lits_of_mm_ain_atms_of_iff
  unfolding set_mset_set_mset_eq_iff is_\<L>\<^sub>a\<^sub>l\<^sub>l_def Ball_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
    in_all_lits_of_mm_ain_atms_of_iff atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n
  by (auto simp: in_all_lits_of_mm_ain_atms_of_iff)

lemma is_\<L>\<^sub>a\<^sub>l\<^sub>l_alt_def: \<open>is_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> (all_lits_of_mm A) \<longleftrightarrow> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>) = atms_of_mm A\<close>
  unfolding set_mset_set_mset_eq_iff is_\<L>\<^sub>a\<^sub>l\<^sub>l_def Ball_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
    in_all_lits_of_mm_ain_atms_of_iff
  by auto (metis literal.sel(2))+

lemma in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n: \<open>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<^sub>i\<^sub>n \<longleftrightarrow> atm_of L \<in># \<A>\<^sub>i\<^sub>n\<close>
  by (cases L) (auto simp: \<L>\<^sub>a\<^sub>l\<^sub>l_def)

lemma literals_are_in_\<L>\<^sub>i\<^sub>n_alt_def:
  \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A> S \<longleftrightarrow> atms_of S \<subseteq> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close>
  apply (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_def all_lits_of_mm_union lits_of_def
       in_all_lits_of_m_ain_atms_of_iff in_all_lits_of_mm_ain_atms_of_iff atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n
       atm_of_eq_atm_of uminus_\<A>\<^sub>i\<^sub>n_iff subset_iff in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n)
  apply (auto simp: atms_of_def)
  done

lemma literals_are_in_\<L>\<^sub>i\<^sub>n_trail_atm_of:
  \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail \<A>\<^sub>i\<^sub>n M \<longleftrightarrow> atm_of ` lits_of_l M \<subseteq> set_mset \<A>\<^sub>i\<^sub>n\<close>
  apply (rule iffI)
  subgoal by (auto dest: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_in_lits_of_l_atms)
  subgoal by (fastforce simp: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_def lits_of_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n)
  done

lemma literals_are_in_\<L>\<^sub>i\<^sub>n_poss_remdups_mset:
  \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A>\<^sub>i\<^sub>n (poss (remdups_mset (atm_of `# C))) \<longleftrightarrow> literals_are_in_\<L>\<^sub>i\<^sub>n \<A>\<^sub>i\<^sub>n C\<close>
  by (induction C)
    (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff atm_of_eq_atm_of
      dest!: multi_member_split)

lemma literals_are_in_\<L>\<^sub>i\<^sub>n_negs_remdups_mset:
  \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A>\<^sub>i\<^sub>n (negs (remdups_mset (atm_of `# C))) \<longleftrightarrow> literals_are_in_\<L>\<^sub>i\<^sub>n \<A>\<^sub>i\<^sub>n C\<close>
  by (induction C)
    (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff atm_of_eq_atm_of
      dest!: multi_member_split)

lemma \<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_all_lits_of_m:
   \<open>set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (atm_of `# all_lits_of_m C)) = set_mset C \<union> uminus ` set_mset C\<close>
  supply lit_eq_Neg_Pos_iff[iff]
  by (auto simp: \<L>\<^sub>a\<^sub>l\<^sub>l_def all_lits_of_m_def image_iff dest!: multi_member_split)

lemma atm_of_all_lits_of_mm:
  \<open>set_mset (atm_of `# all_lits_of_mm bw) = atms_of_mm bw\<close>
  \<open>atm_of ` set_mset (all_lits_of_mm bw) = atms_of_mm bw\<close>
  using in_all_lits_of_mm_ain_atms_of_iff apply (auto simp: image_iff)
  by (metis (full_types) image_eqI literal.sel(1))+

lemma \<L>\<^sub>a\<^sub>l\<^sub>l_union:
   \<open>set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (A + B)) = set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l  A) \<union> set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l  B)\<close>
  by (auto simp: \<L>\<^sub>a\<^sub>l\<^sub>l_def)

lemma \<L>\<^sub>a\<^sub>l\<^sub>l_cong:
  \<open>set_mset A = set_mset B \<Longrightarrow> set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l A) = set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l B)\<close>
  by (auto simp: \<L>\<^sub>a\<^sub>l\<^sub>l_def)

lemma atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_cong:
  \<open>set_mset \<A> = set_mset \<B> \<Longrightarrow> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>) = atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<B>)\<close>
  unfolding \<L>\<^sub>a\<^sub>l\<^sub>l_def
  by auto

lemma is_\<L>\<^sub>a\<^sub>l\<^sub>l_cong:
  \<open>set_mset \<A> = set_mset \<B> \<Longrightarrow> is_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> =  is_\<L>\<^sub>a\<^sub>l\<^sub>l \<B>\<close>
  unfolding \<L>\<^sub>a\<^sub>l\<^sub>l_def is_\<L>\<^sub>a\<^sub>l\<^sub>l_def
  by auto


text \<open>The definition is here to be shared later.\<close>
definition get_propagation_reason :: \<open>('v, 'mark) ann_lits \<Rightarrow> 'v literal \<Rightarrow> 'mark option nres\<close> where
  \<open>get_propagation_reason M L = SPEC(\<lambda>C. C \<noteq> None \<longrightarrow> Propagated L (the C) \<in> set M)\<close>


end