theory Watched_Literals_Watch_List_Domain
  imports Watched_Literals_Watch_List
begin

text \<open>We refine the implementation by adding a \<^emph>\<open>domain\<close> on the literals\<close>



subsection \<open>State Conversion\<close>

subsubsection \<open>Functions and Types:\<close>

type_synonym ann_lits_l = \<open>(nat, nat) ann_lits\<close>
type_synonym clauses_to_update_ll = \<open>nat list\<close>


subsection \<open>Refinement\<close>

subsubsection \<open>Set of all literals of the problem\<close>

definition all_lits :: \<open>('a, 'v literal list \<times> 'b) fmap \<Rightarrow> 'v literal multiset multiset \<Rightarrow>
   'v literal multiset\<close> where
  \<open>all_lits S NUE = all_lits_of_mm ((\<lambda>C. mset (fst C)) `# ran_m S + NUE)\<close>

abbreviation all_lits_st :: \<open>'v twl_st_wl \<Rightarrow> 'v literal multiset\<close> where
  \<open>all_lits_st S \<equiv> all_lits (get_clauses_wl S) (get_unit_clauses_wl S)\<close>

definition all_atms :: \<open>_ \<Rightarrow> _ \<Rightarrow> 'v multiset\<close> where
  \<open>all_atms N NUE = atm_of `# all_lits N NUE\<close>

abbreviation all_atms_st :: \<open>'v twl_st_wl \<Rightarrow> 'v multiset\<close> where
  \<open>all_atms_st S \<equiv> atm_of `# all_lits_st S\<close>


text \<open>We start in a context where we have an initial set of atoms. We later extend the locale to
  include a bound on the largest atom (in order to generate more efficient code).
\<close>
context
  fixes \<A>\<^sub>i\<^sub>n :: \<open>nat multiset\<close>
begin

text \<open>This is the \<^emph>\<open>completion\<close> of \<^term>\<open>\<A>\<^sub>i\<^sub>n\<close>, containing the positive and the negation of every
  literal of \<^term>\<open>\<A>\<^sub>i\<^sub>n\<close>:\<close>
definition \<L>\<^sub>a\<^sub>l\<^sub>l where \<open>\<L>\<^sub>a\<^sub>l\<^sub>l = poss \<A>\<^sub>i\<^sub>n + negs \<A>\<^sub>i\<^sub>n\<close>

lemma atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n: \<open>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l = set_mset \<A>\<^sub>i\<^sub>n\<close>
  unfolding \<L>\<^sub>a\<^sub>l\<^sub>l_def by (auto simp: atms_of_def image_Un image_image)

definition is_\<L>\<^sub>a\<^sub>l\<^sub>l :: \<open>nat literal multiset \<Rightarrow> bool\<close> where
  \<open>is_\<L>\<^sub>a\<^sub>l\<^sub>l S \<longleftrightarrow> set_mset \<L>\<^sub>a\<^sub>l\<^sub>l = set_mset S\<close>

definition literals_are_in_\<L>\<^sub>i\<^sub>n :: \<open>nat clause \<Rightarrow> bool\<close> where
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

definition literals_are_in_\<L>\<^sub>i\<^sub>n_mm :: \<open>nat clauses \<Rightarrow> bool\<close> where
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

definition literals_are_in_\<L>\<^sub>i\<^sub>n_trail :: \<open>(nat, 'mark) ann_lits \<Rightarrow> bool\<close> where
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



definition blits_in_\<L>\<^sub>i\<^sub>n :: \<open>nat twl_st_wl \<Rightarrow> bool\<close> where
  \<open>blits_in_\<L>\<^sub>i\<^sub>n S \<longleftrightarrow>
    (\<forall>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st S). \<forall>(i, K, b) \<in> set (watched_by S L). K \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st S))\<close>


definition literals_are_\<L>\<^sub>i\<^sub>n :: \<open>nat multiset \<Rightarrow> nat twl_st_wl \<Rightarrow> bool\<close> where
  \<open>literals_are_\<L>\<^sub>i\<^sub>n \<A> S \<equiv> (is_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> (all_lits_st S) \<and> blits_in_\<L>\<^sub>i\<^sub>n S)\<close>


lemma literals_are_in_\<L>\<^sub>i\<^sub>n_nth:
  fixes C :: nat
  assumes dom: \<open>C \<in># dom_m (get_clauses_wl S)\<close> and
   \<open>literals_are_\<L>\<^sub>i\<^sub>n \<A> S\<close>
  shows \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (mset (get_clauses_wl S \<propto> C))\<close>
proof -
  let ?N = \<open>get_clauses_wl S\<close>
  have \<open>?N \<propto> C \<in># ran_mf ?N\<close>
    using dom by (auto simp: ran_m_def)
  then have \<open>mset (?N \<propto> C) \<in># mset `# (ran_mf ?N)\<close>
    by blast
  from all_lits_of_m_subset_all_lits_of_mmD[OF this] show ?thesis
    using assms(2) unfolding is_\<L>\<^sub>a\<^sub>l\<^sub>l_def literals_are_in_\<L>\<^sub>i\<^sub>n_def literals_are_\<L>\<^sub>i\<^sub>n_def
    by (auto simp add: all_lits_of_mm_union all_lits_def)
qed

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

lemma literals_are_\<L>\<^sub>i\<^sub>n_set_mset_\<L>\<^sub>a\<^sub>l\<^sub>l[simp]:
  \<open>literals_are_\<L>\<^sub>i\<^sub>n \<A> S \<Longrightarrow> set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st S)) = set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close>
  using in_all_lits_of_mm_ain_atms_of_iff
  unfolding set_mset_set_mset_eq_iff is_\<L>\<^sub>a\<^sub>l\<^sub>l_def Ball_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
    in_all_lits_of_mm_ain_atms_of_iff atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n literals_are_\<L>\<^sub>i\<^sub>n_def
  by (auto simp: in_all_lits_of_mm_ain_atms_of_iff)

lemma is_\<L>\<^sub>a\<^sub>l\<^sub>l_all_lits_st_\<L>\<^sub>a\<^sub>l\<^sub>l[simp]:
  \<open>is_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> (all_lits_st S) \<Longrightarrow>
    set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st S)) = set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close>
  \<open>is_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> (all_lits N NUE) \<Longrightarrow>
    set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (all_atms N NUE)) = set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close>
  \<open>is_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> (all_lits N NUE) \<Longrightarrow>
    set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (atm_of `# all_lits N NUE)) = set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close>
  using in_all_lits_of_mm_ain_atms_of_iff
  unfolding set_mset_set_mset_eq_iff is_\<L>\<^sub>a\<^sub>l\<^sub>l_def Ball_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
    in_all_lits_of_mm_ain_atms_of_iff atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n
  by (auto simp: in_all_lits_of_mm_ain_atms_of_iff all_lits_def all_atms_def)


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

lemma
  assumes
      x2_T: \<open>(x2, T) \<in> state_wl_l b\<close> and
      struct: \<open>twl_struct_invs U\<close> and
      T_U: \<open>(T, U) \<in> twl_st_l b'\<close>
  shows
    literals_are_\<L>\<^sub>i\<^sub>n_literals_are_\<L>\<^sub>i\<^sub>n_trail:
      \<open>literals_are_\<L>\<^sub>i\<^sub>n \<A>\<^sub>i\<^sub>n x2 \<Longrightarrow> literals_are_in_\<L>\<^sub>i\<^sub>n_trail \<A>\<^sub>i\<^sub>n (get_trail_wl x2)\<close>
     (is \<open>_\<Longrightarrow> ?trail\<close>) and
    literals_are_\<L>\<^sub>i\<^sub>n_literals_are_in_\<L>\<^sub>i\<^sub>n_conflict:
      \<open>literals_are_\<L>\<^sub>i\<^sub>n \<A>\<^sub>i\<^sub>n x2 \<Longrightarrow> get_conflict_wl x2 \<noteq> None \<Longrightarrow> literals_are_in_\<L>\<^sub>i\<^sub>n \<A>\<^sub>i\<^sub>n (the (get_conflict_wl x2))\<close> and
    conflict_not_tautology:
      \<open>get_conflict_wl x2 \<noteq> None \<Longrightarrow> \<not>tautology (the (get_conflict_wl x2))\<close>
proof -
  have
    alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of U)\<close> and
    confl: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (state\<^sub>W_of U)\<close> and
    M_lev: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (state\<^sub>W_of U)\<close> and
    dist: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of U)\<close>
   using struct unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
   by fast+

  show lits_trail: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail \<A>\<^sub>i\<^sub>n (get_trail_wl x2)\<close>
    if \<open>literals_are_\<L>\<^sub>i\<^sub>n \<A>\<^sub>i\<^sub>n x2\<close>
    using alien that x2_T T_U unfolding is_\<L>\<^sub>a\<^sub>l\<^sub>l_def
      literals_are_in_\<L>\<^sub>i\<^sub>n_trail_def cdcl\<^sub>W_restart_mset.no_strange_atm_def
      literals_are_\<L>\<^sub>i\<^sub>n_def all_lits_def all_atms_def
    by (subst (asm) all_clss_l_ran_m[symmetric])
     (auto 5 2
        simp del: all_clss_l_ran_m union_filter_mset_complement
        simp: twl_st twl_st_l twl_st_wl all_lits_of_mm_union lits_of_def
        convert_lits_l_def image_image in_all_lits_of_mm_ain_atms_of_iff
        get_unit_clauses_wl_alt_def)

  {
    assume conf: \<open>get_conflict_wl x2 \<noteq> None\<close>
    show lits_confl: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A>\<^sub>i\<^sub>n (the (get_conflict_wl x2))\<close>
      if \<open>literals_are_\<L>\<^sub>i\<^sub>n \<A>\<^sub>i\<^sub>n x2\<close>
      using x2_T T_U alien that conf unfolding is_\<L>\<^sub>a\<^sub>l\<^sub>l_alt_def
       cdcl\<^sub>W_restart_mset.no_strange_atm_def literals_are_in_\<L>\<^sub>i\<^sub>n_alt_def
       literals_are_\<L>\<^sub>i\<^sub>n_def all_lits_def all_atms_def
      apply (subst (asm) all_clss_l_ran_m[symmetric])
      unfolding image_mset_union all_lits_of_mm_union
      by (auto simp add: twl_st all_lits_of_mm_union lits_of_def
         image_image in_all_lits_of_mm_ain_atms_of_iff
        in_all_lits_of_m_ain_atms_of_iff
        get_unit_clauses_wl_alt_def
        simp del: all_clss_l_ran_m)

    have M_confl: \<open>get_trail_wl x2 \<Turnstile>as CNot (the (get_conflict_wl x2))\<close>
      using confl conf x2_T T_U unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
      by (auto 5 5 simp: twl_st true_annots_def)
    moreover have n_d: \<open>no_dup (get_trail_wl x2)\<close>
      using M_lev x2_T T_U unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
      by (auto simp: twl_st)
    ultimately show 4: \<open>\<not>tautology (the (get_conflict_wl x2))\<close>
      using n_d M_confl
      by (meson no_dup_consistentD tautology_decomp' true_annots_true_cls_def_iff_negation_in_model)
  }
qed

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

lemma in_set_all_atms_iff:
  \<open>y \<in># all_atms bu bw \<longleftrightarrow>
    y \<in> atms_of_mm (mset `# ran_mf bu) \<or> y \<in> atms_of_mm bw\<close>
  by (auto simp: all_atms_def all_lits_def in_all_lits_of_mm_ain_atms_of_iff
     atm_of_all_lits_of_mm)

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

definition unit_prop_body_wl_D_inv
  :: \<open>nat twl_st_wl \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat literal \<Rightarrow> bool\<close> where
\<open>unit_prop_body_wl_D_inv T' j w L \<longleftrightarrow>
    unit_prop_body_wl_inv T' j w L \<and> literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st T') T' \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st T')\<close>


text \<open>
  \<^item> should be the definition of \<^term>\<open>unit_prop_body_wl_find_unwatched_inv\<close>.
  \<^item> the distinctiveness should probably be only a property, not a part of the definition.
\<close>
definition unit_prop_body_wl_D_find_unwatched_inv where
\<open>unit_prop_body_wl_D_find_unwatched_inv f C S \<longleftrightarrow>
   unit_prop_body_wl_find_unwatched_inv f C S \<and>
   (f \<noteq> None \<longrightarrow> the f \<ge> 2 \<and> the f < length (get_clauses_wl S \<propto> C) \<and>
   get_clauses_wl S \<propto> C ! (the f) \<noteq> get_clauses_wl S \<propto> C ! 0  \<and>
   get_clauses_wl S \<propto> C ! (the f) \<noteq> get_clauses_wl S \<propto> C ! 1)\<close>


definition unit_propagation_inner_loop_wl_loop_D_inv where
  \<open>unit_propagation_inner_loop_wl_loop_D_inv L = (\<lambda>(j, w, S).
      literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st S) S \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st S) \<and>
      unit_propagation_inner_loop_wl_loop_inv L (j, w, S))\<close>

definition unit_propagation_inner_loop_wl_loop_D_pre where
  \<open>unit_propagation_inner_loop_wl_loop_D_pre L = (\<lambda>(j, w, S).
     unit_propagation_inner_loop_wl_loop_D_inv L (j, w, S) \<and>
     unit_propagation_inner_loop_wl_loop_pre L (j, w, S))\<close>

definition unit_propagation_inner_loop_body_wl_D
  :: \<open>nat literal \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat twl_st_wl \<Rightarrow>
    (nat \<times> nat \<times> nat twl_st_wl) nres\<close> where
  \<open>unit_propagation_inner_loop_body_wl_D L j w S = do {
      ASSERT(unit_propagation_inner_loop_wl_loop_D_pre L (j, w, S));
      let (C, K, b) = (watched_by S L) ! w;
      let S = keep_watch L j w S;
      ASSERT(unit_prop_body_wl_D_inv S j w L);
      let val_K = polarity (get_trail_wl S) K;
      if val_K = Some True
      then RETURN (j+1, w+1, S)
      else do {
          if b then do {
            ASSERT(propagate_proper_bin_case L K S C);
            if val_K = Some False
            then do {RETURN (j+1, w+1, set_conflict_wl (get_clauses_wl S \<propto> C) S)}
            else do {
              let i = (if ((get_clauses_wl S)\<propto>C) ! 0 = L then 0 else 1);
              S \<leftarrow> propagate_lit_wl_bin K C i S;
              RETURN (j+1, w+1, S)
            }
        }  \<comment>\<open>Now the costly operations:\<close>
        else if C \<notin># dom_m (get_clauses_wl S)
        then RETURN (j, w+1, S)
        else do {
          let i = (if ((get_clauses_wl S)\<propto>C) ! 0 = L then 0 else 1);
          L' \<leftarrow> mop_clauses_at (get_clauses_wl S) C (1-i);
          let val_L' = polarity (get_trail_wl S) L';
          if val_L' = Some True
          then update_blit_wl L C b j w L' S
          else do {
            f \<leftarrow> find_unwatched_l (get_trail_wl S) (get_clauses_wl S \<propto>C);
            ASSERT (unit_prop_body_wl_D_find_unwatched_inv f C S);
            case f of
              None \<Rightarrow> do {
                if val_L' = Some False
                then RETURN (j+1, w+1, set_conflict_wl (get_clauses_wl S \<propto> C) S)
                else do {
                  S \<leftarrow> propagate_lit_wl_bin K C i S;
                  RETURN (j+1, w+1, S)}
              }
            | Some f \<Rightarrow> do {
                let K = get_clauses_wl S \<propto> C ! f;
                let val_L' = polarity (get_trail_wl S) K;
                if val_L' = Some True
                then update_blit_wl L C b j w K S
                else update_clause_wl L C b j w i f S
              }
          }
        }
      }
   }\<close>

declare Id_refine[refine_vcg del] refine0(5)[refine_vcg del]

lemma unit_prop_body_wl_D_inv_clauses_distinct_eq:
  assumes
    x[simp]: \<open>watched_by S K ! w = (x1, x2)\<close> and
    inv: \<open>unit_prop_body_wl_D_inv (keep_watch K i w S) i w K\<close> and
    y: \<open>y < length (get_clauses_wl S \<propto> (fst (watched_by S K ! w)))\<close> and
    w: \<open>fst(watched_by S K ! w) \<in># dom_m (get_clauses_wl (keep_watch K i w S))\<close> and
    y': \<open>y' < length (get_clauses_wl S \<propto> (fst (watched_by S K ! w)))\<close> and
    w_le: \<open>w < length (watched_by S K)\<close>
  shows \<open>get_clauses_wl S \<propto> x1 ! y =
     get_clauses_wl S \<propto> x1 ! y' \<longleftrightarrow> y = y'\<close> (is \<open>?eq \<longleftrightarrow> ?y\<close>)
proof
  assume eq: ?eq
  let ?S = \<open>keep_watch K i w S\<close>
  let ?C = \<open>fst (watched_by ?S K ! w)\<close>
  have dom: \<open>fst (watched_by (keep_watch K i w S) K ! w) \<in># dom_m (get_clauses_wl (keep_watch K i w S))\<close>
      \<open>fst (watched_by (keep_watch K i w S) K ! w) \<in># dom_m (get_clauses_wl S)\<close>
    using w_le assms by (auto simp: x twl_st_wl)
  obtain T U where
      ST: \<open>(?S, T) \<in> state_wl_l (Some (K, w))\<close> and
      TU: \<open>(set_clauses_to_update_l
              (clauses_to_update_l
                (remove_one_lit_from_wq ?C T) +
                {#?C#})
              (remove_one_lit_from_wq ?C T),
              U)
            \<in> twl_st_l (Some K)\<close> and
      struct_U: \<open>twl_struct_invs U\<close> and
      i_w: \<open>i \<le> w\<close> and
      w_le: \<open>w < length (watched_by (keep_watch K i w S) K)\<close>
    using inv w unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def
      unit_prop_body_wl_inv_def unit_propagation_inner_loop_body_l_inv_def x fst_conv
    apply -
    apply (simp only: simp_thms dom)
    apply normalize_goal+
    by blast
  have \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of U)\<close>
    using struct_U unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast
  then have \<open>distinct_mset_mset (mset `# ran_mf (get_clauses_wl S))\<close>
    using ST TU
    unfolding image_Un cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
      all_clss_lf_ran_m[symmetric] image_mset_union
    by (auto simp: drop_Suc twl_st_wl twl_st_l twl_st)
  then have \<open>distinct (get_clauses_wl S \<propto> C)\<close> if \<open>C > 0\<close> and \<open>C \<in># dom_m (get_clauses_wl S)\<close>
     for C
    using that ST TU unfolding cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
       distinct_mset_set_def
    by (auto simp: nth_in_set_tl mset_take_mset_drop_mset cdcl\<^sub>W_restart_mset_state
      distinct_mset_set_distinct twl_st)
  moreover have \<open>?C > 0\<close> and \<open>?C \<in># dom_m (get_clauses_wl S)\<close>
    using inv w unfolding unit_propagation_inner_loop_body_l_inv_def unit_prop_body_wl_D_inv_def
      unit_prop_body_wl_inv_def x apply -
      apply (simp only: simp_thms twl_st_wl x fst_conv dom)
      apply normalize_goal+
      apply (solves simp)
      apply (simp only: simp_thms twl_st_wl x fst_conv dom)
      done
  ultimately have \<open>distinct (get_clauses_wl S \<propto> ?C)\<close>
    by blast
  moreover have \<open>fst (watched_by (keep_watch K i w S) K ! w) = fst (watched_by S K ! w)\<close>
    using i_w w_le
    by (cases S; cases \<open>i=w\<close>) (auto simp: keep_watch_def)
  ultimately show ?y
    using y y' eq
    by (auto simp: nth_eq_iff_index_eq twl_st_wl x)
next
  assume ?y
  then show ?eq by blast
qed

lemma in_all_lits_uminus_iff[simp]: \<open>(- xa \<in># all_lits N NUE) = (xa \<in># all_lits N NUE)\<close>
  unfolding all_lits_def
  by (auto simp: in_all_lits_of_mm_uminus_iff)

lemma is_\<L>\<^sub>a\<^sub>l\<^sub>l_all_atms_st_all_lits_st[simp]:
  \<open>is_\<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st S) (all_lits_st S)\<close>
  unfolding is_\<L>\<^sub>a\<^sub>l\<^sub>l_def
  by (auto simp: in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n atm_of_eq_atm_of)

lemma literals_are_\<L>\<^sub>i\<^sub>n_all_atms_st:
  \<open>blits_in_\<L>\<^sub>i\<^sub>n S \<Longrightarrow> literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st S) S\<close>
  unfolding literals_are_\<L>\<^sub>i\<^sub>n_def
  by auto

lemma blits_in_\<L>\<^sub>i\<^sub>n_keep_watch:
  assumes \<open>blits_in_\<L>\<^sub>i\<^sub>n (a, b, c, d, e, f, g)\<close> and
    w:\<open>w < length (watched_by (a, b, c, d, e, f, g) K)\<close>
  shows \<open>blits_in_\<L>\<^sub>i\<^sub>n (a, b, c, d, e, f, g (K := (g K)[j := g K ! w]))\<close>
proof -
  let ?S = \<open>(a, b, c, d, e, f, g)\<close>
  let ?T = \<open>(a, b, c, d, e, f, g (K := (g K)[j := g K ! w]))\<close>
  let ?g = \<open>g (K := (g K)[j := g K ! w])\<close>
  have H: \<open>\<And>L i K b. L\<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st ?S) \<Longrightarrow> (i, K, b) \<in>set (g L) \<Longrightarrow>
        K \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st ?S)\<close>
    using assms
    unfolding blits_in_\<L>\<^sub>i\<^sub>n_def watched_by.simps
    by blast
  have \<open> L\<in>#\<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st ?S) \<Longrightarrow> (i, K', b') \<in>set (?g L) \<Longrightarrow>
        K' \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st ?S)\<close> for L i K' b'
    using H[of L i K'] H[of L \<open>fst (g K ! w)\<close> \<open>fst (snd (g K ! w))\<close>]
      nth_mem[OF w]
    unfolding blits_in_\<L>\<^sub>i\<^sub>n_def watched_by.simps
    by (cases \<open>j < length (g K)\<close>; cases \<open>g K ! w\<close>)
      (auto split: if_splits elim!: in_set_upd_cases)
  moreover have \<open>all_atms_st ?S = all_atms_st ?T\<close>
    by (auto simp: all_lits_def all_atms_def)
  ultimately show ?thesis
    unfolding blits_in_\<L>\<^sub>i\<^sub>n_def watched_by.simps
    by force
qed

text \<open>We mark as safe intro rule, since we will always be in a case where the equivalence holds,
  although in general the equivalence does not hold.\<close>
lemma literals_are_\<L>\<^sub>i\<^sub>n_keep_watch[twl_st_wl, simp, intro!]:
  \<open>literals_are_\<L>\<^sub>i\<^sub>n \<A> S \<Longrightarrow> w < length (watched_by S K) \<Longrightarrow> literals_are_\<L>\<^sub>i\<^sub>n \<A> (keep_watch K j w S)\<close>
  by (cases S) (auto simp: keep_watch_def literals_are_\<L>\<^sub>i\<^sub>n_def
      blits_in_\<L>\<^sub>i\<^sub>n_keep_watch all_lits_def all_atms_def)

lemma all_lits_update_swap[simp]:
  \<open>x1 \<in># dom_m x1aa \<Longrightarrow> n < length (x1aa \<propto> x1) \<Longrightarrow>n' < length (x1aa \<propto> x1) \<Longrightarrow>
     all_lits (x1aa(x1 \<hookrightarrow> swap (x1aa \<propto> x1) n n')) = all_lits x1aa\<close>
  using distinct_mset_dom[of x1aa]
  unfolding all_lits_def
  by (auto simp: ran_m_def if_distrib image_mset_If filter_mset_eq not_in_iff[THEN iffD1]
      removeAll_mset_filter_mset[symmetric]
    dest!: multi_member_split[of x1]
    intro!: ext)

lemma blits_in_\<L>\<^sub>i\<^sub>n_propagate:
  \<open>x1 \<in># dom_m x1aa \<Longrightarrow> n < length (x1aa \<propto> x1) \<Longrightarrow> n' < length (x1aa \<propto> x1) \<Longrightarrow>
    blits_in_\<L>\<^sub>i\<^sub>n (Propagated A x1' # x1b, x1aa
         (x1 \<hookrightarrow> swap (x1aa \<propto> x1) n n'), D, x1c, x1d,
          add_mset A' x1e, x2e) \<longleftrightarrow>
    blits_in_\<L>\<^sub>i\<^sub>n (x1b, x1aa, D, x1c, x1d, x1e, x2e)\<close>
  \<open>x1 \<in># dom_m x1aa \<Longrightarrow> n < length (x1aa \<propto> x1) \<Longrightarrow> n' < length (x1aa \<propto> x1) \<Longrightarrow>
    blits_in_\<L>\<^sub>i\<^sub>n (x1b, x1aa
         (x1 \<hookrightarrow> swap (x1aa \<propto> x1) n n'), D, x1c, x1d,x1e, x2e) \<longleftrightarrow>
    blits_in_\<L>\<^sub>i\<^sub>n (x1b, x1aa, D, x1c, x1d, x1e, x2e)\<close>
  \<open>blits_in_\<L>\<^sub>i\<^sub>n
        (Propagated A x1' # x1b, x1aa, D, x1c, x1d,
         add_mset A' x1e, x2e) \<longleftrightarrow>
    blits_in_\<L>\<^sub>i\<^sub>n (x1b, x1aa, D, x1c, x1d, x1e, x2e)\<close>
  \<open>x1' \<in># dom_m x1aa \<Longrightarrow> n < length (x1aa \<propto> x1') \<Longrightarrow> n' < length (x1aa \<propto> x1') \<Longrightarrow>
    K \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st (x1b, x1aa, D, x1c, x1d, x1e, x2e)) \<Longrightarrow> blits_in_\<L>\<^sub>i\<^sub>n
        (x1a, x1aa(x1' \<hookrightarrow> swap (x1aa \<propto> x1') n n'), D, x1c, x1d,
         x1e, x2e
         (x1aa \<propto> x1' ! n' :=
            x2e (x1aa \<propto> x1' ! n') @ [(x1', K, b')])) \<longleftrightarrow>
    blits_in_\<L>\<^sub>i\<^sub>n (x1a, x1aa, D, x1c, x1d, x1e, x2e)\<close>
  \<open>K \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st (x1b, x1aa, D, x1c, x1d, x1e, x2e)) \<Longrightarrow>
     blits_in_\<L>\<^sub>i\<^sub>n (x1a, x1aa, D, x1c, x1d,
         x1e, x2e
         (x1aa \<propto> x1' ! n' := x2e (x1aa \<propto> x1' ! n') @ [(x1', K, b')])) \<longleftrightarrow>
  blits_in_\<L>\<^sub>i\<^sub>n (x1a, x1aa, D, x1c, x1d, x1e, x2e)\<close>
  unfolding blits_in_\<L>\<^sub>i\<^sub>n_def
  by (auto split: if_splits)[5]

lemma literals_are_\<L>\<^sub>i\<^sub>n_set_conflict_wl:
  \<open>literals_are_\<L>\<^sub>i\<^sub>n \<A> (set_conflict_wl D S) \<longleftrightarrow> literals_are_\<L>\<^sub>i\<^sub>n \<A> S\<close>
  by (cases S; auto simp: blits_in_\<L>\<^sub>i\<^sub>n_def literals_are_\<L>\<^sub>i\<^sub>n_def set_conflict_wl_def)

lemma blits_in_\<L>\<^sub>i\<^sub>n_keep_watch':
  assumes K': \<open>K' \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st (a, b, c, d, e, f, g))\<close> and
    w:\<open>blits_in_\<L>\<^sub>i\<^sub>n (a, b, c, d, e, f, g)\<close>
  shows \<open>blits_in_\<L>\<^sub>i\<^sub>n (a, b, c, d, e, f, g (K := (g K)[j := (i, K', b')]))\<close>
proof -
  let ?\<A> = \<open>all_atms_st (a, b, c, d, e, f, g)\<close>
  let ?g = \<open>g (K := (g K)[j := (i, K', b')])\<close>
  have H: \<open>\<And>L i K b'. L\<in>#\<L>\<^sub>a\<^sub>l\<^sub>l ?\<A> \<Longrightarrow> (i, K, b') \<in>set (g L) \<Longrightarrow> K \<in># \<L>\<^sub>a\<^sub>l\<^sub>l ?\<A>\<close>
    using assms
    unfolding blits_in_\<L>\<^sub>i\<^sub>n_def watched_by.simps
    by blast
  have \<open> L\<in>#\<L>\<^sub>a\<^sub>l\<^sub>l ?\<A> \<Longrightarrow> (i, K', b') \<in>set (?g L) \<Longrightarrow> K' \<in># \<L>\<^sub>a\<^sub>l\<^sub>l ?\<A>\<close> for L i K' b'
    using H[of L i K'] K'
    unfolding blits_in_\<L>\<^sub>i\<^sub>n_def watched_by.simps
    by (cases \<open>j < length (g K)\<close>; cases \<open>g K ! w\<close>)
      (auto split: if_splits elim!: in_set_upd_cases)

  then show ?thesis
    unfolding blits_in_\<L>\<^sub>i\<^sub>n_def watched_by.simps
    by force
qed

lemma literals_are_\<L>\<^sub>i\<^sub>n_all_atms_stD[dest]:
  \<open>literals_are_\<L>\<^sub>i\<^sub>n \<A> S \<Longrightarrow> literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st S) S\<close>
  unfolding literals_are_\<L>\<^sub>i\<^sub>n_def
  by auto

lemma blits_in_\<L>\<^sub>i\<^sub>n_set_conflict[simp]: \<open>blits_in_\<L>\<^sub>i\<^sub>n (set_conflict_wl D S) = blits_in_\<L>\<^sub>i\<^sub>n S\<close>
  by (cases S) (auto simp: blits_in_\<L>\<^sub>i\<^sub>n_def set_conflict_wl_def)

lemma unit_propagation_inner_loop_body_wl_D_spec:
  fixes S :: \<open>nat twl_st_wl\<close> and K :: \<open>nat literal\<close> and w :: nat
  assumes
    K: \<open>K \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close> and
    \<A>\<^sub>i\<^sub>n: \<open>literals_are_\<L>\<^sub>i\<^sub>n \<A> S\<close>
  shows \<open>unit_propagation_inner_loop_body_wl_D K j w S \<le>
      \<Down> {((j', n', T'), (j, n, T)). j' = j \<and> n' = n \<and> T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n \<A> T'}
        (unit_propagation_inner_loop_body_wl K j w S)\<close>
proof -
  obtain M N D NE UE Q W where
    S: \<open>S = (M, N, D, NE, UE, Q, W)\<close>
    by (cases S)
  have f': \<open>(f, f') \<in> \<langle>Id\<rangle>option_rel\<close> if \<open>(f, f') \<in> Id\<close> for f f'
    using that by auto
  define find_unwatched_wl :: \<open>(nat,nat) ann_lits \<Rightarrow> _\<close> where
    \<open>find_unwatched_wl = find_unwatched_l\<close>
  let ?C = \<open>fst ((watched_by S K) ! w)\<close>
  have find_unwatched: \<open>find_unwatched_wl (get_trail_wl S) ((get_clauses_wl S)\<propto>D)
    \<le> \<Down> {(L, L'). L = L' \<and> (L \<noteq> None \<longrightarrow> the L < length ((get_clauses_wl S)\<propto>C) \<and> the L \<ge> 2)}
        (find_unwatched_l (get_trail_wl S) ((get_clauses_wl S)\<propto>C))\<close>
      (is \<open>_ \<le> \<Down> ?find_unwatched _\<close>)
    if \<open>C = D\<close>
    for C D and L and K and S
    unfolding find_unwatched_l_def find_unwatched_wl_def that
    by (auto simp: intro!: RES_refine)

  have propagate_lit_wl:
      \<open>(propagate_lit_wl
         (get_clauses_wl S \<propto> x1a ! (1 - (if get_clauses_wl S \<propto> x1a ! 0 = K then 0 else 1)))
         x1a
         (if get_clauses_wl S \<propto> x1a ! 0 = K then 0 else 1)
          S) \<le> \<Down> {(T', T).
         T = T' \<and>
         literals_are_\<L>\<^sub>i\<^sub>n \<A> T'}
       (propagate_lit_wl
        (get_clauses_wl S \<propto> x1 !
         (1 - (if get_clauses_wl S \<propto> x1 ! 0 = K then 0
               else 1)))
       x1
        (if get_clauses_wl S \<propto> x1 ! 0 = K then 0 else 1) S)\<close>
  if \<open>unit_prop_body_wl_D_inv S j w K\<close> and \<open>\<not>x1 \<notin># dom_m (get_clauses_wl S)\<close> and
    \<open>(watched_by S K) ! w = (x1a, x2a)\<close> and
    \<open>(watched_by S K) ! w = (x1, x2)\<close> and
    \<open>literals_are_\<L>\<^sub>i\<^sub>n \<A> S\<close>
  for f f' j S x1 x2 x1a x2a
  unfolding propagate_lit_wl_def S
  apply (refine_vcg mop_clauses_swap_itself_spec)
  using that \<A>\<^sub>i\<^sub>n
  by (auto simp: clauses_def unit_prop_body_wl_find_unwatched_inv_def
        mset_take_mset_drop_mset' S unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def
        ran_m_mapsto_upd unit_propagation_inner_loop_body_l_inv_def blits_in_\<L>\<^sub>i\<^sub>n_propagate
        state_wl_l_def image_mset_remove1_mset_if literals_are_\<L>\<^sub>i\<^sub>n_def op_clauses_swap_def
        mop_clauses_swap_def intro!: ASSERT_refine_right)

  have update_clause_wl: \<open>update_clause_wl K x1' b' j w
     (if get_clauses_wl S \<propto> x1' ! 0 = K then 0 else 1) n S
    \<le> \<Down> {((j', n', T'), j, n, T). j' = j \<and> n' = n \<and> T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n \<A> T'}
       (update_clause_wl K x1 b j w
         (if get_clauses_wl S \<propto> x1 ! 0 = K then 0 else 1) n' S)\<close>
    if \<open>(n, n') \<in> Id\<close> and \<open>unit_prop_body_wl_D_inv S j w K\<close>
      \<open>(f, f') \<in> ?find_unwatched x1 S\<close> and
      \<open>f = Some n\<close> \<open>f' = Some n'\<close> and
      \<open>unit_prop_body_wl_D_find_unwatched_inv f x1' S\<close> and
      \<open>\<not>x1 \<notin># dom_m (get_clauses_wl S)\<close> and
      \<open>watched_by S K ! w = (x1, x2)\<close> and
      \<open>watched_by S K ! w = (x1', x2')\<close> and
      \<open>(b, b') \<in> Id\<close> and
      \<open>literals_are_\<L>\<^sub>i\<^sub>n \<A> S\<close>
    for n n' f f' S x1 x2 x1' x2' b b'
    unfolding update_clause_wl_def S
    apply (refine_rcg mop_clauses_swap_itself_spec)
    using that \<A>\<^sub>i\<^sub>n
    by (auto simp: clauses_def mset_take_mset_drop_mset unit_prop_body_wl_find_unwatched_inv_def
          mset_take_mset_drop_mset' S unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def
          ran_m_clause_upd unit_propagation_inner_loop_body_l_inv_def blits_in_\<L>\<^sub>i\<^sub>n_propagate
          state_wl_l_def image_mset_remove1_mset_if literals_are_\<L>\<^sub>i\<^sub>n_def op_clauses_swap_def)

  have H: \<open>watched_by S K ! w = A \<Longrightarrow> watched_by (keep_watch K j w S) K ! w = A\<close>
    for S j w K A x1
    by (cases S; cases \<open>j=w\<close>) (auto simp: keep_watch_def)
  have update_blit_wl: \<open>update_blit_wl K x1a b' j w
        (get_clauses_wl (keep_watch K j w S) \<propto> x1a !
          (1 - (if get_clauses_wl (keep_watch K j w S) \<propto> x1a ! 0 = K then 0 else 1)))
        (keep_watch K j w S)
        \<le> \<Down> {((j', n', T'), j, n, T).
            j' = j \<and> n' = n \<and> T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n \<A> T'}
          (update_blit_wl K x1 b j w
            (get_clauses_wl (keep_watch K j w S) \<propto> x1 !
              (1 -
              (if get_clauses_wl (keep_watch K j w S) \<propto> x1 ! 0 = K then 0
                else 1)))
            (keep_watch K j w S))\<close>
    if
      x: \<open>watched_by S K ! w = (x1, x2)\<close> and
      xa: \<open>watched_by S K ! w = (x1a, x2a)\<close> and
      unit: \<open>unit_prop_body_wl_D_inv (keep_watch K j w S) j w K\<close> and
      x1: \<open>\<not>x1 \<notin># dom_m (get_clauses_wl (keep_watch K j w S))\<close> and
      bb': \<open>(b, b') \<in> Id\<close>
    for x1 x2 x1a x2a b b'
  proof -
    have [simp]: \<open>x1a = x1\<close> and x1a: \<open>x1 \<in># dom_m (get_clauses_wl S)\<close>
      \<open>fst (watched_by (keep_watch K j w S) K ! w) \<in># dom_m (get_clauses_wl (keep_watch K j w S))\<close>
      using x xa x1 unit unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def
      by auto

    have \<open>get_clauses_wl S \<propto>x1 ! 0 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A> \<and> get_clauses_wl S \<propto> x1 ! Suc 0 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close>
      using assms that
        literals_are_in_\<L>\<^sub>i\<^sub>n_nth[of x1 S]
        literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l[of \<A> \<open>get_clauses_wl S \<propto> x1\<close> 0]
        literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l[of \<A> \<open>get_clauses_wl S \<propto> x1\<close> 1]
      unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def
        unit_propagation_inner_loop_body_l_inv_def x1a apply (simp only: x1a fst_conv simp_thms)
      apply normalize_goal+
      by (auto simp del:  simp: x1a)
    then show ?thesis
      using assms unit bb'
      by (cases S)
        (auto simp: keep_watch_def update_blit_wl_def literals_are_\<L>\<^sub>i\<^sub>n_def
          blits_in_\<L>\<^sub>i\<^sub>n_propagate blits_in_\<L>\<^sub>i\<^sub>n_keep_watch' unit_prop_body_wl_D_inv_def)
  qed
  have update_blit_wl': \<open>update_blit_wl K x1a b' j w (get_clauses_wl (keep_watch K j w S) \<propto> x1a ! x)
        (keep_watch K j w S)
        \<le> \<Down> {((j', n', T'), j, n, T).
            j' = j \<and> n' = n \<and> T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n \<A> T'}
          (update_blit_wl K x1 b j w
            (get_clauses_wl (keep_watch K j w S) \<propto> x1 ! x')
            (keep_watch K j w S))\<close>
    if
      x1: \<open>watched_by S K ! w = (x1, x2)\<close> and
      xa: \<open>watched_by S K ! w = (x1a, x2a)\<close> and
      unw: \<open>unit_prop_body_wl_D_find_unwatched_inv f x1a (keep_watch K j w S)\<close> and
      dom: \<open>\<not>x1 \<notin># dom_m(get_clauses_wl (keep_watch K j w S))\<close> and
      unit: \<open>unit_prop_body_wl_D_inv (keep_watch K j w S) j w K\<close> and
      f: \<open>f = Some x\<close> and
      xx': \<open>(x, x') \<in> nat_rel\<close> and
      bb': \<open>(b, b') \<in> Id\<close>
    for x1 x2 x1a x2a f fa x x' b b'
  proof -
    have [simp]: \<open>x1a = x1\<close> \<open>x = x'\<close>
      using x1 xa xx' by auto

    have x1a: \<open>x1 \<in># dom_m (get_clauses_wl S)\<close>
      \<open>fst (watched_by S K ! w) \<in># dom_m (get_clauses_wl S)\<close>
      using dom x1 by auto
    have \<open>get_clauses_wl S \<propto>x1 ! x \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close>
      using assms that
        literals_are_in_\<L>\<^sub>i\<^sub>n_nth[of x1 S]
        literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l[of \<A> \<open>get_clauses_wl S \<propto> x1\<close> x]
         unw
      unfolding unit_prop_body_wl_D_find_unwatched_inv_def
      by auto
    then show ?thesis
      using assms bb'
      by (cases S) (auto simp: keep_watch_def update_blit_wl_def literals_are_\<L>\<^sub>i\<^sub>n_def
          blits_in_\<L>\<^sub>i\<^sub>n_propagate blits_in_\<L>\<^sub>i\<^sub>n_keep_watch')
  qed

  have set_conflict_rel:
    \<open>((j + 1, w + 1,
        set_conflict_wl (get_clauses_wl (keep_watch K j w S) \<propto> x1a) (keep_watch K j w S)),
       j + 1, w + 1,
       set_conflict_wl (get_clauses_wl (keep_watch K j w S) \<propto> x1) (keep_watch K j w S))
      \<in> {((j', n', T'), j, n, T). j' = j \<and> n' = n \<and> T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n \<A> T'}\<close>
    if
      pre: \<open>unit_propagation_inner_loop_wl_loop_D_pre K (j, w, S)\<close> and
      x: \<open>watched_by S K ! w = (x1, x2)\<close> and
      xa: \<open>watched_by S K ! w = (x1a, x2a')\<close> and
      xa': \<open>x2a' = (x2a, x3)\<close> and
      unit: \<open>unit_prop_body_wl_D_inv (keep_watch K j w S) j w K\<close> and
      dom: \<open>\<not> x1a \<notin># dom_m (get_clauses_wl (keep_watch K j w S))\<close>
    for x1 x2 x1a x2a f fa x2a' x3
  proof -
    have [simp]: \<open>blits_in_\<L>\<^sub>i\<^sub>n
        (set_conflict_wl D (a, b, c, d, e, fb, g(K := (g K)[j := de]))) \<longleftrightarrow>
        blits_in_\<L>\<^sub>i\<^sub>n ((a, b, c, d, e, fb, g(K := (g K)[j := de])))\<close>
      for a b c d e f g de D
      by (auto simp: blits_in_\<L>\<^sub>i\<^sub>n_def set_conflict_wl_def)

    have [simp]: \<open>x1a = x1\<close>
      using xa x by auto

    have \<open>x2a \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close>
      using xa x dom assms pre unit nth_mem[of w \<open>watched_by S K\<close>] xa'
      by (cases S)
        (auto simp: unit_prop_body_wl_D_inv_def literals_are_\<L>\<^sub>i\<^sub>n_def
          unit_prop_body_wl_inv_def blits_in_\<L>\<^sub>i\<^sub>n_def keep_watch_def
          unit_propagation_inner_loop_wl_loop_D_pre_def
          dest!: multi_member_split split: if_splits)
    then show ?thesis
      using assms that by (cases S) (auto simp: keep_watch_def literals_are_\<L>\<^sub>i\<^sub>n_set_conflict_wl
        literals_are_\<L>\<^sub>i\<^sub>n_def blits_in_\<L>\<^sub>i\<^sub>n_keep_watch')
  qed
  have bin_set_conflict:
    \<open>((j + 1, w + 1, set_conflict_wl (get_clauses_wl (keep_watch K j w S) \<propto> x1b) (keep_watch K j w S)), j + 1, w + 1,
       set_conflict_wl (get_clauses_wl (keep_watch K j w S) \<propto> x1) (keep_watch K j w S))
      \<in> {((j', n', T'), j, n, T). j' = j \<and> n' = n \<and> T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n \<A> T'}\<close>
    if
      \<open>unit_propagation_inner_loop_wl_loop_pre K (j, w, S)\<close> and
      \<open>unit_propagation_inner_loop_wl_loop_D_pre K (j, w, S)\<close> and
      \<open>x2 = (x1a, x2a)\<close> and
      \<open>watched_by S K ! w = (x1, x2)\<close> and
      \<open>x2b = (x1c, x2c)\<close> and
      \<open>watched_by S K ! w = (x1b, x2b)\<close> and
      \<open>unit_prop_body_wl_inv (keep_watch K j w S) j w K\<close> and
      \<open>unit_prop_body_wl_D_inv (keep_watch K j w S) j w K\<close> and
      \<open>polarity (get_trail_wl (keep_watch K j w S)) x1c \<noteq> Some True\<close> and
      \<open>polarity (get_trail_wl (keep_watch K j w S)) x1a \<noteq> Some True\<close> and
      \<open>x2c\<close> and
      \<open>x2a\<close> and
      \<open>polarity (get_trail_wl (keep_watch K j w S)) x1c = Some False\<close> and
      \<open>polarity (get_trail_wl (keep_watch K j w S)) x1a = Some False\<close>
    for x1 x2 x1a x2a x1b x2b x1c x2c
  proof -
    show ?thesis
      using that assms
      by (auto simp: literals_are_\<L>\<^sub>i\<^sub>n_set_conflict_wl unit_propagation_inner_loop_wl_loop_pre_def)
  qed
  have bin_prop:
    \<open>propagate_lit_wl_bin x1c x1b (if get_clauses_wl (keep_watch K j w S) \<propto> x1b ! 0 = K then 0 else 1) (keep_watch K j w S) \<le> \<Down> {(T', T). T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n \<A> T'}
       (propagate_lit_wl_bin x1a x1 (if get_clauses_wl (keep_watch K j w S) \<propto> x1 ! 0 = K then 0 else 1) (keep_watch K j w S))\<close>
    if
      \<open>unit_propagation_inner_loop_wl_loop_pre K (j, w, S)\<close> and
      \<open>unit_propagation_inner_loop_wl_loop_D_pre K (j, w, S)\<close> and
      \<open>x2 = (x1a, x2a)\<close> and
      \<open>watched_by S K ! w = (x1, x2)\<close> and
      \<open>x2b = (x1c, x2c)\<close> and
      \<open>watched_by S K ! w = (x1b, x2b)\<close> and
      \<open>unit_prop_body_wl_inv (keep_watch K j w S) j w K\<close> and
      \<open>unit_prop_body_wl_D_inv (keep_watch K j w S) j w K\<close> and
      \<open>polarity (get_trail_wl (keep_watch K j w S)) x1c \<noteq> Some True\<close> and
      \<open>polarity (get_trail_wl (keep_watch K j w S)) x1a \<noteq> Some True\<close> and
      \<open>x2c\<close> and
      \<open>x2a\<close> and
      \<open>polarity (get_trail_wl (keep_watch K j w S)) x1c \<noteq> Some False\<close> and
      \<open>polarity (get_trail_wl (keep_watch K j w S)) x1a \<noteq> Some False\<close> and
      \<open>propagate_proper_bin_case K x1a (keep_watch K j w S) x1\<close>
    for x1 x2 x1a x2a x1b x2b x1c x2c
  unfolding propagate_lit_wl_bin_def S propagate_proper_bin_case_def
  apply refine_vcg
  using that \<A>\<^sub>i\<^sub>n
  by (simp_all add: unit_prop_body_wl_find_unwatched_inv_def
        propagate_proper_bin_case_def unit_prop_body_wl_inv_def
        S unit_prop_body_wl_D_inv_def keep_watch_def state_wl_l_def literals_are_\<L>\<^sub>i\<^sub>n_def
	Let_def blits_in_\<L>\<^sub>i\<^sub>n_propagate)
  show ?thesis
    unfolding unit_propagation_inner_loop_body_wl_D_def find_unwatched_wl_def[symmetric]
    unfolding unit_propagation_inner_loop_body_wl_def
    supply [[goals_limit=1]]
    apply (refine_rcg find_unwatched f' mop_clauses_at_itself[THEN fref_to_Down_curry2])
    subgoal using assms unfolding unit_propagation_inner_loop_wl_loop_D_inv_def
        unit_propagation_inner_loop_wl_loop_D_pre_def unit_propagation_inner_loop_wl_loop_pre_def
      by auto
    subgoal using assms unfolding unit_prop_body_wl_D_inv_def
        unit_propagation_inner_loop_wl_loop_pre_def by auto
    subgoal by simp
    subgoal using assms by (auto simp: unit_propagation_inner_loop_wl_loop_pre_def)
    subgoal by simp
    subgoal
      using assms by (auto simp: unit_prop_body_wl_D_inv_clauses_distinct_eq
          unit_propagation_inner_loop_wl_loop_pre_def)
    subgoal by auto
    subgoal
      by (rule bin_set_conflict)
    apply (rule bin_prop; assumption)
    subgoal for x1 x2 x1a x2a x1b x2b x1c x2c
      by simp
    subgoal by simp
    subgoal
      using assms by (auto simp: unit_prop_body_wl_D_inv_clauses_distinct_eq
          unit_propagation_inner_loop_wl_loop_pre_def)
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by (rule update_blit_wl) auto
    subgoal by simp
    subgoal
      using assms
      unfolding unit_prop_body_wl_D_find_unwatched_inv_def unit_prop_body_wl_inv_def
      by (cases \<open>watched_by S K ! w\<close>)
        (auto simp: unit_prop_body_wl_D_inv_clauses_distinct_eq twl_st_wl)
    subgoal by (auto simp: twl_st_wl)
    subgoal by (auto simp: twl_st_wl)
    subgoal for x1 x2 x1a x2a f fa
      by (rule set_conflict_rel)
    subgoal
      by (rule propagate_lit_wl[OF _ _ H H]; assumption?)
       (simp add: assms literals_are_\<L>\<^sub>i\<^sub>n_keep_watch assms
        unit_propagation_inner_loop_wl_loop_pre_def)
    subgoal by (auto simp: twl_st_wl)
    subgoal by (rule update_blit_wl') auto
    subgoal by (rule update_clause_wl[OF _ _ _ _ _ _ _ H H]; assumption?) (auto simp: assms
      unit_propagation_inner_loop_wl_loop_pre_def)
    done
qed


lemma unit_propagation_inner_loop_body_wl_D_unit_propagation_inner_loop_body_wl_D:
  \<open>(uncurry3 unit_propagation_inner_loop_body_wl_D, uncurry3 unit_propagation_inner_loop_body_wl) \<in>
    [\<lambda>(((K, j), w), S). literals_are_\<L>\<^sub>i\<^sub>n \<A> S \<and> K \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>]\<^sub>f
    Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<rightarrow> \<langle>nat_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r
       {(T', T). T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n \<A> T}\<rangle> nres_rel\<close>
     (is \<open>?G1\<close>) and
  unit_propagation_inner_loop_body_wl_D_unit_propagation_inner_loop_body_wl_D_weak:
   \<open>(uncurry3 unit_propagation_inner_loop_body_wl_D, uncurry3 unit_propagation_inner_loop_body_wl) \<in>
    [\<lambda>(((K, j), w), S). literals_are_\<L>\<^sub>i\<^sub>n \<A> S \<and> K \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>]\<^sub>f
    Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<rightarrow> \<langle>nat_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r Id\<rangle> nres_rel\<close>
   (is \<open>?G2\<close>)
proof -
  have 1: \<open>nat_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r {(T', T). T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n \<A> T} =
     {((j', n', T'), (j, (n, T))). j' = j \<and> n' = n \<and> T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n \<A> T'}\<close>
    by auto
  show ?G1
    by (auto simp add: fref_def nres_rel_def uncurry_def simp del: twl_st_of_wl.simps
        intro!: unit_propagation_inner_loop_body_wl_D_spec[of _ \<A>, unfolded 1[symmetric]])

  then show ?G2
    apply -
    apply (match_spec)
    apply (match_fun_rel; match_fun_rel?)
    by fastforce+
qed

definition unit_propagation_inner_loop_wl_loop_D
  :: \<open>nat literal \<Rightarrow> nat twl_st_wl \<Rightarrow> (nat \<times> nat \<times> nat twl_st_wl) nres\<close>
where
  \<open>unit_propagation_inner_loop_wl_loop_D L S\<^sub>0 = do {
    ASSERT(L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st S\<^sub>0));
    let n = length (watched_by S\<^sub>0 L);
    WHILE\<^sub>T\<^bsup>unit_propagation_inner_loop_wl_loop_D_inv L\<^esup>
      (\<lambda>(j, w, S). w < n \<and> get_conflict_wl S = None)
      (\<lambda>(j, w, S). do {
        unit_propagation_inner_loop_body_wl_D L j w S
      })
      (0, 0, S\<^sub>0)
  }
  \<close>

lemma unit_propagation_inner_loop_wl_spec:
  assumes \<A>\<^sub>i\<^sub>n: \<open>literals_are_\<L>\<^sub>i\<^sub>n \<A> S\<close> and K: \<open>K \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close>
  shows \<open>unit_propagation_inner_loop_wl_loop_D K S \<le>
     \<Down> {((j', n', T'), j, n, T). j' = j \<and> n' = n \<and> T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n \<A> T'}
       (unit_propagation_inner_loop_wl_loop K S)\<close>
proof -
  have u: \<open>unit_propagation_inner_loop_body_wl_D K j w S \<le>
         \<Down> {((j', n', T'), j, n, T). j' = j \<and> n' = n \<and> T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n \<A> T'}
           (unit_propagation_inner_loop_body_wl K' j' w' S')\<close>
  if \<open>K \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close> and \<open>literals_are_\<L>\<^sub>i\<^sub>n \<A> S\<close> and
    \<open>S = S'\<close> \<open>K = K'\<close> \<open>w = w'\<close> \<open>j'=j\<close>
  for S S' and w w' and K K' and j' j
    using unit_propagation_inner_loop_body_wl_D_spec[of K \<A> S j w] that by auto

  show ?thesis
    unfolding unit_propagation_inner_loop_wl_loop_D_def unit_propagation_inner_loop_wl_loop_def
    apply (refine_vcg u)
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms unfolding unit_propagation_inner_loop_wl_loop_D_inv_def
      by (auto dest: literals_are_\<L>\<^sub>i\<^sub>n_set_mset_\<L>\<^sub>a\<^sub>l\<^sub>l)
    subgoal by auto
    subgoal using K by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

definition unit_propagation_inner_loop_wl_D
 :: \<open>nat literal \<Rightarrow> nat twl_st_wl \<Rightarrow> nat twl_st_wl nres\<close> where
  \<open>unit_propagation_inner_loop_wl_D L S\<^sub>0 = do {
     (j, w, S) \<leftarrow> unit_propagation_inner_loop_wl_loop_D L S\<^sub>0;
     ASSERT (j \<le> w \<and> w \<le> length (watched_by S L) \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st S\<^sub>0) \<and>
        L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st S));
     S \<leftarrow> cut_watch_list j w L S;
     RETURN S
  }\<close>

lemma unit_propagation_inner_loop_wl_D_spec:
  assumes \<A>\<^sub>i\<^sub>n: \<open>literals_are_\<L>\<^sub>i\<^sub>n \<A> S\<close> and K: \<open>K \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close>
  shows \<open>unit_propagation_inner_loop_wl_D K S \<le>
     \<Down> {(T', T). T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n \<A> T}
       (unit_propagation_inner_loop_wl K S)\<close>
proof -
  have cut_watch_list: \<open>cut_watch_list x1b x1c K x2c \<bind> RETURN
        \<le> \<Down> {(T', T). T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n \<A> T}
          (cut_watch_list x1 x1a K x2a)\<close>
    if
      \<open>(x, x')
      \<in> {((j', n', T'), j, n, T).
          j' = j \<and> n' = n \<and> T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n \<A> T'}\<close> and
      \<open>x2 = (x1a, x2a)\<close> and
      \<open>x' = (x1, x2)\<close> and
      \<open>x2b = (x1c, x2c)\<close> and
      \<open>x = (x1b, x2b)\<close> and
      \<open>x1 \<le> x1a \<and> x1a \<le> length (watched_by x2a K)\<close>
    for x x' x1 x2 x1a x2a x1b x2b x1c x2c
  proof -
    show ?thesis
      using that unfolding literals_are_\<L>\<^sub>i\<^sub>n_def
      by (cases x2c) (auto simp: cut_watch_list_def
          blits_in_\<L>\<^sub>i\<^sub>n_def dest!: in_set_takeD in_set_dropD)
  qed

  show ?thesis
    unfolding unit_propagation_inner_loop_wl_D_def unit_propagation_inner_loop_wl_def
    apply (refine_vcg unit_propagation_inner_loop_wl_spec[of \<A>])
    subgoal using \<A>\<^sub>i\<^sub>n .
    subgoal using K .
    subgoal by auto
    subgoal by auto
    subgoal using \<A>\<^sub>i\<^sub>n K by auto
    subgoal using \<A>\<^sub>i\<^sub>n K by auto
    subgoal by (rule cut_watch_list)
    done
qed

definition unit_propagation_outer_loop_wl_D_inv where
\<open>unit_propagation_outer_loop_wl_D_inv S \<longleftrightarrow>
    unit_propagation_outer_loop_wl_inv S \<and>
    literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st S) S\<close>

definition unit_propagation_outer_loop_wl_D
   :: \<open>nat twl_st_wl \<Rightarrow> nat twl_st_wl nres\<close>
where
  \<open>unit_propagation_outer_loop_wl_D S\<^sub>0 =
    WHILE\<^sub>T\<^bsup>unit_propagation_outer_loop_wl_D_inv\<^esup>
      (\<lambda>S. literals_to_update_wl S \<noteq> {#})
      (\<lambda>S. do {
        ASSERT(literals_to_update_wl S \<noteq> {#});
        (S', L) \<leftarrow> select_and_remove_from_literals_to_update_wl S;
        ASSERT(L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st S));
        unit_propagation_inner_loop_wl_D L S'
      })
      (S\<^sub>0 :: nat twl_st_wl)\<close>

lemma literals_are_\<L>\<^sub>i\<^sub>n_set_lits_to_upd[twl_st_wl, simp]:
   \<open>literals_are_\<L>\<^sub>i\<^sub>n \<A> (set_literals_to_update_wl C S) \<longleftrightarrow> literals_are_\<L>\<^sub>i\<^sub>n \<A> S\<close>
  by (cases S) (auto simp: literals_are_\<L>\<^sub>i\<^sub>n_def blits_in_\<L>\<^sub>i\<^sub>n_def)

lemma unit_propagation_outer_loop_wl_D_spec:
  assumes \<A>\<^sub>i\<^sub>n: \<open>literals_are_\<L>\<^sub>i\<^sub>n \<A> S\<close>
  shows \<open>unit_propagation_outer_loop_wl_D S \<le>
     \<Down> {(T', T). T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n \<A> T}
       (unit_propagation_outer_loop_wl S)\<close>
proof -
  have H: \<open>set_mset (all_lits_of_mm (mset `# ran_mf (get_clauses_wl S') + get_unit_clauses_wl S')) =
    set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st S'))\<close> for S'
    by (auto simp: in_all_lits_of_mm_ain_atms_of_iff all_atms_def all_lits_def
      in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n)
  have select: \<open>select_and_remove_from_literals_to_update_wl S \<le>
    \<Down> {((T', L'), (T, L)). T = T' \<and> L = L' \<and>
        T = set_literals_to_update_wl (literals_to_update_wl S - {#L#}) S}
              (select_and_remove_from_literals_to_update_wl S')\<close>
    if \<open>S = S'\<close> for S S' :: \<open>nat twl_st_wl\<close>
    unfolding select_and_remove_from_literals_to_update_wl_def select_and_remove_from_literals_to_update_def
    apply (rule RES_refine)
    using that unfolding select_and_remove_from_literals_to_update_wl_def by blast
  have unit_prop: \<open>literals_are_\<L>\<^sub>i\<^sub>n \<A> S \<Longrightarrow>
          K \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A> \<Longrightarrow>
          unit_propagation_inner_loop_wl_D K S
          \<le> \<Down> {(T', T). T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n \<A> T} (unit_propagation_inner_loop_wl K' S')\<close>
    if \<open>K = K'\<close> and \<open>S = S'\<close> for K K' and S S' :: \<open>nat twl_st_wl\<close>
    unfolding that by (rule unit_propagation_inner_loop_wl_D_spec)
  show ?thesis
    unfolding unit_propagation_outer_loop_wl_D_def unit_propagation_outer_loop_wl_def H
    apply (refine_vcg select unit_prop)
    subgoal using \<A>\<^sub>i\<^sub>n by simp
    subgoal unfolding unit_propagation_outer_loop_wl_D_inv_def by auto
    subgoal by auto
    subgoal by auto
    subgoal using \<A>\<^sub>i\<^sub>n apply simp by auto
    subgoal by auto
    subgoal by auto
    subgoal using \<A>\<^sub>i\<^sub>n by (auto simp: twl_st_wl)
    subgoal for S' S T'L' TL T' L' T L
      using \<A>\<^sub>i\<^sub>n by auto
    done
qed

lemma unit_propagation_outer_loop_wl_D_spec':
  shows \<open>(unit_propagation_outer_loop_wl_D, unit_propagation_outer_loop_wl) \<in>
    {(T', T). T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n \<A> T} \<rightarrow>\<^sub>f
     \<langle>{(T', T). T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n \<A> T}\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  subgoal for x y
    apply (rule order_trans)
    apply (rule unit_propagation_outer_loop_wl_D_spec[of \<A> x])
     apply (auto simp: prod_rel_def intro: conc_fun_R_mono)
    done
  done

definition skip_and_resolve_loop_wl_D_inv where
  \<open>skip_and_resolve_loop_wl_D_inv S\<^sub>0 brk S \<equiv>
      skip_and_resolve_loop_wl_inv S\<^sub>0 brk S \<and> literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st S) S\<close>

definition skip_and_resolve_loop_wl_D
  :: \<open>nat twl_st_wl \<Rightarrow> nat twl_st_wl nres\<close>
where
  \<open>skip_and_resolve_loop_wl_D S\<^sub>0 =
    do {
      ASSERT(get_conflict_wl S\<^sub>0 \<noteq> None);
      (_, S) \<leftarrow>
        WHILE\<^sub>T\<^bsup>\<lambda>(brk, S). skip_and_resolve_loop_wl_D_inv S\<^sub>0 brk S\<^esup>
        (\<lambda>(brk, S). \<not>brk \<and> \<not>is_decided (hd (get_trail_wl S)))
        (\<lambda>(brk, S).
          do {
            ASSERT(\<not>brk \<and> \<not>is_decided (hd (get_trail_wl S)));
            let D' = the (get_conflict_wl S);
            let (L, C) = lit_and_ann_of_propagated (hd (get_trail_wl S));
            if -L \<notin># D' then
              do {RETURN (False, tl_state_wl S)}
            else
              if get_maximum_level (get_trail_wl S) (remove1_mset (-L) D') =
                count_decided (get_trail_wl S)
              then
                do {RETURN (update_confl_tl_wl C L S)}
              else
                do {RETURN (True, S)}
          }
        )
        (False, S\<^sub>0);
      RETURN S
    }
  \<close>

lemma literals_are_\<L>\<^sub>i\<^sub>n_tl_state_wl[simp]:
  \<open>literals_are_\<L>\<^sub>i\<^sub>n \<A> (tl_state_wl S) = literals_are_\<L>\<^sub>i\<^sub>n \<A> S\<close>
  by (cases S)
   (auto simp: is_\<L>\<^sub>a\<^sub>l\<^sub>l_def tl_state_wl_def literals_are_\<L>\<^sub>i\<^sub>n_def blits_in_\<L>\<^sub>i\<^sub>n_def)

lemma get_clauses_wl_tl_state: \<open>get_clauses_wl (tl_state_wl T) = get_clauses_wl T\<close>
  unfolding tl_state_wl_def by (cases T) auto

lemma blits_in_\<L>\<^sub>i\<^sub>n_skip_and_resolve[simp]:
  \<open>blits_in_\<L>\<^sub>i\<^sub>n (tl x1aa, N, D, ar, as, at, bd) = blits_in_\<L>\<^sub>i\<^sub>n (x1aa, N, D, ar, as, at, bd)\<close>
  \<open>blits_in_\<L>\<^sub>i\<^sub>n
        (x1aa, N,
         Some (resolve_cls_wl' (x1aa', N', x1ca', ar', as', at', bd') x2b
            x1b),
         ar, as, at, bd) =
  blits_in_\<L>\<^sub>i\<^sub>n (x1aa, N, x1ca', ar, as, at, bd)\<close>
  by (auto simp: blits_in_\<L>\<^sub>i\<^sub>n_def)


lemma skip_and_resolve_loop_wl_D_spec:
  assumes \<A>\<^sub>i\<^sub>n: \<open>literals_are_\<L>\<^sub>i\<^sub>n \<A> S\<close>
  shows \<open>skip_and_resolve_loop_wl_D S \<le>
     \<Down> {(T', T). T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n \<A> T \<and> get_clauses_wl T = get_clauses_wl S}
       (skip_and_resolve_loop_wl S)\<close>
    (is \<open>_ \<le> \<Down> ?R _\<close>)
proof -
  define invar where
   \<open>invar = (\<lambda>(brk, T). skip_and_resolve_loop_wl_D_inv S brk T)\<close>
  have 1: \<open>((get_conflict_wl S = Some {#}, S), get_conflict_wl S = Some {#}, S) \<in> Id\<close>
    by auto

  show ?thesis
    unfolding skip_and_resolve_loop_wl_D_def skip_and_resolve_loop_wl_def
    apply (subst (2) WHILEIT_add_post_condition)
    apply (refine_rcg 1 WHILEIT_refine[where R = \<open>{((i', S'), (i, S)). i = i' \<and> (S', S) \<in> ?R}\<close>])
    subgoal using assms by auto
    subgoal unfolding skip_and_resolve_loop_wl_D_inv_def by fast
    subgoal by fast
    subgoal by fast
    subgoal by fast
    subgoal by auto
    subgoal
      unfolding skip_and_resolve_loop_wl_D_inv_def update_confl_tl_wl_def
      by (auto split: prod.splits) (simp add: get_clauses_wl_tl_state)
    subgoal by auto
    subgoal
      unfolding skip_and_resolve_loop_wl_D_inv_def update_confl_tl_wl_def
      by (auto split: prod.splits simp: literals_are_\<L>\<^sub>i\<^sub>n_def)
    subgoal by auto
    subgoal by auto
    done
qed

definition find_lit_of_max_level_wl' :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow>
   nat literal nres\<close> where
  \<open>find_lit_of_max_level_wl' M N D NE UE Q W L =
     find_lit_of_max_level_wl (M, N, Some D, NE, UE, Q, W) L\<close>

definition (in -) list_of_mset2
  :: \<open>nat literal \<Rightarrow> nat literal \<Rightarrow> nat clause \<Rightarrow> nat clause_l nres\<close>
where
  \<open>list_of_mset2 L L' D =
    SPEC (\<lambda>E. mset E = D \<and> E!0 = L \<and> E!1 = L' \<and> length E \<ge> 2)\<close>

definition single_of_mset where
  \<open>single_of_mset D = SPEC(\<lambda>L. D = mset [L])\<close>

definition backtrack_wl_D_inv where
  \<open>backtrack_wl_D_inv S \<longleftrightarrow> backtrack_wl_inv S \<and> literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st S) S\<close>

definition propagate_bt_wl_D
  :: \<open>nat literal \<Rightarrow> nat literal \<Rightarrow> nat twl_st_wl \<Rightarrow> nat twl_st_wl nres\<close>
where
  \<open>propagate_bt_wl_D = (\<lambda>L L' (M, N, D, NE, UE, Q, W). do {
    D'' \<leftarrow> list_of_mset2 (-L) L' (the D);
    i \<leftarrow> get_fresh_index_wl N (NE+UE) W;
    let b = (length D'' = 2);
    RETURN (Propagated (-L) i # M, fmupd i (D'', False) N,
          None, NE, UE, {#L#}, W(-L:= W (-L) @ [(i, L', b)], L':= W L' @ [(i, -L, b)]))
      })\<close>

definition propagate_unit_bt_wl_D
  :: \<open>nat literal \<Rightarrow> nat twl_st_wl \<Rightarrow> (nat twl_st_wl) nres\<close>
where
  \<open>propagate_unit_bt_wl_D = (\<lambda>L (M, N, D, NE, UE, Q, W). do {
        D' \<leftarrow> single_of_mset (the D);
        RETURN (Propagated (-L) 0 # M, N, None, NE, add_mset {#D'#} UE, {#L#}, W)
    })\<close>

definition backtrack_wl_D :: \<open>nat twl_st_wl \<Rightarrow> nat twl_st_wl nres\<close> where
  \<open>backtrack_wl_D S =
    do {
      ASSERT(backtrack_wl_D_inv S);
      let L = lit_of (hd (get_trail_wl S));
      S \<leftarrow> extract_shorter_conflict_wl S;
      S \<leftarrow> find_decomp_wl L S;

      if size (the (get_conflict_wl S)) > 1
      then do {
        L' \<leftarrow> find_lit_of_max_level_wl S L;
        propagate_bt_wl_D L L' S
      }
      else do {
        propagate_unit_bt_wl_D L S
     }
  }\<close>

lemma backtrack_wl_D_spec:
  fixes S :: \<open>nat twl_st_wl\<close>
  assumes \<A>\<^sub>i\<^sub>n: \<open>literals_are_\<L>\<^sub>i\<^sub>n \<A> S\<close> and confl: \<open>get_conflict_wl S \<noteq> None\<close>
  shows \<open>backtrack_wl_D S \<le>
     \<Down> {(T', T). T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n \<A> T}
       (backtrack_wl S)\<close>
proof -
  have 1: \<open>((get_conflict_wl S = Some {#}, S), get_conflict_wl S = Some {#}, S) \<in> Id\<close>
    by auto

  have 3: \<open>find_lit_of_max_level_wl S M \<le>
     \<Down>{(L', L). L' \<in># remove1_mset (-M) (the (get_conflict_wl S)) \<and> L' = L}
      (find_lit_of_max_level_wl S' M')\<close>
    if \<open>S = S'\<close> and \<open>M = M'\<close>
    for S S' :: \<open>nat twl_st_wl\<close> and M M'
    using that by (cases S; cases S') (auto simp: find_lit_of_max_level_wl_def intro!: RES_refine)
  have H: \<open>mset `# mset (take n (tl xs)) + a + (mset `# mset (drop (Suc n) xs) + b) =
   mset `# mset (tl xs) + a + b\<close> for n and xs :: \<open>'a list list\<close> and a b
    apply (subst (2) append_take_drop_id[of n \<open>tl xs\<close>, symmetric])
    apply (subst mset_append)
    by (auto simp: drop_Suc)
  have list_of_mset: \<open>list_of_mset2 L L' D \<le>
      \<Down> {(E, F). F = [L, L'] @ remove1 L (remove1 L' E) \<and> D = mset E \<and> E!0 = L \<and> E!1 = L' \<and> E=F}
        (list_of_mset D')\<close>
    (is \<open>_ \<le> \<Down> ?list_of_mset _\<close>)
    if \<open>D = D'\<close> and uL_D: \<open>L \<in># D\<close> and L'_D: \<open>L' \<in># D\<close> and L_uL': \<open>L \<noteq> L'\<close> for D D' L L'
    unfolding list_of_mset_def list_of_mset2_def
  proof (rule RES_refine)
    fix s
    assume s: \<open>s \<in> {E. mset E = D \<and> E ! 0 = L \<and> E ! 1 = L' \<and> length E \<ge> 2}\<close>
    then show \<open>\<exists>s'\<in>{D'a. D' = mset D'a}.
            (s, s')
            \<in> {(E, F).
                F = [L, L'] @ remove1 L (remove1 L' E) \<and> D = mset E \<and> E ! 0 = L \<and> E ! 1 = L'\<and> E=F}\<close>
      apply (cases s; cases \<open>tl s\<close>)
      using that by (auto simp: diff_single_eq_union diff_diff_add_mset[symmetric]
          simp del: diff_diff_add_mset)
  qed

  define extract_shorter_conflict_wl' where
    \<open>extract_shorter_conflict_wl' S = extract_shorter_conflict_wl S\<close> for S :: \<open>nat twl_st_wl\<close>
  define find_lit_of_max_level_wl' where
    \<open>find_lit_of_max_level_wl' S = find_lit_of_max_level_wl S\<close> for S :: \<open>nat twl_st_wl\<close>

  have extract_shorter_conflict_wl: \<open>extract_shorter_conflict_wl' S
    \<le> \<Down> {(U, U'). U = U' \<and> equality_except_conflict_wl U S \<and> get_conflict_wl U \<noteq> None \<and>
      the (get_conflict_wl U) \<subseteq># the (get_conflict_wl S) \<and>
      -lit_of (hd (get_trail_wl S)) \<in># the (get_conflict_wl U)
      } (extract_shorter_conflict_wl S)\<close>
    (is \<open>_ \<le> \<Down> ?extract_shorter _\<close>)
    unfolding extract_shorter_conflict_wl'_def extract_shorter_conflict_wl_def
    by (cases S)
      (auto 5 5 simp: extract_shorter_conflict_wl'_def extract_shorter_conflict_wl_def
       intro!: RES_refine)

  have find_decomp_wl: \<open>find_decomp_wl (lit_of (hd (get_trail_wl S))) T
    \<le> \<Down> {(U, U'). U = U' \<and> equality_except_trail_wl U T}
        (find_decomp_wl (lit_of (hd (get_trail_wl S))) T')\<close>
    (is \<open>_ \<le> \<Down> ?find_decomp _\<close>)
    if \<open>(T, T') \<in> ?extract_shorter\<close>
    for T T'
    using that unfolding find_decomp_wl_def
    by (cases T) (auto 5 5 intro!: RES_refine)

  have find_lit_of_max_level_wl:
    \<open>find_lit_of_max_level_wl U (lit_of (hd (get_trail_wl S)))
      \<le> \<Down> Id (find_lit_of_max_level_wl U' (lit_of (hd (get_trail_wl S))))\<close>
    if
      \<open>(U, U') \<in> ?find_decomp T\<close>
    for T U U'
    using that unfolding find_lit_of_max_level_wl_def
    by (cases T) (auto 5 5 intro!: RES_refine)

  have find_lit_of_max_level_wl':
     \<open>find_lit_of_max_level_wl' U (lit_of (hd (get_trail_wl S)))
        \<le> \<Down>{(L, L'). L = L' \<and> L \<in># remove1_mset (-lit_of (hd (get_trail_wl S))) (the (get_conflict_wl U))}
           (find_lit_of_max_level_wl U' (lit_of (hd (get_trail_wl S))))\<close>
      (is \<open>_ \<le> \<Down> ?find_lit _\<close>)
    if
      \<open>backtrack_wl_inv S\<close> and
      \<open>backtrack_wl_D_inv S\<close> and
      \<open>(U, U') \<in> ?find_decomp T\<close> and
      \<open>1 < size (the (get_conflict_wl U))\<close> and
      \<open>1 < size (the (get_conflict_wl U'))\<close>
    for U U' T
    using that unfolding find_lit_of_max_level_wl'_def find_lit_of_max_level_wl_def
    by (cases U) (auto 5 5 intro!: RES_refine)

  have is_\<L>\<^sub>a\<^sub>l\<^sub>l_add: \<open>is_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> (A + B) \<longleftrightarrow> set_mset A \<subseteq> set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close> if \<open>is_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> B\<close> for A B
    using that unfolding is_\<L>\<^sub>a\<^sub>l\<^sub>l_def by auto

  have propagate_bt_wl_D: \<open>propagate_bt_wl_D (lit_of (hd (get_trail_wl S))) L U
        \<le> \<Down> {(T', T). T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n \<A> T}
           (propagate_bt_wl (lit_of (hd (get_trail_wl S))) L' U')\<close>
    if
      \<open>backtrack_wl_inv S\<close> and
      bt: \<open>backtrack_wl_D_inv S\<close> and
      TT': \<open>(T, T') \<in> ?extract_shorter\<close> and
      UU': \<open>(U, U') \<in> ?find_decomp T\<close> and
      \<open>1 < size (the (get_conflict_wl U))\<close> and
      \<open>1 < size (the (get_conflict_wl U'))\<close> and
      LL': \<open>(L, L') \<in> ?find_lit U\<close>
    for L L' T T' U U'
  proof -
    obtain MS NS DS NES UES W Q where
       S: \<open>S = (MS, NS, Some DS, NES, UES, Q, W)\<close>
      using bt by (cases S; cases \<open>get_conflict_wl S\<close>)
        (auto simp: backtrack_wl_D_inv_def backtrack_wl_inv_def
          backtrack_l_inv_def state_wl_l_def)
    then obtain DT where
      T: \<open>T = (MS, NS, Some DT, NES, UES, Q, W)\<close> and DT: \<open>DT \<subseteq># DS\<close>
      using TT' by (cases T'; cases \<open>get_conflict_wl T'\<close>) auto
    then obtain MU where
      U: \<open>U = (MU, NS, Some DT, NES, UES, Q, W)\<close> and U': \<open>U' = U\<close>
      using UU' by (cases U) auto
    define list_of_mset where
      \<open>list_of_mset D L L' = ?list_of_mset D L L'\<close> for D and L L' :: \<open>nat literal\<close>
    have [simp]: \<open>get_conflict_wl S = Some DS\<close>
      using S by auto
    obtain T U where
      dist: \<open>distinct_mset (the (get_conflict_wl S))\<close> and
      ST: \<open>(S, T) \<in> state_wl_l None\<close> and
      TU: \<open>(T, U) \<in> twl_st_l None\<close> and
      alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of U)\<close>
      using bt unfolding backtrack_wl_D_inv_def backtrack_wl_inv_def backtrack_l_inv_def
      twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
      apply -
      apply normalize_goal+
      by (auto simp: twl_st_wl twl_st_l twl_st)

    then have \<open>distinct_mset DT\<close>
      using DT unfolding S by (auto simp: distinct_mset_mono)
    then have [simp]: \<open>L \<noteq> -lit_of (hd MS)\<close>
      using LL' by (auto simp: U S dest: distinct_mem_diff_mset)

    have \<open>x \<in># all_lits_of_m (the (get_conflict_wl S)) \<Longrightarrow>
        x \<in># all_lits_of_mm ({#mset x. x \<in># ran_mf (get_clauses_wl S)#} + get_unit_clauses_wl S)\<close>
      for x
      using alien ST TU unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def
      all_clss_lf_ran_m[symmetric] set_mset_union
      by (auto simp: twl_st_wl twl_st_l twl_st in_all_lits_of_m_ain_atms_of_iff
        in_all_lits_of_mm_ain_atms_of_iff get_unit_clauses_wl_alt_def)
    then have \<open>x \<in># all_lits_of_m DS \<Longrightarrow>
        x \<in># all_lits_of_mm ({#mset x. x \<in># ran_mf NS#} + (NES + UES))\<close>
      for x
      by (simp add: S)
    then have H: \<open>x \<in># all_lits_of_m DT \<Longrightarrow>
        x \<in># all_lits_of_mm ({#mset x. x \<in># ran_mf NS#} + (NES + UES))\<close>
      for x
      using DT all_lits_of_m_mono by blast
    have propa_ref: \<open>((Propagated (- lit_of (hd (get_trail_wl S))) i # MU, fmupd i (D, False) NS,
      None, NES, UES, unmark (hd (get_trail_wl S)), W
      (- lit_of (hd (get_trail_wl S)) :=
         W (- lit_of (hd (get_trail_wl S))) @ [(i, L, length D = 2)],
       L := W L @ [(i, -lit_of (hd (get_trail_wl S)), length D = 2)])),
     Propagated (- lit_of (hd (get_trail_wl S))) i' # MU,
     fmupd i'
      ([- lit_of (hd (get_trail_wl S)), L'] @
       remove1 (- lit_of (hd (get_trail_wl S))) (remove1 L' D'),
       False)
      NS,
     None, NES, UES, unmark (hd (get_trail_wl S)), W
     (- lit_of (hd (get_trail_wl S)) :=
        W (- lit_of (hd (get_trail_wl S))) @ [(i', L',
        length
           ([- lit_of (hd (get_trail_wl S)), L'] @
            remove1 (- lit_of (hd (get_trail_wl S))) (remove1 L' D')) =
          2)],
      L' := W L' @ [(i', - lit_of (hd (get_trail_wl S)),
        length
           ([- lit_of (hd (get_trail_wl S)), L'] @
            remove1 (- lit_of (hd (get_trail_wl S))) (remove1 L' D')) =
          2)]))
    \<in> {(T', T). T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n \<A> T}\<close>
      if
        DD': \<open>(D, D') \<in> list_of_mset (the (Some DT)) (- lit_of (hd (get_trail_wl S))) L\<close> and
        ii': \<open>(i, i') \<in> {(i, i'). i = i' \<and> i \<notin># dom_m NS}\<close>
      for i i' D D'
    proof -
      have [simp]: \<open>i = i'\<close> \<open>L = L'\<close> and i'_dom: \<open>i' \<notin># dom_m NS\<close>
        using ii' LL' by auto
      have
        D: \<open>D = [- lit_of (hd (get_trail_wl S)), L] @
          remove1 (- lit_of (hd (get_trail_wl S))) (remove1 L D')\<close> and
        DT_D: \<open>DT = mset D\<close>
        using DD' unfolding list_of_mset_def
        by force+
      have \<open>L \<in> set D\<close>
        using ii' LL' by (auto simp: U DT_D dest!: in_diffD)
      have K: \<open>L \<in> set D \<Longrightarrow> L \<in># all_lits_of_m (mset D)\<close> for L
        unfolding in_multiset_in_set[symmetric]
        apply (drule multi_member_split)
        by (auto simp: all_lits_of_m_add_mset)
      have [simp]: \<open>- lit_of (hd (get_trail_wl S)) # L' #
              remove1 (- lit_of (hd (get_trail_wl S))) (remove1 L' D') = D\<close>
        using D by simp
      then have 1[simp]: \<open>- lit_of (hd MS) # L' #
              remove1 (- lit_of (hd MS)) (remove1 L' D') = D\<close>
        using D by (simp add: S)
      have \<open>- lit_of (hd MS) \<in> set D\<close>
        apply (subst 1[symmetric])
        unfolding set_append list.sel
        by (rule list.set_intros)
      have \<open>set_mset (all_lits_of_m (mset D)) \<subseteq>
          set_mset (all_lits_of_mm ({#mset (fst x). x \<in># ran_m NS#} + (NES + UES)))\<close>
	by (auto dest!: H[unfolded DT_D])
      then have [simp]: \<open>is_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> (all_lits (fmupd i' (D, False) NS) (NES + UES)) =
          is_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> (all_lits NS (NES + UES))\<close>
	\<open>set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (atm_of `# all_lits (fmupd i' (D, False) NS) (NES + UES))) =
 	  set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (atm_of `# all_lits NS (NES + UES)))\<close>
	using i'_dom unfolding is_\<L>\<^sub>a\<^sub>l\<^sub>l_def all_lits_def
	by (auto 5 5 simp add: ran_m_mapsto_upd_notin all_lits_of_mm_add_mset
	  in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n atm_of_eq_atm_of)

      have \<open>x \<in># all_lits_of_mm ({#mset (fst x). x \<in># ran_m NS#} + (NES + UES)) \<Longrightarrow>
        x \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close> for x
        using i'_dom \<A>\<^sub>i\<^sub>n unfolding is_\<L>\<^sub>a\<^sub>l\<^sub>l_def literals_are_\<L>\<^sub>i\<^sub>n_def
	by (auto simp: S all_lits_def)
      then show ?thesis
        using i'_dom \<A>\<^sub>i\<^sub>n K[OF \<open>L \<in> set D\<close>] K[OF \<open>- lit_of (hd MS) \<in> set D\<close>]
	unfolding literals_are_\<L>\<^sub>i\<^sub>n_def
        by (auto simp: ran_m_mapsto_upd_notin all_lits_of_mm_add_mset
            blits_in_\<L>\<^sub>i\<^sub>n_def is_\<L>\<^sub>a\<^sub>l\<^sub>l_add S dest!: H[unfolded DT_D])
    qed

    define get_fresh_index2 where
      \<open>get_fresh_index2 N NUE W = get_fresh_index_wl (N :: nat clauses_l) (NUE :: nat clauses)
          (W::nat literal \<Rightarrow> (nat watcher) list)\<close>
      for N NUE W
    have fresh: \<open>get_fresh_index_wl N NUE W \<le> \<Down> {(i, i'). i = i' \<and> i \<notin># dom_m N} (get_fresh_index2 N' NUE' W')\<close>
      if \<open>N = N'\<close> \<open>NUE = NUE'\<close> \<open>W=W'\<close>for N N' NUE NUE' W W'
      using that by (auto simp: get_fresh_index_wl_def get_fresh_index2_def intro!: RES_refine)
    show ?thesis
      unfolding propagate_bt_wl_D_def propagate_bt_wl_def propagate_bt_wl_D_def U U' S T
      apply (subst (2) get_fresh_index2_def[symmetric])
      apply clarify
      apply (refine_rcg list_of_mset fresh)
      subgoal ..
      subgoal using TT' T by (auto simp: U S)
      subgoal using LL' by (auto simp: T U S dest: in_diffD)
      subgoal by auto
      subgoal ..
      subgoal ..
      subgoal ..
      subgoal for D D' i i'
        unfolding list_of_mset_def[symmetric] U[symmetric] U'[symmetric] S[symmetric] T[symmetric]
        by (rule propa_ref)
      done
  qed

  have propagate_unit_bt_wl_D: \<open>propagate_unit_bt_wl_D (lit_of (hd (get_trail_wl S))) U
    \<le> SPEC (\<lambda>c. (c, propagate_unit_bt_wl (lit_of (hd (get_trail_wl S))) U')
                 \<in> {(T', T). T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n \<A> T})\<close>
    if
      \<open>backtrack_wl_inv S\<close> and
      bt: \<open>backtrack_wl_D_inv S\<close> and
      TT': \<open>(T, T') \<in> ?extract_shorter\<close> and
      UU': \<open>(U, U') \<in> ?find_decomp T\<close> and
      \<open>\<not>1 < size (the (get_conflict_wl U))\<close> and
      \<open>\<not>1 < size (the (get_conflict_wl U'))\<close>
    for L L' T T' U U'
  proof -
    obtain MS NS DS NES UES W Q where
       S: \<open>S = (MS, NS, Some DS, NES, UES, Q, W)\<close>
      using bt by (cases S; cases \<open>get_conflict_wl S\<close>)
        (auto simp: backtrack_wl_D_inv_def backtrack_wl_inv_def
          backtrack_l_inv_def state_wl_l_def)
    then obtain DT where
      T: \<open>T = (MS, NS, Some DT, NES, UES, Q, W)\<close> and DT: \<open>DT \<subseteq># DS\<close>
      using TT' by (cases T'; cases \<open>get_conflict_wl T'\<close>) auto
    then obtain MU where
      U: \<open>U = (MU, NS, Some DT, NES, UES, Q, W)\<close> and U': \<open>U' = U\<close>
      using UU' by (cases U) auto
    define list_of_mset where
      \<open>list_of_mset D L L' = ?list_of_mset D L L'\<close> for D and L L' :: \<open>nat literal\<close>
    have [simp]: \<open>get_conflict_wl S = Some DS\<close>
      using S by auto
    obtain T U where
      dist: \<open>distinct_mset (the (get_conflict_wl S))\<close> and
      ST: \<open>(S, T) \<in> state_wl_l None\<close> and
      TU: \<open>(T, U) \<in> twl_st_l None\<close> and
      alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of U)\<close>
      using bt unfolding backtrack_wl_D_inv_def backtrack_wl_inv_def backtrack_l_inv_def
      twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
      apply -
      apply normalize_goal+
      by (auto simp: twl_st_wl twl_st_l twl_st)

    then have \<open>distinct_mset DT\<close>
      using DT unfolding S by (auto simp: distinct_mset_mono)
    have \<open>x \<in># all_lits_of_m (the (get_conflict_wl S)) \<Longrightarrow>
        x \<in># all_lits_of_mm ({#mset x. x \<in># ran_mf (get_clauses_wl S)#} + get_unit_init_clss_wl S)\<close>
      for x
      using alien ST TU unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def
      all_clss_lf_ran_m[symmetric] set_mset_union
      by (auto simp: twl_st_wl twl_st_l twl_st in_all_lits_of_m_ain_atms_of_iff
        in_all_lits_of_mm_ain_atms_of_iff)
    then have \<open>x \<in># all_lits_of_m DS \<Longrightarrow>
        x \<in># all_lits_of_mm ({#mset x. x \<in># ran_mf NS#} + NES)\<close>
      for x
      by (simp add: S)
    then have H: \<open>x \<in># all_lits_of_m DT \<Longrightarrow>
        x \<in># all_lits_of_mm ({#mset x. x \<in># ran_mf NS#} + NES)\<close>
      for x
      using DT all_lits_of_m_mono by blast
    then have \<A>\<^sub>i\<^sub>n_D: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A> DT\<close>
      using DT \<A>\<^sub>i\<^sub>n unfolding literals_are_in_\<L>\<^sub>i\<^sub>n_def S is_\<L>\<^sub>a\<^sub>l\<^sub>l_def literals_are_\<L>\<^sub>i\<^sub>n_def
      by (auto simp: all_lits_of_mm_union all_lits_def)
    have [simp]: \<open>is_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> (all_lits NS (add_mset {#x#} (NES + UES))) =
      is_\<L>\<^sub>a\<^sub>l\<^sub>l \<A> (all_lits NS (NES + UES))\<close>
      \<open>set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (atm_of `# all_lits NS (add_mset {#x#} (NES + UES)))) =
       set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (atm_of `# all_lits NS (NES + UES)))\<close>
      if \<open>DT = {#x#}\<close>
      for x
      using H[of x] H[of \<open>-x\<close>] that
      unfolding is_\<L>\<^sub>a\<^sub>l\<^sub>l_def all_lits_def
      by (auto simp add: all_lits_of_mm_add_mset in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n atm_of_eq_atm_of
        all_lits_of_m_add_mset insert_absorb all_lits_of_mm_union)

    show ?thesis
      unfolding propagate_unit_bt_wl_D_def propagate_unit_bt_wl_def U U' single_of_mset_def
      apply clarify
      apply refine_vcg
      using \<A>\<^sub>i\<^sub>n_D \<A>\<^sub>i\<^sub>n unfolding literals_are_\<L>\<^sub>i\<^sub>n_def
      by (auto simp: clauses_def mset_take_mset_drop_mset mset_take_mset_drop_mset'
          all_lits_of_mm_add_mset is_\<L>\<^sub>a\<^sub>l\<^sub>l_add literals_are_in_\<L>\<^sub>i\<^sub>n_def S
          blits_in_\<L>\<^sub>i\<^sub>n_def)
  qed
  show ?thesis
    unfolding backtrack_wl_D_def backtrack_wl_def find_lit_of_max_level_wl'_def
    apply (subst extract_shorter_conflict_wl'_def[symmetric])
    apply (subst find_lit_of_max_level_wl'_def[symmetric])
    supply [[goals_limit=1]]
    apply (refine_vcg extract_shorter_conflict_wl find_lit_of_max_level_wl find_decomp_wl
       find_lit_of_max_level_wl' propagate_bt_wl_D propagate_unit_bt_wl_D)
    subgoal using \<A>\<^sub>i\<^sub>n unfolding backtrack_wl_D_inv_def by fast
    subgoal by auto
    by assumption+
qed


subsubsection \<open>Decide or Skip\<close>

definition find_unassigned_lit_wl_D
  :: \<open>nat twl_st_wl \<Rightarrow> (nat twl_st_wl \<times> nat literal option) nres\<close>
where
  \<open>find_unassigned_lit_wl_D S = (
     SPEC(\<lambda>((M, N, D, NE, UE, WS, Q), L).
         S = (M, N, D, NE, UE, WS, Q) \<and>
         (L \<noteq> None \<longrightarrow>
            undefined_lit M (the L) \<and> the L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms N NE) \<and>
            atm_of (the L) \<in> atms_of_mm (clause `# twl_clause_of `# init_clss_lf N + NE)) \<and>
         (L = None \<longrightarrow> (\<nexists>L'. undefined_lit M L' \<and>
            atm_of L' \<in> atms_of_mm (clause `# twl_clause_of `# init_clss_lf N + NE)))))
\<close>


definition decide_wl_or_skip_D_pre :: \<open>nat twl_st_wl \<Rightarrow> bool\<close> where
\<open>decide_wl_or_skip_D_pre S \<longleftrightarrow>
   decide_wl_or_skip_pre S \<and> literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st S) S\<close>

definition decide_wl_or_skip_D
  :: \<open>nat twl_st_wl \<Rightarrow> (bool \<times> nat twl_st_wl) nres\<close>
where
  \<open>decide_wl_or_skip_D S = (do {
    ASSERT(decide_wl_or_skip_D_pre S);
    (S, L) \<leftarrow> find_unassigned_lit_wl_D S;
    case L of
      None \<Rightarrow> RETURN (True, S)
    | Some L \<Rightarrow> RETURN (False, decide_lit_wl L S)
  })
\<close>

theorem decide_wl_or_skip_D_spec:
  assumes \<open>literals_are_\<L>\<^sub>i\<^sub>n \<A> S\<close>
  shows \<open>decide_wl_or_skip_D S
    \<le> \<Down> {((b', T'), b, T). b = b' \<and> T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n \<A> T} (decide_wl_or_skip S)\<close>
proof -
  have H: \<open>find_unassigned_lit_wl_D S \<le> \<Down> {((S', L'), L). S' = S \<and> L = L' \<and> literals_are_\<L>\<^sub>i\<^sub>n \<A> S \<and>
         (L \<noteq> None \<longrightarrow>
            undefined_lit (get_trail_wl S) (the L) \<and>
            atm_of (the L) \<in> atms_of_mm (clause `# twl_clause_of `# init_clss_lf (get_clauses_wl S)
                 + get_unit_init_clss_wl S)) \<and>
         (L = None \<longrightarrow> (\<nexists>L'. undefined_lit (get_trail_wl S) L' \<and>
            atm_of L' \<in> atms_of_mm (clause `# twl_clause_of `# init_clss_lf (get_clauses_wl S)
                 + get_unit_init_clss_wl S)))}
     (find_unassigned_lit_wl S')\<close>
    (is \<open>_ \<le> \<Down> ?find _\<close>)
    if \<open>S = S'\<close> and \<open>literals_are_\<L>\<^sub>i\<^sub>n \<A> S\<close>
    for S S' :: \<open>nat twl_st_wl\<close>
    using that(2) unfolding find_unassigned_lit_wl_def find_unassigned_lit_wl_D_def that(1)
    by (cases S') (auto intro!: RES_refine simp: mset_take_mset_drop_mset')
  have [refine]: \<open>x = x' \<Longrightarrow> (x, x') \<in> \<langle>Id\<rangle> option_rel\<close>
    for x x' by auto
  have decide_lit_wl: \<open>((False, decide_lit_wl L T), False, decide_lit_wl L' S')
        \<in> {((b', T'), b, T).
            b = b' \<and> T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n \<A> T}\<close>
    if
      SS': \<open>(S, S') \<in> {(T', T). T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n \<A> T}\<close> and
      \<open>decide_wl_or_skip_pre S'\<close> and
      pre: \<open>decide_wl_or_skip_D_pre S\<close> and
      LT_L': \<open>(LT, bL') \<in> ?find S\<close> and
      LT: \<open>LT = (T, bL)\<close> and
      \<open>bL' = Some L'\<close> and
      \<open>bL = Some L\<close> and
      LL': \<open>(L, L') \<in> Id\<close>
    for S S' L L' LT bL bL' T
  proof -
    have \<A>\<^sub>i\<^sub>n: \<open>literals_are_\<L>\<^sub>i\<^sub>n \<A> T\<close> and [simp]: \<open>T = S\<close>
      using LT_L' pre unfolding LT decide_wl_or_skip_D_pre_def
   by fast+
    have [simp]: \<open>S' = S\<close> \<open>L = L'\<close>
      using SS' LL' by simp_all
    have \<open>literals_are_\<L>\<^sub>i\<^sub>n \<A> (decide_lit_wl L' S)\<close>
      using \<A>\<^sub>i\<^sub>n
      by (cases S) (auto simp: decide_lit_wl_def clauses_def blits_in_\<L>\<^sub>i\<^sub>n_def
          literals_are_\<L>\<^sub>i\<^sub>n_def)
    then show ?thesis
      by auto
  qed

  have \<open>(decide_wl_or_skip_D, decide_wl_or_skip) \<in> {(T', T).  T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n \<A> T} \<rightarrow>\<^sub>f
     \<langle>{((b', T'), (b, T)). b = b' \<and> T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n \<A> T}\<rangle> nres_rel\<close>
    unfolding decide_wl_or_skip_D_def decide_wl_or_skip_def
    apply (intro frefI)
    apply (refine_vcg H)
    subgoal unfolding decide_wl_or_skip_D_pre_def by blast
    subgoal by simp
    subgoal by auto
    subgoal by simp
    subgoal unfolding decide_wl_or_skip_D_pre_def by fast
    subgoal by (rule decide_lit_wl) assumption+
    done
  then show ?thesis
    using assms by (cases S) (auto simp: fref_def nres_rel_def)
qed


subsubsection \<open>Backtrack, Skip, Resolve or Decide\<close>

definition cdcl_twl_o_prog_wl_D_pre where
\<open>cdcl_twl_o_prog_wl_D_pre S \<longleftrightarrow> cdcl_twl_o_prog_wl_pre S \<and> literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st S) S\<close>

definition cdcl_twl_o_prog_wl_D
 :: \<open>nat twl_st_wl \<Rightarrow> (bool \<times> nat twl_st_wl) nres\<close>
where
  \<open>cdcl_twl_o_prog_wl_D S =
    do {
      ASSERT(cdcl_twl_o_prog_wl_D_pre S);
      if get_conflict_wl S = None
      then decide_wl_or_skip_D S
      else do {
        if count_decided (get_trail_wl S) > 0
        then do {
          T \<leftarrow> skip_and_resolve_loop_wl_D S;
          ASSERT(get_conflict_wl T \<noteq> None \<and> get_clauses_wl S = get_clauses_wl T);
          U \<leftarrow> backtrack_wl_D T;
          RETURN (False, U)
        }
        else RETURN (True, S)
      }
    }
  \<close>

theorem cdcl_twl_o_prog_wl_D_spec:
  assumes \<open>literals_are_\<L>\<^sub>i\<^sub>n \<A> S\<close>
  shows \<open>cdcl_twl_o_prog_wl_D S \<le> \<Down> {((b', T'), (b, T)). b = b' \<and> T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n \<A> T}
     (cdcl_twl_o_prog_wl S)\<close>
proof -
  have 1: \<open>backtrack_wl_D S \<le>
     \<Down> {(T', T). T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n \<A> T}
       (backtrack_wl T)\<close> if \<open>literals_are_\<L>\<^sub>i\<^sub>n \<A> S\<close> and \<open>get_conflict_wl S \<noteq> None\<close> and \<open>S = T\<close>
    for S T
    using backtrack_wl_D_spec[of \<A> S] that by fast
  have 2: \<open>skip_and_resolve_loop_wl_D S \<le>
     \<Down> {(T', T). T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n \<A> T \<and>  get_clauses_wl T = get_clauses_wl S}
        (skip_and_resolve_loop_wl T)\<close>
    if \<A>\<^sub>i\<^sub>n: \<open>literals_are_\<L>\<^sub>i\<^sub>n \<A> S\<close> \<open>S = T\<close>
    for S T
    using skip_and_resolve_loop_wl_D_spec[of \<A> S] that by fast
  show ?thesis
    using assms
    unfolding cdcl_twl_o_prog_wl_D_def cdcl_twl_o_prog_wl_def
    apply (refine_vcg decide_wl_or_skip_D_spec 1 2)
    subgoal unfolding cdcl_twl_o_prog_wl_D_pre_def by auto
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by simp
    subgoal by auto
    subgoal by auto
    done
qed

theorem cdcl_twl_o_prog_wl_D_spec':
  \<open>(cdcl_twl_o_prog_wl_D, cdcl_twl_o_prog_wl) \<in>
    {(S,S'). (S,S') \<in> Id \<and>literals_are_\<L>\<^sub>i\<^sub>n \<A> S} \<rightarrow>\<^sub>f
    \<langle>bool_rel \<times>\<^sub>r {(T', T). T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n \<A> T}\<rangle> nres_rel\<close>
  apply (intro frefI nres_relI)
  subgoal for x y
    apply (rule order_trans)
    apply (rule cdcl_twl_o_prog_wl_D_spec[of \<A> x])
     apply (auto simp: prod_rel_def intro: conc_fun_R_mono)
    done
  done


subsubsection \<open>Full Strategy\<close>

definition cdcl_twl_stgy_prog_wl_D
   :: \<open>nat twl_st_wl \<Rightarrow> nat twl_st_wl nres\<close>
where
  \<open>cdcl_twl_stgy_prog_wl_D S\<^sub>0 =
  do {
    do {
      (brk, T) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(brk, T). cdcl_twl_stgy_prog_wl_inv S\<^sub>0 (brk, T) \<and>
          literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st T) T\<^esup>
        (\<lambda>(brk, _). \<not>brk)
        (\<lambda>(brk, S).
        do {
          T \<leftarrow> unit_propagation_outer_loop_wl_D S;
          cdcl_twl_o_prog_wl_D T
        })
        (False, S\<^sub>0);
      RETURN T
    }
  }
  \<close>

theorem cdcl_twl_stgy_prog_wl_D_spec:
  assumes \<open>literals_are_\<L>\<^sub>i\<^sub>n \<A> S\<close>
  shows \<open>cdcl_twl_stgy_prog_wl_D S \<le> \<Down> {(T', T). T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n \<A> T}
     (cdcl_twl_stgy_prog_wl S)\<close>
proof -
  have 1: \<open>((False, S), False, S) \<in> {((brk', T'), brk, T). brk = brk' \<and> T = T' \<and>
      literals_are_\<L>\<^sub>i\<^sub>n \<A> T}\<close>
    using assms by fast
  have 2: \<open>unit_propagation_outer_loop_wl_D S \<le> \<Down> {(T', T). T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n \<A> T}
       (unit_propagation_outer_loop_wl T)\<close> if \<open>S = T\<close> \<open>literals_are_\<L>\<^sub>i\<^sub>n \<A> S\<close> for S T
    using unit_propagation_outer_loop_wl_D_spec[of \<A> S] that by fast
  have 3: \<open>cdcl_twl_o_prog_wl_D S \<le> \<Down> {((b', T'), b, T). b = b' \<and> T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n \<A> T}
    (cdcl_twl_o_prog_wl T)\<close> if \<open>S = T\<close> \<open>literals_are_\<L>\<^sub>i\<^sub>n \<A> S\<close> for S T
    using cdcl_twl_o_prog_wl_D_spec[of \<A> S] that by fast
  show ?thesis
    unfolding cdcl_twl_stgy_prog_wl_D_def cdcl_twl_stgy_prog_wl_def
    apply (refine_vcg 1 2 3)
    subgoal by auto
    subgoal by auto
    subgoal by fast
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

lemma cdcl_twl_stgy_prog_wl_D_spec':
  \<open>(cdcl_twl_stgy_prog_wl_D, cdcl_twl_stgy_prog_wl) \<in>
    {(S,S'). (S,S') \<in> Id \<and>literals_are_\<L>\<^sub>i\<^sub>n \<A> S} \<rightarrow>\<^sub>f
    \<langle>{(T', T). T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n \<A> T}\<rangle> nres_rel\<close>
  by (intro frefI nres_relI)
    (auto intro: cdcl_twl_stgy_prog_wl_D_spec)

definition cdcl_twl_stgy_prog_wl_D_pre where
  \<open>cdcl_twl_stgy_prog_wl_D_pre S U \<longleftrightarrow>
    (cdcl_twl_stgy_prog_wl_pre S U \<and> literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st S) S)\<close>

lemma cdcl_twl_stgy_prog_wl_D_spec_final:
  assumes
    \<open>cdcl_twl_stgy_prog_wl_D_pre S S'\<close>
  shows
    \<open>cdcl_twl_stgy_prog_wl_D S \<le> \<Down> (state_wl_l None O twl_st_l None) (conclusive_TWL_run S')\<close>
proof -
  have T: \<open>cdcl_twl_stgy_prog_wl_pre S S' \<and> literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st S) S\<close>
    using assms unfolding cdcl_twl_stgy_prog_wl_D_pre_def by blast
  show ?thesis
    apply (rule order_trans[OF cdcl_twl_stgy_prog_wl_D_spec[of \<open>all_atms_st S\<close>]])
    subgoal using T by auto
    subgoal
      apply (rule order_trans)
      apply (rule ref_two_step')
       apply (rule cdcl_twl_stgy_prog_wl_spec_final[of _ S'])
      subgoal using T by fast
      subgoal unfolding conc_fun_chain by (rule conc_fun_R_mono) blast
      done
    done
qed


definition cdcl_twl_stgy_prog_break_wl_D :: \<open>nat twl_st_wl \<Rightarrow> nat twl_st_wl nres\<close>
where
  \<open>cdcl_twl_stgy_prog_break_wl_D S\<^sub>0 =
  do {
    b \<leftarrow> SPEC (\<lambda>_. True);
    (b, brk, T) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(b, brk, T). cdcl_twl_stgy_prog_wl_inv S\<^sub>0 (brk, T) \<and>
          literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st T) T\<^esup>
        (\<lambda>(b, brk, _). b \<and> \<not>brk)
        (\<lambda>(b, brk, S).
        do {
          ASSERT(b);
          T \<leftarrow> unit_propagation_outer_loop_wl_D S;
          (brk, T) \<leftarrow> cdcl_twl_o_prog_wl_D T;
          b \<leftarrow> SPEC (\<lambda>_. True);
          RETURN(b, brk, T)
        })
        (b, False, S\<^sub>0);
    if brk then RETURN T
    else cdcl_twl_stgy_prog_wl_D T
  }\<close>

theorem cdcl_twl_stgy_prog_break_wl_D_spec:
  assumes \<open>literals_are_\<L>\<^sub>i\<^sub>n \<A> S\<close>
  shows \<open>cdcl_twl_stgy_prog_break_wl_D S \<le> \<Down> {(T', T). T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n \<A> T}
     (cdcl_twl_stgy_prog_break_wl S)\<close>
proof -
  define f where \<open>f \<equiv> SPEC (\<lambda>_::bool. True)\<close>
  have 1: \<open>((b, False, S), b, False, S) \<in> {((b', brk', T'), b, brk, T). b = b' \<and> brk = brk' \<and>
        T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n \<A> T}\<close>
    for b
    using assms by fast
  have 1: \<open>((b, False, S), b', False, S) \<in> {((b', brk', T'), b, brk, T). b = b' \<and> brk = brk' \<and>
        T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n \<A> T}\<close>
    if \<open>(b, b') \<in> bool_rel\<close>
    for b b'
    using assms that by fast

  have 2: \<open>unit_propagation_outer_loop_wl_D S \<le> \<Down> {(T', T). T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n \<A> T}
       (unit_propagation_outer_loop_wl T)\<close> if \<open>S = T\<close> \<open>literals_are_\<L>\<^sub>i\<^sub>n \<A> S\<close> for S T
    using unit_propagation_outer_loop_wl_D_spec[of \<A> S] that by fast
  have 3: \<open>cdcl_twl_o_prog_wl_D S \<le> \<Down> {((b', T'), b, T). b = b' \<and> T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n \<A> T}
    (cdcl_twl_o_prog_wl T)\<close> if \<open>S = T\<close> \<open>literals_are_\<L>\<^sub>i\<^sub>n \<A> S\<close> for S T
    using cdcl_twl_o_prog_wl_D_spec[of \<A> S] that by fast
  show ?thesis
    unfolding cdcl_twl_stgy_prog_break_wl_D_def cdcl_twl_stgy_prog_break_wl_def f_def[symmetric]
    apply (refine_vcg 1 2 3)
    subgoal by auto
    subgoal by fast
    subgoal by fast
    subgoal by fast
    subgoal by fast
    subgoal by fast
    subgoal by fast
    subgoal by fast
    subgoal by fast
    subgoal by fast
    subgoal by fast
    subgoal by (fast intro!: cdcl_twl_stgy_prog_wl_D_spec)
    done
qed

lemma cdcl_twl_stgy_prog_break_wl_D_spec_final:
  assumes
    \<open>cdcl_twl_stgy_prog_wl_D_pre S S'\<close>
  shows
    \<open>cdcl_twl_stgy_prog_break_wl_D S \<le> \<Down> (state_wl_l None O twl_st_l None) (conclusive_TWL_run S')\<close>
proof -
  have T: \<open>cdcl_twl_stgy_prog_wl_pre S S' \<and> literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st S) S\<close>
    using assms unfolding cdcl_twl_stgy_prog_wl_D_pre_def by blast
  show ?thesis
    apply (rule order_trans[OF cdcl_twl_stgy_prog_break_wl_D_spec[of \<open>all_atms_st S\<close>]])
    subgoal using T by auto
    subgoal
      apply (rule order_trans)
      apply (rule ref_two_step')
       apply (rule cdcl_twl_stgy_prog_break_wl_spec_final[of _ S'])
      subgoal using T by fast
      subgoal unfolding conc_fun_chain by (rule conc_fun_R_mono) blast
      done
    done
qed


definition cdcl_twl_stgy_prog_early_wl_D :: \<open>nat twl_st_wl \<Rightarrow> (bool \<times> nat twl_st_wl) nres\<close>
where
  \<open>cdcl_twl_stgy_prog_early_wl_D S\<^sub>0 =
  do {
    b \<leftarrow> SPEC (\<lambda>_. True);
    (b, brk, T) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(b, brk, T). cdcl_twl_stgy_prog_wl_inv S\<^sub>0 (brk, T) \<and>
          literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st T) T\<^esup>
        (\<lambda>(b, brk, _). b \<and> \<not>brk)
        (\<lambda>(b, brk, S).
        do {
          ASSERT(b);
          ASSERT(\<not>brk);
          T \<leftarrow> unit_propagation_outer_loop_wl_D S;
          (brk, T) \<leftarrow> cdcl_twl_o_prog_wl_D T;
          b \<leftarrow> SPEC (\<lambda>_. True);
          RETURN(b, brk, T)
        })
        (b, False, S\<^sub>0);
    RETURN (brk ,T)
  }\<close>

theorem cdcl_twl_stgy_prog_early_wl_D_spec:
  assumes \<open>literals_are_\<L>\<^sub>i\<^sub>n \<A> S\<close>
  shows \<open>cdcl_twl_stgy_prog_early_wl_D S \<le> \<Down> (bool_rel \<times>\<^sub>r {(T', T). T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n \<A> T})
     (cdcl_twl_stgy_prog_early_wl S)\<close>
proof -
  define f where \<open>f \<equiv> SPEC (\<lambda>_::bool. True)\<close>
  have 1: \<open>((b, False, S), b, False, S) \<in> {((b', brk', T'), b, brk, T). b = b' \<and> brk = brk' \<and>
        T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n \<A> T}\<close>
    for b
    using assms by fast
  have 1: \<open>((b, False, S), b', False, S) \<in> {((b', brk', T'), b, brk, T). b = b' \<and> brk = brk' \<and>
        T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n \<A> T}\<close>
    if \<open>(b, b') \<in> bool_rel\<close>
    for b b'
    using assms that by fast

  have 2: \<open>unit_propagation_outer_loop_wl_D S \<le> \<Down> {(T', T). T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n \<A> T}
       (unit_propagation_outer_loop_wl T)\<close> if \<open>S = T\<close> \<open>literals_are_\<L>\<^sub>i\<^sub>n \<A> S\<close> for S T
    using unit_propagation_outer_loop_wl_D_spec[of \<A> S] that by fast
  have 3: \<open>cdcl_twl_o_prog_wl_D S \<le> \<Down> {((b', T'), b, T). b = b' \<and> T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n \<A> T}
    (cdcl_twl_o_prog_wl T)\<close> if \<open>S = T\<close> \<open>literals_are_\<L>\<^sub>i\<^sub>n \<A> S\<close> for S T
    using cdcl_twl_o_prog_wl_D_spec[of \<A> S] that by fast
  show ?thesis
    unfolding cdcl_twl_stgy_prog_early_wl_D_def cdcl_twl_stgy_prog_early_wl_def f_def[symmetric]
    apply (refine_vcg 1 2 3)
    subgoal by auto
    subgoal by fast
    subgoal by fast
    subgoal by fast
    subgoal by fast
    subgoal by fast
    subgoal by fast
    subgoal by fast
    subgoal by fast
    subgoal by auto
    subgoal by auto
    done
qed

lemma cdcl_twl_stgy_prog_early_wl_D_spec_final:
  assumes
    \<open>cdcl_twl_stgy_prog_wl_D_pre S S'\<close>
  shows
    \<open>cdcl_twl_stgy_prog_early_wl_D S \<le> \<Down> (bool_rel \<times>\<^sub>r (state_wl_l None O twl_st_l None)) (partial_conclusive_TWL_run S')\<close>
proof -
  have T: \<open>cdcl_twl_stgy_prog_wl_pre S S' \<and> literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st S) S\<close>
    using assms unfolding cdcl_twl_stgy_prog_wl_D_pre_def by blast
  show ?thesis
    apply (rule order_trans[OF cdcl_twl_stgy_prog_early_wl_D_spec[of \<open>all_atms_st S\<close>]])
    subgoal using T by auto
    subgoal
      apply (rule order_trans)
      apply (rule ref_two_step')
       apply (rule cdcl_twl_stgy_prog_early_wl_spec_final[of _ S'])
      subgoal using T by fast
      subgoal unfolding conc_fun_chain by (rule conc_fun_R_mono) fastforce
      done
    done
qed

text \<open>The definition is here to be shared later.\<close>
definition get_propagation_reason :: \<open>('v, 'mark) ann_lits \<Rightarrow> 'v literal \<Rightarrow> 'mark option nres\<close> where
  \<open>get_propagation_reason M L = SPEC(\<lambda>C. C \<noteq> None \<longrightarrow> Propagated L (the C) \<in> set M)\<close>

end
