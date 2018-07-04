theory IsaSAT_Arena
imports IsaSAT_Setup
begin

text \<open>The order in memory is in the following order:
  \<^enum> the saved position (is optional in cadical);
  \<^enum> the status;
  \<^enum> the activity;
  \<^enum> the LBD;
  \<^enum> the size;
  \<^enum> the clause.

Remark that the information can be compressed to reduce the size in memory:
  \<^enum> the saved position can be skipped for short clauses;
  \<^enum> the LBD will most of the time be much shorter than a 32-bit integer, so only an
    approximation can be kept and the remaining bits be reused;
  \<^enum> the activity is not kept by cadical (to use instead a MTF-like scheme). 

As we are alredy wasteful with memory, we implement the first optimisation.
\<close>

definition POS_SHIFT :: nat where
  \<open>POS_SHIFT = 5\<close>

definition STATUS_SHIFT :: nat where
  \<open>STATUS_SHIFT = 4\<close>

definition ACTIVITY_SHIFT :: nat where
  \<open>ACTIVITY_SHIFT = 3\<close>

definition LBD_SHIFT :: nat where
  \<open>LBD_SHIFT = 2\<close>

definition SIZE_SHIFT :: nat where
  \<open>SIZE_SHIFT = 1\<close>

definition is_short_clause where
\<open>is_short_clause C \<longleftrightarrow> length C \<le> 5\<close>

abbreviation is_long_clause where
\<open>is_long_clause C \<equiv> \<not>is_short_clause C\<close>

definition header_size where
\<open>header_size C = (if is_short_clause C then 4 else 5)\<close>

lemma arena_shift_distinct[simp]:
  \<open>i >  3 \<Longrightarrow> i - SIZE_SHIFT \<noteq> i - LBD_SHIFT\<close>
  \<open>i >  3 \<Longrightarrow> i - SIZE_SHIFT \<noteq> i - ACTIVITY_SHIFT\<close>
  \<open>i >  3 \<Longrightarrow> i - SIZE_SHIFT \<noteq> i - STATUS_SHIFT\<close>
  \<open>i >  3 \<Longrightarrow> i - LBD_SHIFT \<noteq> i - ACTIVITY_SHIFT\<close>
  \<open>i >  3 \<Longrightarrow> i - LBD_SHIFT \<noteq> i - STATUS_SHIFT\<close>
  \<open>i >  3 \<Longrightarrow> i - ACTIVITY_SHIFT \<noteq> i - STATUS_SHIFT\<close>

  \<open>i >  4 \<Longrightarrow> i - SIZE_SHIFT \<noteq> i - POS_SHIFT\<close>
  \<open>i >  4 \<Longrightarrow> i - LBD_SHIFT \<noteq> i - POS_SHIFT\<close>
  \<open>i >  4 \<Longrightarrow> i - ACTIVITY_SHIFT \<noteq> i - POS_SHIFT\<close>
  \<open>i >  4 \<Longrightarrow> i - STATUS_SHIFT \<noteq> i - POS_SHIFT\<close>


  \<open>i >  3 \<Longrightarrow> j >  3 \<Longrightarrow> i - SIZE_SHIFT = j - SIZE_SHIFT \<longleftrightarrow> i = j\<close>
  \<open>i >  3 \<Longrightarrow> j >  3 \<Longrightarrow> i - LBD_SHIFT = j - LBD_SHIFT \<longleftrightarrow> i = j\<close>
  \<open>i >  4 \<Longrightarrow> j >  4 \<Longrightarrow> i - ACTIVITY_SHIFT = j - ACTIVITY_SHIFT \<longleftrightarrow> i = j\<close>
  \<open>i >  3 \<Longrightarrow> j >  3 \<Longrightarrow> i - STATUS_SHIFT = j - STATUS_SHIFT \<longleftrightarrow> i = j\<close>
  \<open>i >  4 \<Longrightarrow> j >  4 \<Longrightarrow> i - POS_SHIFT = j - POS_SHIFT \<longleftrightarrow> i = j\<close>

  \<open>i \<ge>  header_size C \<Longrightarrow> i - SIZE_SHIFT \<noteq> i - LBD_SHIFT\<close>
  \<open>i  \<ge>  header_size C \<Longrightarrow> i - SIZE_SHIFT \<noteq> i - ACTIVITY_SHIFT\<close>
  \<open>i  \<ge>  header_size C \<Longrightarrow> i - SIZE_SHIFT \<noteq> i - STATUS_SHIFT\<close>
  \<open>i  \<ge>  header_size C \<Longrightarrow> i - LBD_SHIFT \<noteq> i - ACTIVITY_SHIFT\<close>
  \<open>i  \<ge>  header_size C \<Longrightarrow> i - LBD_SHIFT \<noteq> i - STATUS_SHIFT\<close>
  \<open>i  \<ge>  header_size C \<Longrightarrow> i - ACTIVITY_SHIFT \<noteq> i - STATUS_SHIFT\<close>

  \<open>i \<ge> header_size C \<Longrightarrow> is_long_clause C \<Longrightarrow> i - SIZE_SHIFT \<noteq> i - POS_SHIFT\<close>
  \<open>i \<ge> header_size C \<Longrightarrow> is_long_clause C \<Longrightarrow> i - LBD_SHIFT \<noteq> i - POS_SHIFT\<close>
  \<open>i \<ge> header_size C \<Longrightarrow> is_long_clause C \<Longrightarrow> i - ACTIVITY_SHIFT \<noteq> i - POS_SHIFT\<close>
  \<open>i \<ge> header_size C \<Longrightarrow> is_long_clause C \<Longrightarrow> i - STATUS_SHIFT \<noteq> i - POS_SHIFT\<close>


  \<open>i \<ge> header_size C \<Longrightarrow> j \<ge> header_size C' \<Longrightarrow> i - SIZE_SHIFT = j - SIZE_SHIFT \<longleftrightarrow> i = j\<close>
  \<open>i \<ge> header_size C \<Longrightarrow> j \<ge> header_size C' \<Longrightarrow> i - LBD_SHIFT = j - LBD_SHIFT \<longleftrightarrow> i = j\<close>
  \<open>i \<ge> header_size C \<Longrightarrow> j \<ge> header_size C' \<Longrightarrow> i - ACTIVITY_SHIFT = j - ACTIVITY_SHIFT \<longleftrightarrow> i = j\<close>
  \<open>i \<ge> header_size C \<Longrightarrow> j \<ge> header_size C' \<Longrightarrow> i - STATUS_SHIFT = j - STATUS_SHIFT \<longleftrightarrow> i = j\<close>
  \<open>i \<ge> header_size C \<Longrightarrow> j \<ge> header_size C' \<Longrightarrow> is_long_clause C \<Longrightarrow> is_long_clause C' \<Longrightarrow> i - POS_SHIFT = j - POS_SHIFT \<longleftrightarrow> i = j\<close>
  unfolding POS_SHIFT_def STATUS_SHIFT_def ACTIVITY_SHIFT_def LBD_SHIFT_def SIZE_SHIFT_def
    header_size_def
  by (auto split: if_splits simp: is_short_clause_def)


datatype arena_el =
  is_Lit: ALit (arena_lit: \<open>nat literal\<close>) |
  is_LBD: ALBD (arena_lbd: nat) |
  is_Act: AActivity (arena_act: nat) |
  is_Size: ASize (arena_size: nat)  |
  is_Pos: APos (arena_pos: nat)  |
  is_Status: AStatus (arena_status: clause_status)

type_synonym arena = \<open>arena_el list\<close>


definition extra_information_dom :: \<open>arena \<Rightarrow> (nat, nat literal list \<times> bool) fmap \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>extra_information_dom arena N i \<longleftrightarrow>
     (i \<ge> header_size (N \<propto> i) \<and> i \<in># dom_m N \<and> length (N \<propto> i) \<ge> 2 \<and>
       i + length (N\<propto>i) \<le> length arena \<and>
     (is_long_clause (N\<propto>i) \<longrightarrow> (is_Pos (arena!(i - POS_SHIFT)) \<and>
       arena_pos(arena!(i - POS_SHIFT)) < length (N \<propto> i) - 2)) \<and>
     is_Status(arena!(i - STATUS_SHIFT)) \<and> 
        (arena_status(arena!(i - STATUS_SHIFT)) = INIT \<longleftrightarrow> irred N i) \<and> 
        (arena_status(arena!(i - STATUS_SHIFT)) = LEARNED \<longleftrightarrow> \<not>irred N i) \<and>
     is_LBD(arena!(i - LBD_SHIFT)) \<and> 
     is_Act(arena!(i - ACTIVITY_SHIFT)) \<and> 
     is_Size(arena!(i - SIZE_SHIFT)) \<and> arena_size(arena!(i - SIZE_SHIFT)) + 2 = length(N\<propto>i) \<and>
     take (length (N\<propto>i)) (drop i arena) = map ALit (N\<propto> i)
  )\<close>


definition extra_information_vdom :: \<open>arena \<Rightarrow> (nat, nat literal list \<times> bool) fmap \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>extra_information_vdom arena N i \<longleftrightarrow>
     i \<ge> 4 \<and> i \<notin># dom_m N \<and> i < length arena \<and>
     is_Status(arena!(i - STATUS_SHIFT)) \<and> arena_status(arena!(i - STATUS_SHIFT)) = DELETED
\<close>

definition extra_information_mark_to_delete where
  \<open>extra_information_mark_to_delete arena i = arena[i - STATUS_SHIFT := AStatus DELETED]\<close>

definition valid_arena where
  \<open>valid_arena arena N vdom \<longleftrightarrow>
    (\<forall>i \<in># dom_m N. extra_information_dom arena N i) \<and>
    (\<forall>i \<in> vdom. i \<notin># dom_m N \<longrightarrow> extra_information_vdom arena N i)
\<close>

lemma minimal_difference_between_valid_index:
  assumes  \<open>Multiset.Ball (dom_m N) (extra_information_dom arena N)\<close> and
    \<open>i \<in># dom_m N\<close> and \<open>j \<in># dom_m N\<close> and \<open>j > i\<close>
  shows \<open>j - i \<ge> length (N\<propto>i) + header_size (N\<propto>j)\<close>
proof (rule ccontr)
  assume False: \<open>\<not> ?thesis\<close>
  have 
    1: \<open>extra_information_dom arena N i\<close> and 
    2: \<open>extra_information_dom arena N j\<close> 
    using assms 
    by auto
  
  have eq: \<open>take (length (N \<propto> i)) (drop i arena) = map ALit (N \<propto> i)\<close> and
    \<open>length (N \<propto> i) - Suc 0 < length (N \<propto> i)\<close> and
    i_le: \<open>i < length arena\<close> and
    i_ge: \<open>i \<ge> header_size(N\<propto>i)\<close> and
    length_Ni: \<open>length (N\<propto>i) \<ge> 2\<close>
    using 1 
    unfolding extra_information_dom_def extra_information_mark_to_delete_def
    by auto
  from arg_cong[OF this(1), of \<open>\<lambda>n. n ! (length (N\<propto>i) - 1)\<close>] this(2-) 
  have lit: \<open>is_Lit (arena ! (i + length(N\<propto>i) - 1))\<close>
    by (auto simp: map_nth)

  have 
    pos: \<open>is_long_clause (N \<propto> j) \<longrightarrow> is_Pos (arena ! (j - POS_SHIFT))\<close> and
    st: \<open>is_Status (arena ! (j - STATUS_SHIFT))\<close> and
    size: \<open>is_Size (arena ! (j - SIZE_SHIFT))\<close> and
    lbd: \<open>is_LBD (arena ! (j - LBD_SHIFT))\<close> and
    act: \<open>is_Act (arena ! (j - ACTIVITY_SHIFT))\<close> and
    j_le: \<open>j < length arena\<close> and
    j_ge: \<open>j \<ge> header_size(N\<propto>j)\<close>
    using 2
    unfolding extra_information_dom_def extra_information_mark_to_delete_def
    by auto
  have False if ji: \<open>j - i \<ge> length (N\<propto>i)\<close>
  proof -
    have Suc4: \<open>4 = Suc (Suc (Suc (Suc 0)))\<close>
      by auto
    have Suc5: \<open>5 = Suc (Suc (Suc (Suc (Suc 0))))\<close>
      by auto
    have [simp]: \<open>j - Suc 0 = i + length (N \<propto> i) - Suc 0 \<longleftrightarrow> j = i + length (N \<propto> i)\<close>
      using False that j_ge i_ge length_Ni
      by auto
    consider
       \<open>is_long_clause (N \<propto> j)\<close> \<open>j - POS_SHIFT = i + length(N\<propto>i) - 1\<close> |
       \<open>j - STATUS_SHIFT = i + length(N\<propto>i) - 1\<close> |
       \<open>j - LBD_SHIFT = i + length(N\<propto>i) - 1\<close> |
       \<open>j - ACTIVITY_SHIFT = i + length(N\<propto>i) - 1\<close> |
       \<open>j - SIZE_SHIFT = i + length(N\<propto>i) - 1\<close>
      using False ji j_ge i_ge length_Ni
      unfolding header_size_def not_less_eq_eq STATUS_SHIFT_def SIZE_SHIFT_def
       LBD_SHIFT_def ACTIVITY_SHIFT_def Suc4 le_Suc_eq POS_SHIFT_def Suc5
      apply (cases \<open>is_short_clause (N \<propto> j)\<close>; cases \<open>is_short_clause (N \<propto> i)\<close>; 
        clarsimp_all simp only: if_True if_False add_Suc_right add_0_right
        le_Suc_eq; elim disjE)
      apply linarith
      by (solves simp)+
    then show False
      using lit pos st size lbd act
      by cases auto
  qed
  moreover have False if ji: \<open>j - i < length (N\<propto>i)\<close>
  proof -
    from arg_cong[OF eq, of \<open>\<lambda>xs. xs ! (j-i-1)\<close>]
    have \<open>is_Lit (arena ! (j-1))\<close>
      using that j_le i_le \<open>j > i\<close>
      by auto
    then show False
      using size unfolding SIZE_SHIFT_def by auto
  qed
  ultimately show False
    by linarith
qed


lemma extra_information_dom_delete_clause:
  fixes ia :: \<open>nat\<close>
  assumes 
    i: \<open>i \<in># dom_m N\<close> and
    dom: \<open>Multiset.Ball (dom_m N) (extra_information_dom arena N)\<close> and
    \<open>\<forall>i\<in>vdom. i \<notin># dom_m N \<longrightarrow> extra_information_vdom arena N i\<close> and
    ia: \<open>ia \<in># remove1_mset i (dom_m N)\<close>
  shows \<open>extra_information_dom (extra_information_mark_to_delete arena i)
          (fmdrop i N) ia\<close>
proof -
  have \<open>extra_information_dom arena N ia\<close> and [simp]: \<open>ia \<noteq> i\<close>\<open>i \<noteq> ia\<close>  and
      ia': \<open>header_size (N \<propto> ia) \<le> ia\<close> and
      ia: \<open>ia \<in># dom_m N\<close> 
    using assms distinct_mset_dom[of N] by (auto dest: in_diffD multi_member_split
      simp: extra_information_dom_def)
  moreover have i_header: \<open>i \<ge> header_size (N \<propto> i)\<close> and \<open>i < length arena\<close>
    using assms 
    unfolding extra_information_dom_def extra_information_mark_to_delete_def
    by auto
  moreover {
    have \<open>extra_information_dom arena N i\<close> 
      using assms distinct_mset_dom[of N] by (auto dest: in_diffD multi_member_split)
    then have \<open>is_Status(arena!(i - STATUS_SHIFT))\<close>
      unfolding extra_information_dom_def extra_information_mark_to_delete_def
      by auto
  } 
  moreover   have \<open>take (length (N \<propto> ia))
        (drop ia (arena[i - STATUS_SHIFT := AStatus DELETED])) =
        map ALit (N \<propto> ia)\<close>
    if
      cl:\<open>take (length (N \<propto> ia)) (drop ia arena) = map ALit (N \<propto> ia)\<close> and
      ia: \<open>ia \<in># dom_m N\<close>
  proof -
    show ?thesis
      using cl minimal_difference_between_valid_index[OF dom ia i]
        minimal_difference_between_valid_index[OF dom i ia]
      by (cases \<open>ia < i\<close>; cases \<open>i < ia\<close>)
        (auto simp: drop_update_swap STATUS_SHIFT_def
        header_size_def split: if_splits)
  qed
  moreover have
    \<open>i - STATUS_SHIFT \<noteq> ia - SIZE_SHIFT\<close> (is ?A) and
    \<open>is_long_clause(N\<propto>ia) \<Longrightarrow> i - STATUS_SHIFT \<noteq> ia - POS_SHIFT\<close> and
    \<open>i - STATUS_SHIFT \<noteq> ia - LBD_SHIFT\<close> (is ?C) and
    \<open>i - STATUS_SHIFT \<noteq> ia - ACTIVITY_SHIFT\<close> (is ?D)
  proof -
    show  ?A
      using minimal_difference_between_valid_index[OF dom ia i]
        minimal_difference_between_valid_index[OF dom i ia] ia'
      by (cases \<open>ia < i\<close>; cases \<open>i < ia\<close>) 
        (auto simp: drop_update_swap STATUS_SHIFT_def SIZE_SHIFT_def POS_SHIFT_def
        header_size_def split: if_splits)
    show  \<open>is_long_clause(N\<propto>ia) \<Longrightarrow> i - STATUS_SHIFT \<noteq> ia - POS_SHIFT\<close> 
      using minimal_difference_between_valid_index[OF dom ia i] i_header
        minimal_difference_between_valid_index[OF dom i ia] ia'
      by (cases \<open>ia < i\<close>; cases \<open>i < ia\<close>) 
        (auto simp: drop_update_swap STATUS_SHIFT_def SIZE_SHIFT_def POS_SHIFT_def
        header_size_def split: if_splits)
    show  ?C
      using minimal_difference_between_valid_index[OF dom ia i]
        minimal_difference_between_valid_index[OF dom i ia] ia'
      by (cases \<open>ia < i\<close>; cases \<open>i < ia\<close>) 
        (auto simp: drop_update_swap STATUS_SHIFT_def SIZE_SHIFT_def POS_SHIFT_def LBD_SHIFT_def
        header_size_def split: if_splits)
    show  ?D
      using minimal_difference_between_valid_index[OF dom ia i]
        minimal_difference_between_valid_index[OF dom i ia] ia'
      by (cases \<open>ia < i\<close>; cases \<open>i < ia\<close>) 
        (auto simp: drop_update_swap STATUS_SHIFT_def SIZE_SHIFT_def POS_SHIFT_def LBD_SHIFT_def
          ACTIVITY_SHIFT_def header_size_def split: if_splits)
  qed
  ultimately show ?thesis
    unfolding extra_information_dom_def extra_information_mark_to_delete_def
    apply (intro conjI)
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    done
qed

lemma extra_information_vdom_extra_information_mark_to_delete_same:
  assumes 
    \<open>i \<in># dom_m N\<close> and
    \<open>Multiset.Ball (dom_m N) (extra_information_dom arena N)\<close> and
    \<open>\<forall>i\<in>vdom. i \<notin># dom_m N \<longrightarrow> extra_information_vdom arena N i\<close> and
    \<open>i \<notin># remove1_mset i (dom_m N)\<close>
  shows \<open>extra_information_vdom (extra_information_mark_to_delete arena i)
          (fmdrop i N) i\<close>
proof -
  have \<open>extra_information_dom arena N i\<close>
    using assms distinct_mset_dom[of N] by (auto dest: in_diffD multi_member_split)
  then show ?thesis
  using distinct_mset_dom[of N]
    unfolding extra_information_vdom_def extra_information_dom_def
      extra_information_mark_to_delete_def
    by (clarsimp simp: header_size_def split: if_splits
      dest!: multi_member_split[of i])
qed

lemma extra_information_vdom_extra_information_mark_to_delete:
  fixes ia :: \<open>nat\<close>
  assumes 
    i_dom: \<open>i \<in># dom_m N\<close> and
    \<open>Multiset.Ball (dom_m N) (extra_information_dom arena N)\<close> and
    \<open>\<forall>i\<in>vdom. i \<notin># dom_m N \<longrightarrow> extra_information_vdom arena N i\<close> and
    \<open>ia \<in> vdom\<close> and
    \<open>ia \<notin># remove1_mset i (dom_m N)\<close>
  shows \<open>extra_information_vdom (extra_information_mark_to_delete arena i)
          (fmdrop i N) ia\<close>
proof -
  have \<open>extra_information_dom arena N i\<close>
    using assms distinct_mset_dom[of N] by (auto dest: in_diffD multi_member_split)
  then have \<open>ia = i \<Longrightarrow> ?thesis\<close>
    using extra_information_vdom_extra_information_mark_to_delete_same[OF assms(1-3)]
    using distinct_mset_dom[of N] i_dom
    by (auto dest!: multi_member_split)
  moreover have \<open>i \<noteq> ia \<Longrightarrow> extra_information_vdom arena N ia\<close>
    using assms distinct_mset_dom[of N] by (auto dest: in_diffD multi_member_split
      simp: distinct_mset_remove1_All)
  then have \<open>ia \<noteq> i \<Longrightarrow> ?thesis\<close>
    using distinct_mset_dom[of N]
    unfolding extra_information_vdom_def extra_information_dom_def extra_information_mark_to_delete_def
    by (clarsimp simp: header_size_def split: if_splits
      dest!: multi_member_split[of i])
  ultimately show ?thesis
    by blast
qed

lemma valid_arena_extra_information_mark_to_delete:
  assumes \<open>valid_arena arena N vdom\<close> and \<open>i \<in># dom_m N\<close>
  shows \<open>valid_arena (extra_information_mark_to_delete arena i) (fmdrop i N) (insert i vdom)\<close>
  using assms
  by (auto simp: valid_arena_def extra_information_dom_delete_clause
    extra_information_vdom_extra_information_mark_to_delete_same
    extra_information_vdom_extra_information_mark_to_delete)

lemma valid_arena_remove_from_vdom:
  assumes \<open>valid_arena arena N (insert i vdom)\<close>
  shows  \<open>valid_arena arena N vdom\<close>
  using assms valid_arena_def
  by (auto dest!: in_diffD)

end