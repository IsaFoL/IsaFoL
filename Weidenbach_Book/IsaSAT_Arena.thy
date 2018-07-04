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

As we are already wasteful with memory, we implement the first optimisation.
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
     Misc.slice i (i + length (N\<propto>i)) arena = map ALit (N\<propto> i)
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

(* TODO Move to replce @{thm slice_nth} *)
lemma slice_nth: "\<lbrakk>from \<le> length xs; i < to - from \<rbrakk> \<Longrightarrow> Misc.slice from to xs ! i = xs ! (from + i)"
  unfolding slice_def Misc.slice_def
  apply (subst nth_take, assumption)
  apply (subst nth_drop, assumption)
  ..


lemma slice_irrelevant[simp]:
  \<open>i < from \<Longrightarrow> Misc.slice from to (xs[i := C]) = Misc.slice from to xs\<close>
  \<open>i >= to \<Longrightarrow> Misc.slice from to (xs[i := C]) = Misc.slice from to xs\<close>
  \<open>i >= to \<or> i < from \<Longrightarrow> Misc.slice from to (xs[i := C]) = Misc.slice from to xs\<close>
  unfolding Misc.slice_def apply auto
  by (metis drop_take take_update_cancel)+

lemma slice_update_swap[simp]:
  \<open>i < to \<Longrightarrow> i \<ge> from \<Longrightarrow> i < length xs \<Longrightarrow>
     Misc.slice from to (xs[i := C]) = (Misc.slice from to xs)[(i - from) := C]\<close>
  unfolding Misc.slice_def by (auto simp: drop_update_swap)
(* End Move *)

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

  have eq: \<open>Misc.slice i (i + length (N \<propto> i)) arena = map ALit (N \<propto> i)\<close> and
    \<open>length (N \<propto> i) - Suc 0 < length (N \<propto> i)\<close> and
    i_le: \<open>i < length arena\<close> and
    i_ge: \<open>i \<ge> header_size(N\<propto>i)\<close> and
    length_Ni: \<open>length (N\<propto>i) \<ge> 2\<close>
    using 1
    unfolding extra_information_dom_def extra_information_mark_to_delete_def
    by auto
  from arg_cong[OF this(1), of \<open>\<lambda>n. n ! (length (N\<propto>i) - 1)\<close>] this(2-)
  have lit: \<open>is_Lit (arena ! (i + length(N\<propto>i) - 1))\<close>
    by (auto simp: map_nth slice_nth)

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
        le_Suc_eq; elim disjE Misc.slice_def)
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
      by (auto simp: slice_nth)
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
  moreover have \<open>take (length (N \<propto> ia))
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
    subgoal by (simp add: Misc.slice_def)
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

definition astatus where
  \<open>astatus arena i = arena!(i - STATUS_SHIFT)\<close>

definition asize where
  \<open>asize arena i = arena!(i - SIZE_SHIFT)\<close>

lemma valid_arena_cong_imp:
  assumes
    arena: \<open>valid_arena arena N vdom\<close> and
    clss: \<open>\<And>i. i \<in># dom_m N \<Longrightarrow> 2 \<le> length (N \<propto> i) \<Longrightarrow>
       Misc.slice i (i + length(N\<propto>i)) arena = Misc.slice i (i + length(N\<propto>i)) arena2\<close> and
    status: \<open>\<And>i. i \<in># dom_m N \<Longrightarrow> astatus arena i = astatus arena2 i\<close> and
    size: \<open>\<And>i. i \<in># dom_m N \<Longrightarrow> asize arena i = asize arena2 i\<close> and
    pos: \<open>\<And>i. i \<in># dom_m N \<Longrightarrow> is_long_clause (N\<propto>i) \<Longrightarrow> is_Pos (arena!(i - POS_SHIFT)) \<Longrightarrow>
        arena_pos(arena!(i - POS_SHIFT)) < length (N \<propto> i) - 2 \<Longrightarrow>
       is_Pos (arena2!(i - POS_SHIFT)) \<and>
       arena_pos(arena2!(i - POS_SHIFT)) < length (N \<propto> i) - 2\<close> and
    lbd: \<open>\<And>i. i \<in># dom_m N \<Longrightarrow> is_LBD (arena ! (i - LBD_SHIFT)) \<Longrightarrow> is_LBD (arena2 ! (i - LBD_SHIFT))\<close> and
    act: \<open>\<And>i. i \<in># dom_m N \<Longrightarrow> is_Act (arena ! (i - ACTIVITY_SHIFT))\<Longrightarrow> is_Act (arena2 ! (i - ACTIVITY_SHIFT))\<close> and
    vdom: \<open>\<And>i. i \<in> vdom \<Longrightarrow> i \<notin># dom_m N \<Longrightarrow> astatus arena i = astatus arena2 i\<close> and
    [simp]: \<open>length arena = length arena2\<close>
  shows \<open>valid_arena arena2 N vdom\<close>
proof -
  have \<open>Multiset.Ball (dom_m N) (extra_information_dom arena2 N)\<close>
  proof (intro ballI)
    fix C
    assume C: \<open>C \<in># dom_m N\<close>
    then have \<open>extra_information_dom arena N C\<close>
      using arena
      unfolding valid_arena_def
      by auto
    hence
      \<open>header_size (N \<propto> C) \<le> C\<close> and
      \<open>C \<in># dom_m N\<close> and
      \<open>2 \<le> length (N \<propto> C)\<close> and
      \<open>C + length (N \<propto> C) \<le> length arena\<close> and
      \<open>is_long_clause (N \<propto> C) \<longrightarrow>
      is_Pos (arena ! (C - POS_SHIFT)) \<and>
      arena_pos (arena ! (C - POS_SHIFT)) < length (N \<propto> C) - 2\<close> and
      \<open>is_Status (arena ! (C - STATUS_SHIFT))\<close> and
      \<open>(arena_status (arena ! (C - STATUS_SHIFT)) = INIT) = irred N C\<close> and
      \<open>(arena_status (arena ! (C - STATUS_SHIFT)) = LEARNED) = (\<not> irred N C)\<close> and
      \<open>is_LBD (arena ! (C - LBD_SHIFT))\<close> and
      \<open>is_Act (arena ! (C - ACTIVITY_SHIFT))\<close> and
      \<open>is_Size (arena ! (C - SIZE_SHIFT))\<close> and
      \<open>arena_size (arena ! (C - SIZE_SHIFT)) + 2 = length (N \<propto> C)\<close> and
      \<open>Misc.slice C (C + length (N \<propto> C)) arena = map ALit (N \<propto> C)\<close>
      unfolding extra_information_dom_def by blast+
    then show \<open>extra_information_dom arena2 N C\<close>
      using pos[OF C] lbd[OF C] act[OF C] clss[OF C] size[OF C, unfolded asize_def]
        status[OF C, unfolded astatus_def]
      unfolding extra_information_dom_def
      by simp_all
  qed
  moreover have \<open>extra_information_vdom arena2 N i\<close>
  if
    \<open>i \<in> vdom\<close> and
    \<open>i \<notin># dom_m N\<close>
  for i
  proof -
    have \<open>extra_information_vdom arena N i\<close>
      using arena that
      unfolding valid_arena_def
      by auto
    then show ?thesis
    using vdom[of i] that
    unfolding extra_information_vdom_def astatus_def
    by auto
  qed
  ultimately show ?thesis
    unfolding valid_arena_def
    by blast
qed


definition update_act where
  \<open>update_act C act arena = arena[C - ACTIVITY_SHIFT := AActivity act]\<close>

lemma
  assumes arena: \<open>valid_arena arena N vdom\<close> and i: \<open>i \<in># dom_m N\<close> and j: \<open>j \<in># dom_m N\<close>
  shows
     arena_valid_index_separation_activity:
      \<open>i \<ge> header_size (N\<propto>i)\<close> (is ?A)
      \<open>i \<ge> 4\<close> (is ?A')
      \<open>length (N \<propto> i) \<ge> 2\<close> (is ?L)
      \<open>i < length arena\<close> (is ?L')
      \<open>j = i \<or> (i - ACTIVITY_SHIFT < j \<and> i - LBD_SHIFT < j \<and> length (N \<propto> i) + header_size (N \<propto> j) \<le> j - i) \<or>
        (i - ACTIVITY_SHIFT > j + length (N\<propto>j) \<and> i - LBD_SHIFT > j + length (N\<propto>j) \<and>
            length (N \<propto> j) + header_size (N \<propto> i) \<le> i - j)\<close> (is ?B)
        \<open>i - ACTIVITY_SHIFT \<noteq> j - STATUS_SHIFT\<close> (is ?diff1)
        \<open>i - ACTIVITY_SHIFT \<noteq> i - SIZE_SHIFT\<close> (is ?diff2)
        \<open>i - ACTIVITY_SHIFT \<noteq> j - SIZE_SHIFT\<close> (is ?diff3)
        \<open>i - ACTIVITY_SHIFT \<noteq> i - SIZE_SHIFT\<close> (is ?diff4)
        \<open>i - ACTIVITY_SHIFT \<noteq> j - SIZE_SHIFT\<close> (is ?diff5)
        \<open>i - ACTIVITY_SHIFT \<noteq> i - LBD_SHIFT\<close> (is ?diff6)
        \<open>i - ACTIVITY_SHIFT \<noteq> j - LBD_SHIFT\<close> (is ?diff7)
        \<open>is_long_clause (N\<propto>j) \<Longrightarrow> i - ACTIVITY_SHIFT \<noteq> j - POS_SHIFT\<close> (is \<open>?long \<Longrightarrow> ?diff8\<close>)
        \<open>i - ACTIVITY_SHIFT < i\<close> (is ?notin1) and

     arena_valid_index_separation_lbd:

        \<open>i - LBD_SHIFT \<noteq> j - STATUS_SHIFT\<close> (is ?diff1')
        \<open>i - LBD_SHIFT \<noteq> i - SIZE_SHIFT\<close> (is ?diff2')
        \<open>i - LBD_SHIFT \<noteq> j - SIZE_SHIFT\<close> (is ?diff3')
        \<open>i - LBD_SHIFT \<noteq> i - SIZE_SHIFT\<close> (is ?diff4')
        \<open>i - LBD_SHIFT \<noteq> j - SIZE_SHIFT\<close> (is ?diff5')
        \<open>i - LBD_SHIFT \<noteq> i - ACTIVITY_SHIFT\<close> (is ?diff6')
        \<open>i - LBD_SHIFT \<noteq> j - ACTIVITY_SHIFT\<close> (is ?diff7')
        \<open>is_long_clause (N\<propto>j) \<Longrightarrow> i - LBD_SHIFT \<noteq> j - POS_SHIFT\<close> (is \<open>?long \<Longrightarrow> ?diff8'\<close>)

        \<open>i - LBD_SHIFT < i\<close> (is ?notin1') and

     arena_valid_index_separation_pos:
        \<open>is_long_clause (N\<propto>i) \<Longrightarrow> j = i \<or> (i - POS_SHIFT < j \<and> length (N \<propto> i) + header_size (N \<propto> j) \<le> j - i) \<or>
          (i - POS_SHIFT >= j + length (N\<propto>j) \<and>
            length (N \<propto> j) + header_size (N \<propto> i) \<le> i - j)\<close> (is \<open>_ \<Longrightarrow> ?B'\<close>)

        \<open>is_long_clause (N\<propto>i) \<Longrightarrow> i - POS_SHIFT \<noteq> j - STATUS_SHIFT\<close> (is \<open>?long'' \<Longrightarrow>?diff1''\<close>)
        \<open>is_long_clause (N\<propto>i) \<Longrightarrow> i - POS_SHIFT \<noteq> i - SIZE_SHIFT\<close> (is \<open>_ \<Longrightarrow> ?diff2''\<close>)
        \<open>is_long_clause (N\<propto>i) \<Longrightarrow> i - POS_SHIFT \<noteq> j - SIZE_SHIFT\<close> (is \<open>_ \<Longrightarrow> ?diff3''\<close>)
        \<open>is_long_clause (N\<propto>i) \<Longrightarrow> i - POS_SHIFT \<noteq> i - SIZE_SHIFT\<close> (is \<open>_ \<Longrightarrow> ?diff4''\<close>)
        \<open>is_long_clause (N\<propto>i) \<Longrightarrow> i - POS_SHIFT \<noteq> j - SIZE_SHIFT\<close> (is \<open>_ \<Longrightarrow> ?diff5''\<close>)
        \<open>is_long_clause (N\<propto>i) \<Longrightarrow> i - POS_SHIFT \<noteq> i - ACTIVITY_SHIFT\<close> (is \<open>_ \<Longrightarrow> ?diff6''\<close>)
        \<open>is_long_clause (N\<propto>i) \<Longrightarrow> i - POS_SHIFT \<noteq> j - ACTIVITY_SHIFT\<close> (is \<open>_ \<Longrightarrow> ?diff7''\<close>)
        \<open>is_long_clause (N\<propto>i) \<Longrightarrow> i - POS_SHIFT \<noteq> i - LBD_SHIFT\<close> (is \<open>_ \<Longrightarrow> ?diff8''\<close>)
        \<open>is_long_clause (N\<propto>i) \<Longrightarrow> i - POS_SHIFT \<noteq> j - LBD_SHIFT\<close> (is \<open>_ \<Longrightarrow> ?diff9''\<close>)
        \<open>is_long_clause (N\<propto>i) \<Longrightarrow> i - POS_SHIFT < i\<close> (is \<open>_ \<Longrightarrow> ?notin1''\<close>)
        \<open>is_long_clause (N\<propto>i) \<Longrightarrow> is_long_clause (N\<propto>j) \<Longrightarrow> i - POS_SHIFT = j - POS_SHIFT \<longleftrightarrow> i = j\<close>
proof -
  have dom: \<open>Multiset.Ball (dom_m N) (extra_information_dom arena N)\<close>
    using arena unfolding valid_arena_def by blast
  then show ?A and ?L and ?L'
    using i unfolding extra_information_dom_def by auto
  then show ?A'
    unfolding header_size_def by (auto split: if_splits)
  show ?B
     using minimal_difference_between_valid_index[OF dom i j]
       minimal_difference_between_valid_index[OF dom j i]
      by (cases \<open> i < j\<close>) (auto simp: ACTIVITY_SHIFT_def LBD_SHIFT_def header_size_def split: if_splits)

  show ?diff1 ?diff2 ?diff3 ?diff4 ?diff5 ?diff6 ?diff7 \<open>?long \<Longrightarrow> ?diff8\<close>
   ?diff1' ?diff2' ?diff3' ?diff4' ?diff5' ?diff6' ?diff7' \<open>?long \<Longrightarrow> ?diff8'\<close>
    using \<open>?B\<close> \<open>?A\<close> \<open>?L\<close>
    by (auto simp: ACTIVITY_SHIFT_def STATUS_SHIFT_def header_size_def SIZE_SHIFT_def LBD_SHIFT_def
      POS_SHIFT_def
      split: if_splits)
  show \<open>?long'' \<Longrightarrow>?B'\<close>
     using minimal_difference_between_valid_index[OF dom i j]
       minimal_difference_between_valid_index[OF dom j i]
      by (cases \<open> i < j\<close>) (auto simp: ACTIVITY_SHIFT_def LBD_SHIFT_def header_size_def
        POS_SHIFT_def split: if_splits)
  moreover have \<open>j \<ge> 4\<close> \<open>header_size (N \<propto> j) \<le> j\<close>
    using dom j unfolding extra_information_dom_def by (auto simp: header_size_def split: if_splits)
  ultimately show \<open>?long'' \<Longrightarrow>?diff1''\<close>  \<open>?long'' \<Longrightarrow>?diff2''\<close>  \<open>?long'' \<Longrightarrow>?diff3''\<close>  \<open>?long'' \<Longrightarrow>?diff4''\<close>
     \<open>?long'' \<Longrightarrow>?diff5''\<close>  \<open>?long'' \<Longrightarrow>?diff6''\<close>  \<open>?long'' \<Longrightarrow>?diff7''\<close>   \<open>?long'' \<Longrightarrow>?diff8''\<close>  \<open>?long'' \<Longrightarrow>?diff9''\<close>
    using \<open>?L\<close> \<open>?A\<close>
    by (auto simp: ACTIVITY_SHIFT_def STATUS_SHIFT_def header_size_def SIZE_SHIFT_def LBD_SHIFT_def
      POS_SHIFT_def
      split: if_splits)
  show ?notin1 ?notin1' ?notin1''
    using \<open>?B\<close> \<open>?A\<close>
    by (auto simp: ACTIVITY_SHIFT_def STATUS_SHIFT_def header_size_def SIZE_SHIFT_def LBD_SHIFT_def
      POS_SHIFT_def
      split: if_splits)
  show \<open>is_long_clause (N\<propto>i) \<Longrightarrow> is_long_clause (N\<propto>j) \<Longrightarrow>  i - POS_SHIFT = j - POS_SHIFT \<longleftrightarrow> i = j\<close>
    using \<open>?A\<close> \<open>header_size (N \<propto> j) \<le> j\<close>
    by (cases \<open>i \<ge> 5\<close>)
      (auto simp: ACTIVITY_SHIFT_def STATUS_SHIFT_def header_size_def SIZE_SHIFT_def LBD_SHIFT_def
      POS_SHIFT_def
      split: if_splits)
qed

lemma arena_valid_index_vdom_separation:
  assumes arena: \<open>valid_arena arena N vdom\<close> and i: \<open>i \<in># dom_m N\<close> and
   j: \<open>j \<notin># dom_m N\<close> and
   j: \<open>j \<in> vdom\<close>
  shows
    \<open>i - 3 \<noteq> j - 4\<close>
    \<open>i - 2 \<noteq> j - 4\<close>
    \<open>is_long_clause (N \<propto> i) \<longrightarrow> i - 5 \<noteq> j - 4\<close>
proof -

  have \<open>extra_information_dom arena N i\<close> and \<open>extra_information_vdom arena N j\<close>
    using assms unfolding valid_arena_def by auto
  then have \<open>is_Status (arena ! (j - STATUS_SHIFT))\<close> and \<open>is_Act (arena!(i - ACTIVITY_SHIFT))\<close> and
    \<open>is_LBD (arena ! (i - LBD_SHIFT))\<close>
    \<open>is_long_clause (N \<propto> i) \<longrightarrow> is_Pos (arena ! (i - POS_SHIFT))\<close>
    unfolding extra_information_dom_def extra_information_vdom_def
    by fast+
  then show
    \<open>i - 3 \<noteq> j - 4\<close>
    \<open>i - 2 \<noteq> j - 4\<close>
    \<open>is_long_clause (N \<propto> i) \<longrightarrow> i - 5 \<noteq> j - 4\<close>
    unfolding STATUS_SHIFT_def ACTIVITY_SHIFT_def is_LBD_def LBD_SHIFT_def POS_SHIFT_def
    by auto
qed

lemma
  assumes arena: \<open>valid_arena arena N vdom\<close> and i: \<open>i \<in># dom_m N\<close>
  shows \<open>valid_arena (update_act i act arena) N vdom\<close>
  apply (rule valid_arena_cong_imp)
  apply (rule arena)
  subgoal for j
    unfolding update_act_def
    using arena_valid_index_separation_activity[OF arena i, of j]
    by (auto simp: )
  subgoal for j
    unfolding update_act_def
    using arena_valid_index_separation_activity[OF arena i, of j] i
    by (auto simp: astatus_def update_act_def)
  subgoal for j
    unfolding update_act_def
    using arena_valid_index_separation_activity[OF arena i, of j] i
    by (auto simp: asize_def update_act_def)
  subgoal for j
    unfolding update_act_def
    using arena_valid_index_separation_activity[OF arena i, of j] i
    by (simp add: asize_def update_act_def)
  subgoal for j
    unfolding update_act_def
    using arena_valid_index_separation_activity[OF arena i, of j] i
    by (auto simp: asize_def update_act_def)
  subgoal for j
    unfolding update_act_def
    using arena_valid_index_separation_activity[OF arena i, of j] i
    by (auto simp: asize_def update_act_def)
  subgoal for j
    unfolding update_act_def
    using i arena_valid_index_vdom_separation[OF arena i, of j]
    by (auto simp: astatus_def update_act_def ACTIVITY_SHIFT_def STATUS_SHIFT_def)
  subgoal
    by (simp add: update_act_def)
  done


definition update_lbd where
  \<open>update_lbd C lbd arena = arena[C - LBD_SHIFT := ALBD lbd]\<close>

definition update_pos where
  \<open>update_pos C pos arena = arena[C - POS_SHIFT := APos pos]\<close>

lemma
  assumes arena: \<open>valid_arena arena N vdom\<close> and i: \<open>i \<in># dom_m N\<close>
  shows \<open>valid_arena (update_lbd i act arena) N vdom\<close>
  apply (rule valid_arena_cong_imp)
  apply (rule arena)
  subgoal for j
    unfolding update_lbd_def
    using arena_valid_index_separation_lbd[OF arena i, of j]
    arena_valid_index_separation_activity(5)[OF arena i, of j]
    by (auto simp: )
  subgoal for j
    unfolding update_lbd_def
    using arena_valid_index_separation_lbd[OF arena i, of j] i
    by (auto simp: astatus_def update_lbd_def)
  subgoal for j
    unfolding update_lbd_def
    using arena_valid_index_separation_lbd[OF arena i, of j] i
    by (auto simp: asize_def update_lbd_def)
  subgoal for j
    unfolding update_lbd_def
    using arena_valid_index_separation_lbd[OF arena i, of j] i
    by (simp add: asize_def update_lbd_def)
  subgoal for j
    unfolding update_lbd_def
    using arena_valid_index_separation_lbd[OF arena i, of j] i
    arena_valid_index_separation_activity(1-5)[OF arena i, of j]
    by (simp add: asize_def update_lbd_def)
  subgoal for j
    unfolding update_lbd_def
    using arena_valid_index_separation_lbd[OF arena i, of j] i
    by (auto simp: asize_def update_lbd_def)
  subgoal for j
    unfolding update_lbd_def
    using i arena_valid_index_vdom_separation[OF arena i, of j]
    by (auto simp: astatus_def update_lbd_def ACTIVITY_SHIFT_def STATUS_SHIFT_def
      LBD_SHIFT_def)
  subgoal
    by (simp add: update_lbd_def)
  done


lemma
  assumes arena: \<open>valid_arena arena N vdom\<close> and i: \<open>i \<in># dom_m N\<close> and \<open>pos < length (N\<propto>i) - 2\<close> and
    [simp]: \<open>is_long_clause (N\<propto>i)\<close>
  shows \<open>valid_arena (update_pos i pos arena) N vdom\<close>
  apply (rule valid_arena_cong_imp)
  apply (rule arena)
  subgoal for j
    unfolding update_pos_def
    using arena_valid_index_separation_pos[OF arena i, of j]
    arena_valid_index_separation_activity(1-4)[OF arena i, of j]
    by (auto simp: )
  subgoal for j
    unfolding update_pos_def
    using arena_valid_index_separation_pos[OF arena i, of j] i
    by (auto simp: astatus_def update_pos_def)
  subgoal for j
    unfolding update_pos_def
    using arena_valid_index_separation_pos[OF arena i, of j] i
    arena_valid_index_separation_activity(5)[OF arena i, of j]
    by (auto simp: asize_def update_pos_def)
  subgoal for j
    unfolding update_pos_def
    using arena_valid_index_separation_pos[OF arena i, of j] i  \<open>pos < length (N\<propto>i) - 2\<close>
    arena_valid_index_separation_activity(1-4)[OF arena i, of j]
    by (clarsimp simp add: asize_def update_pos_def)
  subgoal for j
    unfolding update_pos_def
    using arena_valid_index_separation_pos[OF arena i, of j] i
    arena_valid_index_separation_activity(1-4)[OF arena i, of j]
    by (simp add: asize_def update_pos_def)
  subgoal for j
    unfolding update_pos_def
    using arena_valid_index_separation_pos[OF arena i, of j] i
    arena_valid_index_separation_activity(1-4)[OF arena i, of j]
    by (auto simp: asize_def update_pos_def)
  subgoal for j
    unfolding update_pos_def
    using i arena_valid_index_vdom_separation[OF arena i, of j]
    by (auto simp: astatus_def update_pos_def ACTIVITY_SHIFT_def STATUS_SHIFT_def
      LBD_SHIFT_def POS_SHIFT_def)
  subgoal
    by (simp add: update_pos_def)
  done

end