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
  \<open>STATUS_SHIFT = 5\<close>

definition ACTIVITY_SHIFT :: nat where
  \<open>ACTIVITY_SHIFT = 5\<close>

definition LBD_SHIFT :: nat where
  \<open>LBD_SHIFT = 5\<close>

definition SIZE_SHIFT :: nat where
  \<open>SIZE_SHIFT = 5\<close>

datatype arena_el =
  is_Lit: ALit (arena_lit: \<open>nat literal\<close>) |
  is_LBD: ALBD (arena_lbd: nat) |
  is_Act: AActivity (arena_act: nat) |
  is_Size: ASize (arena_size: nat)  |
  is_Pos: APos (arena_pos: nat)  |
  is_Status: AStatus (arena_status: clause_status)

type_synonym arena = \<open>arena_el list\<close>

definition is_short_clause where
\<open>is_short_clause C \<longleftrightarrow> length C \<le> 5\<close>

abbreviation is_long_clause where
\<open>is_long_clause C \<equiv> \<not>is_short_clause C\<close>

definition header_size where
\<open>header_size C = (if is_short_clause C then 5 else 4)\<close>

definition extra_information_dom :: \<open>arena \<Rightarrow> (nat, nat literal list \<times> bool) fmap \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>extra_information_dom arena N i \<longleftrightarrow>
     (i > header_size (N \<propto> i) \<and> i \<in># dom_m N \<and> length (N \<propto> i) \<ge> 2 \<and>
       i + length (N\<propto>i) \<le> length arena \<and>
     (is_long_clause (N\<propto>i) \<longrightarrow> (is_Pos (arena!(i - POS_SHIFT)) \<and>
       arena_pos(arena!(i - POS_SHIFT)) < length (N \<propto> i) - 2)) \<and>
     is_Status(arena!(i - STATUS_SHIFT)) \<and> 
        (arena_status(arena!(i - STATUS_SHIFT)) = INIT \<longleftrightarrow> irred N i) \<and> 
        (arena_status(arena!(i - STATUS_SHIFT)) = LEARNED \<longleftrightarrow> \<not>irred N i) \<and>
     is_Size(arena!(i - SIZE_SHIFT)) \<and> arena_size(arena!(i - SIZE_SHIFT)) + 2 = length(N\<propto>i) \<and>
     take (length (N\<propto>i)) (drop i arena) = map ALit (N\<propto> i)
  )\<close>


definition extra_information_vdom :: \<open>arena \<Rightarrow> (nat, nat literal list \<times> bool) fmap \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>extra_information_vdom arena N i \<longleftrightarrow>
     i > 4 \<and> i \<notin># dom_m N \<and> length (N \<propto> i) \<ge> 2 \<and> i < length arena \<and>
     is_Status(arena!(i - STATUS_SHIFT)) \<and> arena_status(arena!(i - STATUS_SHIFT)) = DELETED
\<close>

definition extra_information_mark_to_delete where
  \<open>extra_information_mark_to_delete arena i = arena[i - STATUS_SHIFT := AStatus DELETED]\<close>

definition valid_arena where
  \<open>valid_arena arena N vdom \<longleftrightarrow>
    (\<forall>i \<in># dom_m N. extra_information_dom arena N i) \<and>
    (\<forall>i \<in> vdom. i \<notin># dom_m N \<longrightarrow> extra_information_vdom arena N i)
\<close>

lemma extra_information_dom_delete_clause:
  fixes ia :: \<open>nat\<close>
  assumes 
    \<open>i \<in># dom_m N\<close> and
    \<open>Multiset.Ball (dom_m N) (extra_information_dom arena N)\<close> and
    \<open>\<forall>i\<in>vdom. i \<notin># dom_m N \<longrightarrow> extra_information_vdom arena N i\<close> and
    ia: \<open>ia \<in># remove1_mset i (dom_m N)\<close>
  shows \<open>extra_information_dom (extra_information_mark_to_delete arena i)
          (fmdrop i N) ia\<close>
proof -
  have \<open>extra_information_dom arena N ia\<close> and [simp]: \<open>ia \<noteq> i\<close>
    using assms distinct_mset_dom[of N] by (auto dest: in_diffD multi_member_split)
  moreover have \<open>i \<ge> header_size (N \<propto> i)\<close> and \<open>i < length arena\<close>
    using assms 
    unfolding extra_information_dom_def extra_information_mark_to_delete_def
    by auto
  ultimately show ?thesis
    unfolding extra_information_dom_def extra_information_mark_to_delete_def
    apply (intro conjI)
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by (auto simp: STATUS_SHIFT_def POS_SHIFT_def)
    subgoal by (auto simp: STATUS_SHIFT_def POS_SHIFT_def header_size_def)
    subgoal by (auto simp: STATUS_SHIFT_def POS_SHIFT_def header_size_def SIZE_SHIFT_def)
    subgoal by (auto simp: STATUS_SHIFT_def POS_SHIFT_def header_size_def SIZE_SHIFT_def)
    subgoal by (auto simp: STATUS_SHIFT_def POS_SHIFT_def header_size_def SIZE_SHIFT_def)
    subgoal by (auto simp: STATUS_SHIFT_def POS_SHIFT_def header_size_def SIZE_SHIFT_def)
    subgoal by (auto simp: STATUS_SHIFT_def POS_SHIFT_def header_size_def SIZE_SHIFT_def)
    subgoal by (auto simp: STATUS_SHIFT_def POS_SHIFT_def header_size_def SIZE_SHIFT_def)
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
    unfolding extra_information_vdom_def extra_information_dom_def
    by (auto simp: STATUS_SHIFT_def POS_SHIFT_def header_size_def SIZE_SHIFT_def) 
qed

lemma extra_information_vdom_extra_information_mark_to_delete:
  fixes ia :: \<open>nat\<close>
  assumes 
    \<open>i \<in># dom_m N\<close> and
    \<open>Multiset.Ball (dom_m N) (extra_information_dom arena N)\<close> and
    \<open>\<forall>i\<in>vdom. i \<notin># dom_m N \<longrightarrow> extra_information_vdom arena N i\<close> and
    \<open>ia \<in> vdom\<close> and
    \<open>ia \<notin># remove1_mset i (dom_m N)\<close>
  shows \<open>extra_information_vdom (extra_information_mark_to_delete arena i)
          (fmdrop i N) ia\<close>
proof -
  have \<open>extra_information_dom arena N i\<close>
    using assms distinct_mset_dom[of N] by (auto dest: in_diffD multi_member_split)
  moreover have \<open>i \<noteq> ia \<Longrightarrow> extra_information_vdom arena N ia\<close>
    using assms distinct_mset_dom[of N] by (auto dest: in_diffD multi_member_split
      simp: distinct_mset_remove1_All)
  ultimately show ?thesis
    unfolding extra_information_vdom_def extra_information_dom_def extra_information_mark_to_delete_def
    by (auto simp: STATUS_SHIFT_def POS_SHIFT_def header_size_def SIZE_SHIFT_def) 
qed

lemma valid_arena_extra_information_mark_to_delete:
  assumes \<open>valid_arena arena N vdom\<close> and \<open>i \<in># dom_m N\<close>
  shows \<open>valid_arena (extra_information_mark_to_delete arena i) (fmdrop i N) (insert i vdom)\<close>
  using assms
  by (auto simp: valid_arena_def extra_information_dom_delete_clause
    extra_information_vdom_extra_information_mark_to_delete_same
    extra_information_vdom_extra_information_mark_to_delete)

end