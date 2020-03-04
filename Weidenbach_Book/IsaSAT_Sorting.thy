theory IsaSAT_Sorting
  imports IsaSAT_Setup
begin

definition clause_score_ordering where
  \<open>clause_score_ordering = (\<lambda>(lbd, act) (lbd', act'). lbd < lbd' \<or> (lbd = lbd' \<and> act < act'))\<close>

definition (in -) clause_score_extract :: \<open>arena \<Rightarrow> nat \<Rightarrow> nat \<times> nat\<close> where
  \<open>clause_score_extract arena C = (
     if arena_status arena C = DELETED
     then (uint32_max, 0) \<comment> \<open>deleted elements are the
        largest possible\<close>
     else
       let lbd = arena_lbd arena C in
       let act = arena_act arena C in
       (lbd, act)
  )\<close>

definition valid_sort_clause_score_pre_at where
  \<open>valid_sort_clause_score_pre_at arena C \<longleftrightarrow>
    (\<exists>i vdom. C = vdom ! i \<and> arena_is_valid_clause_vdom arena (vdom!i) \<and>
          (arena_status arena (vdom!i) \<noteq> DELETED \<longrightarrow>
             (get_clause_LBD_pre arena (vdom!i) \<and> arena_act_pre arena (vdom!i)))
          \<and> i < length vdom)\<close>

definition (in -)valid_sort_clause_score_pre where
  \<open>valid_sort_clause_score_pre arena vdom \<longleftrightarrow>
    (\<forall>C \<in> set vdom. arena_is_valid_clause_vdom arena C \<and>
        (arena_status arena C \<noteq> DELETED \<longrightarrow>
             (get_clause_LBD_pre arena C \<and> arena_act_pre arena C)))\<close>


definition clause_score_less :: "arena \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "clause_score_less arena i j \<longleftrightarrow>
     clause_score_ordering (clause_score_extract arena i) (clause_score_extract arena j)"

definition idx_cdom :: "arena \<Rightarrow> nat set" where
 "idx_cdom arena \<equiv> {i. valid_sort_clause_score_pre_at arena i}"

definition mop_clause_score_less where
  \<open>mop_clause_score_less arena i j = do {
    ASSERT(valid_sort_clause_score_pre_at arena i);
    ASSERT(valid_sort_clause_score_pre_at arena j);
    RETURN (clause_score_ordering (clause_score_extract arena i) (clause_score_extract arena j))
  }\<close>

end