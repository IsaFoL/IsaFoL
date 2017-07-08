theory CDCL_Two_Watched_Literals_List_Conflict_Assn
  imports CDCL_Two_Watched_Literals_List_Watched_Code_Common
begin

no_notation Ref.update ("_ := _" 62)


subsubsection \<open>Clauses Encoded as Positions\<close>

inductive mset_as_position :: \<open>bool option list \<Rightarrow> nat literal multiset \<Rightarrow> bool\<close>where
empty:
  \<open>mset_as_position (replicate n None) {#}\<close> |
add:
  \<open>mset_as_position xs' (add_mset L P)\<close>
   if \<open>mset_as_position xs P\<close> \<open>atm_of L < length xs\<close> and \<open>L \<notin># P\<close> and \<open>-L \<notin># P\<close> and
     \<open>xs' = xs[atm_of L := Some (is_pos L)]\<close>

lemma mset_as_position_distinct_mset:
  \<open>mset_as_position xs P \<Longrightarrow> distinct_mset P\<close>
  by (induction rule: mset_as_position.induct) auto 

lemma mset_as_position_atm_le_length:
  \<open>mset_as_position xs P \<Longrightarrow> L \<in># P \<Longrightarrow> atm_of L < length xs\<close>
  by (induction rule: mset_as_position.induct) (auto simp: nth_list_update' atm_of_eq_atm_of)

lemma mset_as_position_nth:
  \<open>mset_as_position xs P \<Longrightarrow> L \<in># P \<Longrightarrow> xs ! (atm_of L) = Some (is_pos L)\<close>
  by (induction rule: mset_as_position.induct)
    (auto simp: nth_list_update' atm_of_eq_atm_of dest: mset_as_position_atm_le_length)

(*TODO Move*)
lemma (in -) is_pos_neg_not_is_pos: \<open>is_pos (- L) \<longleftrightarrow> \<not>is_pos L\<close>
  by (cases L) auto
(*End Move*)

lemma mset_as_position_in_iff_nth:
  \<open>mset_as_position xs P \<Longrightarrow> atm_of L < length xs \<Longrightarrow> L \<in># P \<longleftrightarrow> xs ! (atm_of L) = Some (is_pos L)\<close>
  by (induction rule: mset_as_position.induct)
    (auto simp: nth_list_update' atm_of_eq_atm_of is_pos_neg_not_is_pos
      dest: mset_as_position_atm_le_length)

term \<open>fold (\<lambda>L xs. xs[atm_of L := Some (is_pos L)]) P xs\<close>
lemma
  fixes P xs
  defines \<open>xs' \<equiv> fold (\<lambda>L xs. xs[atm_of L := Some (is_pos L)]) P xs\<close>
  assumes \<open>mset_as_position xs P'\<close> and
    \<open>\<forall>L \<in> set P. atm_of L < length xs\<close> and
    \<open>\<forall>L \<in> set P. -L \<notin># P'\<close> and
    \<open>distinct P\<close>
  shows \<open>mset_as_position xs' (mset P \<union># P')\<close>
  using assms unfolding xs'_def
  apply (induction P)
  subgoal by auto
  subgoal for L P
    apply (cases \<open>L \<in># P'\<close>)
    apply (auto intro!: mset_as_position.add) 
  sorry
  sorry

end