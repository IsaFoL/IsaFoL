theory WB_Sort
  imports
    WB_More_Refinement
begin

definition partition_between :: \<open>('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> ('a list \<times> nat) nres\<close> where
  \<open>partition_between R h i0 j0 xs0 = do {
     ASSERT(i0 < length xs0 \<and> j0 < length xs0);
     pivot \<leftarrow> RETURN (h (xs0 ! j0));
     (i, xs) \<leftarrow> FOREACHi
       (\<lambda>js (i, xs). i < length xs \<and> mset xs = mset xs0 \<and> i \<ge> i0 \<and>
          i \<le> (j0 - 1) - card js)
       (set [i0..<j0 - 1])
       (\<lambda>j (i, xs). do {
         ASSERT(j < length xs);
         if R (h (xs!j)) pivot
	 then RETURN (i+1, swap xs i j)
	 else RETURN (i, xs)
       })
       (i0, xs0);
     RETURN (xs, i+1)
   }\<close>

lemma Min_atLeastLessThan[simp]: \<open>b > a \<Longrightarrow> Min {a..<b} = a\<close> for a b :: nat
  using linorder_class.eq_Min_iff[of \<open>{a..<b}\<close> a]
  by (auto simp: )

lemma Min_atLeastLessThan2[simp]: \<open>{a..<b} \<noteq> {} \<Longrightarrow> Min {a..<b} = a\<close> for a b :: nat
  using linorder_class.eq_Min_iff[of \<open>{a..<b}\<close> a]
  by (auto simp: )


lemma partition_between_mset_eq:
  assumes \<open>i < length xs\<close> and \<open>j < length xs\<close> and \<open>j > i\<close>
  shows \<open>partition_between R h i j xs \<le> SPEC(\<lambda>(xs', j'). mset xs = mset xs' \<and> j' < length xs \<and>
     j' > i \<and> j' \<le> j)\<close>
proof -
  show ?thesis
    unfolding partition_between_def
    apply (refine_vcg WHILEIT_rule[where R = \<open>measure (\<lambda>(i, j, _). j - i)\<close>])
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal by auto
    subgoal using assms by (auto dest: mset_eq_length)
    subgoal by (force dest: mset_eq_length)
    subgoal by (force dest: mset_eq_length)
    subgoal by auto
    subgoal by auto
    subgoal for x it \<sigma> a b x1 x2
      apply (subst card_Diff_singleton)
      apply (auto dest: finite_subset simp: card_gt_0_iff)
apply (subst Suc_pred)
apply (auto dest: finite_subset simp: card_gt_0_iff)
by (smt One_nat_def Suc_diff_Suc Suc_diff_le Suc_le_mono Suc_pred \<open>i < length xs \<and> j < length xs \<Longrightarrow> finite (set [i..<j - 1])\<close> assms(3) card_atLeastLessThan card_mono diff_Suc_Suc less_le nat_in_between_eq(2) neq0_conv set_upt zero_less_diff)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal for x it \<sigma> a b x1 x2
      by (subst card_Diff_singleton)
        (auto dest: finite_subset simp: card_gt_0_iff)
    subgoal by auto
    subgoal using assms by auto
    subgoal by auto
    subgoal using assms(3) by auto
    done
qed

definition quicksort :: \<open>_ \<Rightarrow> _ \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a::ord list \<Rightarrow> 'a list nres\<close> where
\<open>quicksort R h i j xs0 = do {
  RECT (\<lambda>f (i,j,xs). do {
      ASSERT(mset xs = mset xs0);
      if i+1 \<ge> j then RETURN xs
      else do{
	(xs, k) \<leftarrow> partition_between R h i j xs;
	xs \<leftarrow> f (i, k-1, xs);
	f (k, j, xs)
      }
    })
    (i, j, xs0)
  }\<close>


lemma quicksort_between_mset_eq:
  assumes \<open>i < length xs\<close> and \<open>j < length xs\<close> and \<open>j \<ge> i\<close>
  shows \<open>quicksort R h i j xs \<le> \<Down> Id (SPEC(\<lambda>xs'. mset xs = mset xs'))\<close>
proof -
  have wf: \<open>wf (measure (\<lambda>(i, j, xs). Suc j - i))\<close>
    by auto
  have pre: \<open>(\<lambda>(i, j, xs'). i < length xs \<and> j < length xs \<and> i \<le> j \<and>
    mset xs = mset xs') (i,j,xs)\<close>
    using assms by auto
  show ?thesis
    unfolding quicksort_def
    apply (rule RECT_rule)
       apply (refine_mono)
      apply (rule wf)
     apply (rule pre)
    subgoal premises IH for f x
      using IH(2)
      apply (refine_vcg)
      apply ((auto; fail)+)[2]
      apply (rule partition_between_mset_eq[THEN order_trans])
      subgoal by (auto dest: mset_eq_length)
      subgoal by (auto dest: mset_eq_length)
      subgoal by (auto dest: mset_eq_length)
      apply (rule SPEC_rule)
      apply (subst (5) Down_id_eq[symmetric])
      apply (case_tac xa, simp only: prod.simps)
      apply (rule bind_refine_spec)
      prefer 2
      apply (rule IH(1)[THEN order_trans])
      subgoal
        by (auto dest: mset_eq_length)
      subgoal by auto
      apply (subst (3) Down_id_eq[symmetric])
      apply (rule order.refl)
      apply (rule IH(1)[THEN order_trans])
      subgoal
        by (auto dest: mset_eq_length)
      subgoal by auto
      apply auto
      done
    done
qed

end