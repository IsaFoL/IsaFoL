theory WB_Sort
  imports
    WB_More_Refinement
    "../lib/Explorer"
begin

definition choose_pivot where
  \<open>choose_pivot i j = SPEC(\<lambda>k. k \<ge> i \<and> k \<le> j)\<close>

definition partition_between :: \<open>('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> ('a list \<times> nat) nres\<close> where
  \<open>partition_between R h i0 j0 xs0 = do {
    ASSERT(i0 < length xs0 \<and> j0 < length xs0);
    k \<leftarrow> choose_pivot i0 j0; \<comment> \<open>choice of pivot\<close>	
    ASSERT(k < length xs0);
    xs \<leftarrow> RETURN (swap xs0 k j0);
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
  by auto

lemma partition_between_mset_eq:
  assumes \<open>i < length xs\<close> and \<open>j < length xs\<close> and \<open>j > i\<close>
  shows \<open>partition_between R h i j xs \<le> SPEC(\<lambda>(xs', j'). mset xs = mset xs' \<and> j' < length xs \<and>
     j' > i \<and> j' \<le> j)\<close>
proof -
  have H: \<open>Suc b \<le> j - card \<sigma>\<close>
    if
      a4: \<open>\<sigma> \<subseteq> {i..<j - Suc 0}\<close> and
      a2: \<open>x2 = Suc b\<close> and
      a3: \<open>i \<le> b\<close> and
      a1: \<open>b \<le> j - Suc (card \<sigma>)\<close>
      for \<sigma> b it ix xi2' a x x1 x2 x2'
  proof -
    have f6: "\<forall>n na. 0 < card {na::nat..<n} \<or> \<not> na < n"
      using card_atLeastLessThan by presburger
    have f7: "\<forall>n na. card {n::nat..<na} = 0 \<or> \<not> na \<le> n"
      using card_atLeastLessThan by presburger
    then have f8: "\<forall>n na. card {n..<Suc na} = 0 \<or> \<not> na < n"
      by (meson Suc_leI)
    have f9: "\<not> (0::nat) < 0"
      by fastforce
    have f10: "\<forall>n na. (n::nat) \<le> na \<or> card {na..<n} \<noteq> 0"
      by simp
    have f11: "\<forall>n na. \<not> n < Suc na \<or> \<not> na < n"
      using f9 f8 f6 by metis
    have f12: "\<forall>n na. card {na::nat..<n} = 0 \<or> na < n"
      by (metis (no_types) card_atLeastLessThan neq0_conv zero_less_diff)
    have f13: "\<forall>n. Suc (card {Suc 0..<n}) = n \<or> \<not> 0 < n"
      by (metis (full_types) Suc_pred card_atLeastLessThan)
    have f14: "\<not> b < i"
      using f7 f6 a3 neq0_conv by blast
    have "\<not> card {i..<card {Suc 0..<j}} < card \<sigma>"
      using f11 a4 by (metis card_atLeastLessThan card_mono finite_atLeastLessThan le_imp_less_Suc)
    then show ?thesis
      using f14 f13 f12 f10 f8 assms(3) a2 a1
      by (metis (no_types) Suc_diff_Suc card_atLeastLessThan le_imp_less_Suc nat_diff_split neq0_conv)
  qed

  show ?thesis
    unfolding partition_between_def choose_pivot_def
    apply (refine_vcg WHILEIT_rule[where R = \<open>measure (\<lambda>(i, j, _). j - i)\<close>])
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal by auto
    subgoal by auto
    subgoal using assms by (auto dest: mset_eq_length)
    subgoal by (force dest: mset_eq_length)
    subgoal by (force dest: mset_eq_length)
    subgoal by auto
    subgoal by auto
    subgoal for x it \<sigma> a b x1 x2
      apply (subst card_Diff_singleton)
      apply (auto dest: finite_subset simp: Suc_pred card_gt_0_iff)
      apply (subst Suc_pred)
      by (auto dest: finite_subset simp: card_gt_0_iff intro!: H)
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


sepref_definition p1
  is \<open>uncurry2 (partition_between (<) id)\<close>
  :: \<open>nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a (arl_assn nat_assn)\<^sup>d \<rightarrow>\<^sub>a
      arl_assn nat_assn *a nat_assn\<close>
  unfolding partition_between_def id_def
  apply sepref_dbg_keep
  apply sepref_dbg_trans_keep
  apply sepref_dbg_trans_step_keep
  apply sepref_dbg_side_unfold

  apply sepref
end