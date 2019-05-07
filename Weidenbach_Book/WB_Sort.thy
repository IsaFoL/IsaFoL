theory WB_Sort
  imports
    Watched_Literals.WB_More_Refinement
begin

\<comment> \<open>Every element between \<^term>\<open>lo\<close> and \<^term>\<open>hi\<close> can be chosen as pivot element.\<close>
definition choose_pivot :: \<open>('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat nres\<close> where
  \<open>choose_pivot _ _ _ lo hi = SPEC(\<lambda>k. k \<ge> lo \<and> k \<le> hi)\<close>

\<comment> \<open>The element at index \<open>p\<close> partitions the subarray \<open>lo..hi\<close>. This means that every element \<close>
definition isPartition :: \<open>('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'b list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>isPartition R xs lo hi p \<equiv> (\<forall> i. i \<ge> lo \<and> i < p \<longrightarrow> R (xs!i) (xs!p)) \<and> (\<forall> j. j > p \<and> j \<le> hi \<longrightarrow> R (xs!p) (xs!j))\<close>

definition isPartition_map :: \<open>('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>isPartition_map R h xs i j k \<equiv> isPartition R (map h xs) i j k\<close>

 \<comment> \<open>Example: 6 is the pivot element (with index 4); \<open>7\<close> is equal to the length - 1.\<close>
lemma \<open>isPartition (<) [0,5,3,4,6,9,8,10::nat] 0 7 4\<close>
  apply (auto simp add: isPartition_def numeral_eq_Suc Nat.less_Suc_eq)
  by (smt One_nat_def Suc_diff_Suc diff_is_0_eq le_Suc_eq le_imp_less_Suc nth_Cons')


definition sublist :: \<open>'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list\<close> where
\<open>sublist xs i j \<equiv> take (1+j-i) (drop i xs)\<close>

value \<open>sublist [0,1,2,3::nat] 1 3\<close>
value \<open>sublist [0::nat] 0 0\<close>

lemma sublist_single: \<open>i < length xs \<Longrightarrow> sublist xs i i = [xs!i]\<close>
  by (simp add: sublist_def Hash_Map.take_Suc0(2))

lemma insert_eq: \<open>insert a b = b \<union> {a}\<close>
  by auto

lemma sublist_nth: \<open>\<lbrakk>i1 \<le> i2; i2 < length xs; k \<le> (i2-i1)\<rbrakk> \<Longrightarrow> (sublist xs i1 i2)!k = xs!(i1+k)\<close>
  by (simp add: sublist_def)

lemma sublist_length: \<open>\<lbrakk>i \<le> j; j < length xs\<rbrakk> \<Longrightarrow> length (sublist xs i j) = 1 + j - i\<close>
  by (simp add: sublist_def)

lemma sublist_not_empty: \<open>\<lbrakk>i \<le> j; j < length xs; xs \<noteq> []\<rbrakk> \<Longrightarrow> sublist xs i j \<noteq> []\<close>
  apply simp
  apply (rewrite List.length_greater_0_conv[symmetric])
  apply (rewrite sublist_length)
  by auto

lemma sublist_app: \<open>\<lbrakk>i1 \<le> i2; i2 \<le> i3\<rbrakk> \<Longrightarrow> sublist xs i1 i2 @ sublist xs (Suc i2) i3 = sublist xs i1 i3\<close>
  unfolding sublist_def
  by (smt Suc_eq_plus1_left Suc_le_mono append.assoc le_SucI le_add_diff_inverse le_trans same_append_eq take_add)

definition sorted_sublist_wrt :: \<open>('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'b list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>sorted_sublist_wrt R xs lo hi = sorted_wrt R (sublist xs lo hi)\<close>

definition sorted_sublist :: \<open>'a :: linorder list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>sorted_sublist xs lo hi = sorted_sublist_wrt (<) xs lo hi\<close>

definition sorted_sublist_map :: \<open>('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>sorted_sublist_map R h xs lo hi = sorted_sublist_wrt R (map h xs) lo hi\<close>

lemma sorted_sublist_wrt_refl: \<open>i < length xs \<Longrightarrow> sorted_sublist_wrt R xs i i\<close>
  by (auto simp add: sorted_sublist_wrt_def sublist_single)

lemma sorted_sublist_refl: \<open>i < length xs \<Longrightarrow> sorted_sublist xs i i\<close>
  by (auto simp add: sorted_sublist_def sorted_sublist_wrt_refl)

lemma sorted_sublist_map_refl: \<open>i < length xs \<Longrightarrow> sorted_sublist_map R h xs i i\<close>
  by (auto simp add: sorted_sublist_map_def sorted_sublist_wrt_refl)


definition partition_between :: \<open>('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> ('a list \<times> nat) nres\<close> where
  \<open>partition_between R h lo hi xs0 = do {
    ASSERT(lo < length xs0 \<and> hi < length xs0 \<and> hi > lo);
    k \<leftarrow> choose_pivot R h xs0 lo hi; \<comment> \<open>choice of pivot\<close>
    ASSERT(k < length xs0);
    xs \<leftarrow> RETURN (swap xs0 k hi); \<comment> \<open>move the pivot to the last position, before we start the actual loop\<close>
    ASSERT(length xs = length xs0);
    pivot \<leftarrow> RETURN (h (xs ! hi));
    (i, xs) \<leftarrow> FOREACHi
      (\<lambda>js (i, xs). \<comment> \<open>\<open>js\<close> is the set of \<open>j\<close>s for that we have already run the loop.\<close>
        i < length xs \<and> mset xs = mset xs0 \<and> i \<ge> lo \<and> i + card js \<le> hi)
      (set [lo..<hi]) \<comment> \<open>we loop from \<open>i=lo\<close> to \<open>i=hi-1\<close>\<close>
      (\<lambda>j (i, xs). do {
        ASSERT(j < length xs \<and> i < length xs \<and> mset xs = mset xs0);
        if R (h (xs!j)) pivot
      	then RETURN (i+1, swap xs i j)
      	else RETURN (i, xs)
      })
      (lo, xs);
    ASSERT(i < length xs \<and> hi < length xs);
    RETURN (swap xs i hi, i)
  }\<close>

lemma Min_atLeastLessThan[simp]: \<open>b > a \<Longrightarrow> Min {a..<b} = a\<close> for a b :: nat
  using linorder_class.eq_Min_iff[of \<open>{a..<b}\<close> a]
  by auto

lemma Min_atLeastLessThan2[simp]: \<open>{a..<b} \<noteq> {} \<Longrightarrow> Min {a..<b} = a\<close> for a b :: nat
  using linorder_class.eq_Min_iff[of \<open>{a..<b}\<close> a]
  by auto

lemma partition_between_mset_eq:
  assumes \<open>lo < length xs\<close> and \<open>hi < length xs\<close> and \<open>hi > lo\<close>
  shows \<open>partition_between R h lo hi xs \<le> SPEC(\<lambda>(xs', p). mset xs = mset xs' \<and> p < length xs \<and>
     p \<ge> lo \<and> p \<le> hi)\<close> \<comment> \<open>TODO: Show that \<open>p\<close> is a valid partiton.\<close>
proof -
  have H: \<open>b \<le> hi - card \<sigma>\<close>
    if
      a4: \<open>\<sigma> \<subseteq> {lo..<hi}\<close> and
      a2: \<open>x2 = Suc b\<close> and
      a3: \<open>lo \<le> b\<close> and
      a1: \<open>b \<le> hi - Suc (card \<sigma>)\<close>
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
    have f14: "\<not> b < lo"
      using f7 f6 a3 neq0_conv by blast
    have "\<not> card {lo..<card {0..<hi}} < card \<sigma>"
      using f11 a4 by (metis card_atLeastLessThan card_mono finite_atLeastLessThan minus_nat.diff_0 not_less)
    then show ?thesis
      using f14 f13 f12 f10 f8 assms(3) a2 a1
      by (metis (no_types) Suc_diff_Suc card_atLeastLessThan le_imp_less_Suc nat_diff_split neq0_conv)
  qed
  have K: \<open>b \<le> hi - Suc n \<Longrightarrow> n > 0 \<Longrightarrow> Suc n \<le> hi \<Longrightarrow>  Suc b \<le> hi - n\<close> for b hi n
    by auto
  show ?thesis
    unfolding partition_between_def choose_pivot_def
    apply (refine_vcg)
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal using assms
      by (force dest: mset_eq_length)
    subgoal by (force dest: mset_eq_length)
    subgoal using assms by (auto dest: mset_eq_length)
    subgoal using assms by (auto dest: mset_eq_length)
    subgoal using assms apply (auto dest: mset_eq_length)
      by (metis Suc_lessI \<open>\<And>xa. \<lbrakk>lo < length xs \<and> hi < length xs \<and> lo < hi; lo \<le> xa \<and> xa \<le> hi;
          xa < length xs; length (swap xs xa hi) = length xs\<rbrakk> \<Longrightarrow> finite (set [lo..<hi])\<close>
          \<open>\<And>xa. \<lbrakk>lo < length xs \<and> hi < length xs \<and> lo < hi; lo \<le> xa \<and> xa \<le> hi; xa < length xs\<rbrakk> \<Longrightarrow> length (swap xs xa hi) = length xs\<close>
          add_diff_cancel_left' assms(1) card_gt_0_iff diff_add_inverse2 empty_iff infinite_super le_eq_less_or_eq less_imp_diff_less not_less set_upt size_mset zero_less_diff)
    subgoal by (force dest: mset_eq_length)
    subgoal by auto
    subgoal le1 apply (auto dest: mset_eq_length)
      by (metis add_Suc_right card_Suc_Diff1 finite_atLeastLessThan finite_subset)
    subgoal by (force dest: mset_eq_length)
    subgoal by auto
    subgoal by auto
    subgoal apply (auto dest: mset_eq_length)
      by (metis Suc_leD add_Suc_right card_Suc_Diff1 card_atLeastLessThan card_gt_0_iff infinite_super zero_less_diff)
    subgoal by auto
    subgoal by (force dest: mset_eq_length)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

definition quicksort :: \<open>('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list nres\<close> where
\<open>quicksort R h lo hi xs0 = do {
  RECT (\<lambda>f (lo,hi,xs). do {
      ASSERT(mset xs = mset xs0);
      if hi\<le>lo then RETURN xs
      else do{
	      (xs, p) \<leftarrow> partition_between R h lo hi xs;
	      xs \<leftarrow> f (lo, p-1, xs);
        f (p+1, hi, xs)
      }
    })
    (lo, hi, xs0)
  }\<close>

lemma quicksort_between_mset_eq:
  assumes \<open>lo < length xs \<or> (lo \<ge> length xs \<and> hi \<le> lo)\<close> and \<open>(hi < length xs \<or> (hi \<ge> length xs \<and> hi \<le> lo))\<close>
  shows \<open>quicksort R h lo hi xs \<le> \<Down> Id (SPEC(\<lambda>xs'. mset xs = mset xs'))\<close> \<comment> \<open>TODO: Sortedness\<close>
proof -
  have wf: \<open>wf (measure (\<lambda>(lo, hi, xs). Suc hi - lo))\<close>
    by auto
  have pre: \<open>(\<lambda>(lo, hi, xs'). (lo < length xs \<or> (lo \<ge> length xs \<and> hi \<le> lo)) \<and> 
      (hi < length xs \<or> (hi \<ge> length xs \<and> hi \<le> lo)) \<and>
    mset xs = mset xs') (lo,hi,xs)\<close>
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
      subgoal by auto
      done
    done
qed

text \<open>We use the median of the first, the middle, and the last element.\<close>
definition choose_pivot3 where
  \<open>choose_pivot3 R h xs lo (hi::nat) = do {
    ASSERT(lo < length xs);
    ASSERT(hi < length xs);
    let k = (lo + hi) div 2;
    let start = h (xs ! lo);
    let mid = h (xs ! k);
    let end = h (xs ! hi);
    if (R start mid \<and> R mid end) \<or> (R end mid \<and> R mid start) then RETURN k
    else if (R start end \<and> R end mid) \<or> (R mid end \<and> R end start) then RETURN hi
    else RETURN lo
}\<close>

\<comment> \<open>We only have to show that this procedure yields a valid index between \<open>lo\<close> and \<open>hi\<close>.\<close>
lemma choose_pivot3_choose_pivot:
  assumes \<open>lo < length xs\<close> \<open>hi < length xs\<close> \<open>hi \<ge> lo\<close>
  shows \<open>choose_pivot3 R h xs lo hi \<le> \<Down> Id (choose_pivot R h xs lo hi)\<close>
  unfolding choose_pivot3_def choose_pivot_def
  using assms by (auto intro!: ASSERT_leI simp: Let_def)

\<comment> \<open>The refined partion function: We use the above pivot function and fold instead of non-deterministic iteration.\<close>
definition partition_between_ref
  :: \<open>('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> ('a list \<times> nat) nres\<close>
where
  \<open>partition_between_ref R h lo hi xs0 = do {
    ASSERT(lo < length xs0 \<and> hi < length xs0 \<and> hi > lo);
    k \<leftarrow> choose_pivot3 R h xs0 lo hi; \<comment> \<open>choice of pivot\<close>
    ASSERT(k < length xs0);
    xs \<leftarrow> RETURN (swap xs0 k hi); \<comment> \<open>move the pivot to the last position, before we start the actual loop\<close>
    ASSERT(length xs = length xs0);
    pivot \<leftarrow> RETURN (h (xs ! hi));
    (i, xs) \<leftarrow> nfoldli
      ([lo..<hi])
      (\<lambda>_. True) \<comment> \<open>TODO: We don't we insert the loop invariant here?\<close>
      (\<lambda>j (i, xs). do {
      	ASSERT(j < length xs \<and> i < length xs \<and> mset xs = mset xs0);
      	if R (h (xs!j)) pivot
      	then RETURN (i+1, swap xs i j)
      	else RETURN (i, xs)
      })
      (lo, xs);
    ASSERT(i < length xs \<and> hi < length xs);
    RETURN (swap xs i hi, i)
  }\<close>

lemma partition_between_ref_partition_between:
  \<open>partition_between_ref R h lo hi xs \<le> (partition_between R h lo hi xs)\<close>
proof -
  have swap: \<open>(swap xs k hi, swap xs ka hi) \<in> Id\<close> if \<open>k = ka\<close>
    for k ka
    using that by auto
  have [refine0]: \<open>(h (xsa ! hi), h (xsaa ! hi)) \<in> Id\<close>
    if \<open>(xsa, xsaa) \<in> Id\<close>
    for xsa xsaa
    using that by auto
  \<comment> \<open>Compare non-deterministic iteration with deterministic fold\<close>
  have [refine0]: \<open>(RETURN [lo..<hi], it_to_sorted_list (\<lambda>_ _. True) (set [lo..<hi]))
       \<in> {(c, a).
          c \<le> \<Down> {(x, y).
                 list_all2 (\<lambda>x x'. (x, x') \<in> Id) x
                  y}
               a}\<close>
    by (auto simp: it_to_sorted_list_def list.rel_eq
      intro!: RETURN_RES_refine exI[of _ \<open>[lo..<hi]\<close>])
  \<comment> \<open>Refinement of the loop body\<close>
  have [refine0]: \<open>(\<lambda>j (i, xs). do {
                      _ \<leftarrow> ASSERT (j < length xs \<and> i < length xs \<and> mset xs = mset xsa);
                     if R (h (xs ! j)) pivot then RETURN (i + 1, swap xs i j)
                     else RETURN (i, xs)
                  },
                  \<lambda>j (i, xs). do {
                     _ \<leftarrow> ASSERT (j < length xs \<and> i < length xs \<and> mset xs = mset xsa);
                     if R (h (xs ! j)) pivota then RETURN (i + 1, swap xs i j)
                     else RETURN (i, xs)
                 })
       \<in> {(f, f').
          \<forall>x y. (x, y) \<in> nat_rel \<longrightarrow>
                (\<forall>xa ya.
                    (xa, ya) \<in> Id \<longrightarrow>
                    f x xa \<le> \<Down> Id (f' y ya))}\<close>
    if \<open>(pivot, pivota) \<in> Id\<close>
    for pivot pivota xsa
    using that
    by (auto intro!: ext ASSERT_leI)

  show ?thesis
    apply (subst (2) Down_id_eq[symmetric])
    unfolding partition_between_ref_def
      partition_between_def FOREACH_patterns
      LIST_FOREACH'_def[of \<open>RETURN _\<close>, unfolded nres_monad1, symmetric]
      OP_def
    apply (refine_vcg choose_pivot3_choose_pivot swap
      LIST_FOREACH_autoref["to_\<Down>"] \<comment> \<open>@Peter: what is the proper way to do that?\<close>
      )
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

\<comment> \<open>Technical lemma for sepref\<close>
lemma partition_between_ref_partition_between':
  \<open>(uncurry2 (partition_between_ref R h), uncurry2 (partition_between R h)) \<in>
    nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f \<langle>Id\<rangle>list_rel \<rightarrow>\<^sub>f \<langle>\<langle>Id\<rangle>list_rel \<times>\<^sub>r nat_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto intro: partition_between_ref_partition_between)

\<comment> \<open>Example instantiation for pivot\<close>
definition choose_pivot3_impl where
  \<open>choose_pivot3_impl = choose_pivot3 (<) id\<close>

\<comment> \<open>Example instantiation code for pivot\<close>
sepref_definition choose_pivot3_impl_code
  is \<open>uncurry2 (choose_pivot3_impl)\<close>
  :: \<open>(arl_assn nat_assn)\<^sup>k  *\<^sub>a  nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k\<rightarrow>\<^sub>a nat_assn\<close>
  unfolding choose_pivot3_impl_def choose_pivot3_def id_def
  by sepref

declare choose_pivot3_impl_code.refine[sepref_fr_rules]

\<comment> \<open>Example instantiation for partition\<close>
definition partition_between_impl where
  \<open>partition_between_impl = partition_between_ref (<) id\<close>

sepref_register choose_pivot3 partition_between_ref

\<comment> \<open>Example instantiation code for partition\<close>
sepref_definition partition_between_code
  is \<open>uncurry2 (partition_between_impl)\<close>
  :: \<open>nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a (arl_assn nat_assn)\<^sup>d \<rightarrow>\<^sub>a
      arl_assn nat_assn *a nat_assn\<close>
  unfolding partition_between_ref_def partition_between_impl_def
    choose_pivot3_impl_def[symmetric]
  unfolding id_def
  by sepref

declare partition_between_code.refine[sepref_fr_rules]

\<comment> \<open>Refined quicksort algorithm: We use the refined partition function.\<close>
definition quicksort_ref :: \<open>_ \<Rightarrow> _ \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a::ord list \<Rightarrow> 'a list nres\<close> where
\<open>quicksort_ref R h i j xs0 = do {
  RECT (\<lambda>f (i,j,xs). do {
      ASSERT(mset xs = mset xs0);
      if j \<le> i then RETURN xs
      else do{
      	(xs, k) \<leftarrow> partition_between_ref R h i j xs;
      	xs \<leftarrow> f (i, k-1, xs);
      	f (k+1, j, xs)
      }
    })
    (i, j, xs0)
  }\<close>

lemma quicksort_ref_quicksort:
  \<open>quicksort_ref R f lo hi xs \<le> \<Down> Id (quicksort R f lo hi xs)\<close>
proof -
  have wf: \<open>wf (measure (\<lambda>(lo, hi, xs). Suc hi - lo))\<close>
    by auto
  have pre: \<open> ((lo, hi, xs), lo, hi, xs) \<in> Id \<times>\<^sub>r Id \<times>\<^sub>r \<langle>Id\<rangle>list_rel\<close>
    by auto
  have f: \<open>f (x1b, x2e - 1, x1e)
	\<le> \<Down> Id
	   (fa (x1, x2d - 1, x1d))\<close>
    if
      H: \<open>\<And>x x'.
	  (x, x') \<in> nat_rel \<times>\<^sub>f (nat_rel \<times>\<^sub>f \<langle>Id\<rangle>list_rel) \<Longrightarrow>
	  f x \<le> \<Down> Id (fa x')\<close> and
      \<open>(x, x') \<in> nat_rel \<times>\<^sub>f (nat_rel \<times>\<^sub>f \<langle>Id\<rangle>list_rel)\<close> and
      \<open>x2 = (x1a, x2a)\<close> and
      \<open>x' = (x1, x2)\<close> and
      \<open>x2b = (x1c, x2c)\<close> and
      \<open>x = (x1b, x2b)\<close> and
      \<open>(xa, x'a) \<in> \<langle>Id\<rangle>list_rel \<times>\<^sub>f nat_rel\<close> and
      \<open>x'a = (x1d, x2d)\<close> and
      \<open>xa = (x1e, x2e)\<close>
    for f fa x x' x1 x2 x1a x2a x1b x2b x1c x2c xa x'a x1d x2d x1e x2e
  proof -
    show ?thesis
      by (rule H) (use that in auto)
  qed
  have f': \<open>f (x2e + 1, x1c, xsa) \<le> \<Down> Id (fa (x2d + 1, x1a, xsaa))\<close>
    if
      H: \<open>\<And>x x'.
	  (x, x') \<in> nat_rel \<times>\<^sub>f (nat_rel \<times>\<^sub>f \<langle>Id\<rangle>list_rel) \<Longrightarrow>
	  f x \<le> \<Down> Id (fa x')\<close> and
      \<open>(x, x') \<in> nat_rel \<times>\<^sub>f (nat_rel \<times>\<^sub>f \<langle>Id\<rangle>list_rel)\<close> and
      \<open>x2 = (x1a, x2a)\<close> and
      \<open>x' = (x1, x2)\<close> and
      \<open>x2b = (x1c, x2c)\<close> and
      \<open>x = (x1b, x2b)\<close> and
      \<open>(xa, x'a) \<in> \<langle>Id\<rangle>list_rel \<times>\<^sub>f nat_rel\<close> and
      \<open>x'a = (x1d, x2d)\<close> and
      \<open>xa = (x1e, x2e)\<close> and
      \<open>(xsa, xsaa) \<in> Id\<close>
    for f fa x x' x1 x2 x1a x2a x1b x2b x1c x2c xa x'a x1d x2d x1e x2e xsa xsaa
  proof -
    show ?thesis
      by (rule H) (use that in auto)
  qed
  show ?thesis
    unfolding quicksort_def quicksort_ref_def
    apply (refine_vcg pre
      partition_between_ref_partition_between'[THEN fref_to_Down_curry2])
    subgoal by auto
    subgoal
      by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    apply (rule f; assumption)
    apply (rule f'; assumption)
    done
 qed

\<comment> \<open>Example implementation\<close>
definition quicksort_impl where
  \<open>quicksort_impl = quicksort_ref (<) id\<close>

sepref_register quicksort_impl

\<comment> \<open>Example implementation code\<close>
sepref_definition quicksort_code
  is \<open>uncurry2 (quicksort_impl)\<close>
  :: \<open>nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a (arl_assn nat_assn)\<^sup>d \<rightarrow>\<^sub>a
      arl_assn nat_assn\<close>
  unfolding partition_between_impl_def[symmetric]
    quicksort_impl_def quicksort_ref_def
  by sepref

declare quicksort_code.refine[sepref_fr_rules]

\<comment> \<open>Sort the entire list\<close>
definition full_quicksort where
  \<open>full_quicksort R h xs = quicksort R h 0 (length xs - 1) xs\<close>

definition full_quicksort_ref where
  \<open>full_quicksort_ref R h xs =
    quicksort_ref R h 0 (length xs - 1) xs\<close>

definition full_quicksort_impl :: \<open>nat list \<Rightarrow> nat list nres\<close> where
  \<open>full_quicksort_impl xs = full_quicksort_ref (<) id xs\<close>

lemma full_quicksort_ref_full_quicksort:
  \<open>(full_quicksort_ref R h, full_quicksort R h) \<in>
    \<langle>Id\<rangle>list_rel \<rightarrow>\<^sub>f \<langle> \<langle>Id\<rangle>list_rel\<rangle>nres_rel\<close>
  unfolding full_quicksort_ref_def full_quicksort_def
  by (intro frefI nres_relI)
     (auto intro!: quicksort_ref_quicksort[unfolded Down_id_eq]
       simp: List.null_def)

\<comment> \<open>Executable code for the example instance\<close>
sepref_definition full_quicksort_code
  is \<open>full_quicksort_impl\<close>
  :: \<open>(arl_assn nat_assn)\<^sup>d \<rightarrow>\<^sub>a
      arl_assn nat_assn\<close>
  unfolding full_quicksort_impl_def full_quicksort_ref_def quicksort_impl_def[symmetric] List.null_def
  by sepref

\<comment> \<open>Export the code\<close>
export_code \<open>nat_of_integer\<close> \<open>integer_of_nat\<close> \<open>partition_between_code\<close> \<open>full_quicksort_code\<close> in SML_imp module_name IsaQuicksort file "code/quicksort.sml"

lemma full_quicksort:
  shows \<open>full_quicksort R h xs \<le> \<Down> Id (SPEC(\<lambda>xs'. mset xs = mset xs'))\<close>
  unfolding full_quicksort_def
  apply (rule order_trans)
   prefer 2
   apply (rule quicksort_between_mset_eq)
    prefer 3
    apply auto
  using diff_Suc_less by blast

end
