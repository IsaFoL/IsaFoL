theory WB_Sort
  imports
    Watched_Literals.WB_More_Refinement
begin

text \<open>Every element between \<^term>\<open>lo\<close> and \<^term>\<open>hi\<close> can be chosen as pivot element.\<close>
definition choose_pivot :: \<open>('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat nres\<close> where
  \<open>choose_pivot _ _ _ lo hi = SPEC(\<lambda>k. k \<ge> lo \<and> k \<le> hi)\<close>

text \<open>The element at index \<open>p\<close> partitions the subarray \<open>lo..hi\<close>. This means that every element \<close>
definition isPartition_wrt :: \<open>('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'b list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>isPartition_wrt R xs lo hi p \<equiv> (\<forall> i. i \<ge> lo \<and> i < p \<longrightarrow> R (xs!i) (xs!p)) \<and> (\<forall> j. j > p \<and> j \<le> hi \<longrightarrow> R (xs!p) (xs!j))\<close>

definition isPartition :: \<open>'a :: order list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>isPartition xs lo hi p \<equiv> isPartition_wrt (\<le>) xs lo hi p\<close>

abbreviation isPartition_map :: \<open>('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>isPartition_map R h xs i j k \<equiv> isPartition_wrt R (map h xs) i j k\<close>

text \<open>Example: 6 is the pivot element (with index 4); \<open>7\<close> is equal to the length - 1.\<close>
lemma \<open>isPartition [0,5,3,4,6,9,8,10::nat] 0 7 4\<close>
  by (auto simp add: isPartition_def isPartition_wrt_def nth_Cons')

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
  \<open>sorted_sublist xs lo hi = sorted_sublist_wrt (\<le>) xs lo hi\<close>

abbreviation sorted_sublist_map :: \<open>('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>sorted_sublist_map R h xs lo hi \<equiv> sorted_sublist_wrt R (map h xs) lo hi\<close>

lemma sorted_sublist_wrt_refl: \<open>i < length xs \<Longrightarrow> sorted_sublist_wrt R xs i i\<close>
  by (auto simp add: sorted_sublist_wrt_def sublist_single)

lemma sorted_sublist_refl: \<open>i < length xs \<Longrightarrow> sorted_sublist xs i i\<close>
  by (auto simp add: sorted_sublist_def sorted_sublist_wrt_refl)

lemma sorted_sublist_map_refl: \<open>i < length xs \<Longrightarrow> sorted_sublist_map R h xs i i\<close>
  by (auto simp add: sorted_sublist_wrt_refl)


definition partition_main_inv :: \<open>('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> (nat\<times>nat\<times>'a list) \<Rightarrow> bool\<close> where
  \<open>partition_main_inv R h lo hi xs0 p \<equiv>
    case p of (i,j,xs) \<Rightarrow>
    j < length xs \<and> j \<le> hi \<and> i < length xs \<and> lo \<le> i \<and> i \<le> j \<and> mset xs = mset xs0 \<and>
    (\<forall>k. k \<ge> lo \<and> k < i \<longrightarrow> R (h (xs!k)) (h (xs!hi))) \<and> \<comment> \<open>All elements from \<open>lo\<close> to \<open>i-1\<close> are smaller than the pivot\<close>
    (\<forall>k. k \<ge> i \<and> k < j \<longrightarrow>  R (h (xs!hi)) (h (xs!k))) \<and> \<comment> \<open>All elements from \<open>i\<close> to \<open>j-1\<close> are greater than the pivot\<close>
    (\<forall>k. k \<ge> j \<and> k \<le> hi \<longrightarrow> xs!k = xs0!k) \<comment> \<open>All elements from \<open>j\<close> to \<open>hi\<close> are unchanged\<close>
  \<close>

text \<open>The main part of the partition function. The pivot is assumed to be the last element. This is
exactly the "Lomuto partition scheme" partition function from Wikipedia.\<close>
definition partition_main :: \<open>('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> ('a list \<times> nat) nres\<close> where
  \<open>partition_main R h lo hi xs0 = do {
    ASSERT(hi < length xs0);
    pivot \<leftarrow> RETURN (h (xs0 ! hi));
    (i,j,xs) \<leftarrow> WHILE\<^sub>T\<^bsup>partition_main_inv R h lo hi xs0\<^esup> \<comment> \<open>We loop from \<^term>\<open>j=lo\<close> to \<^term>\<open>j=hi-1\<close>.\<close>
      (\<lambda>(i,j,xs). j < hi)
      (\<lambda>(i,j,xs). do {
        ASSERT(i < length xs \<and> j < length xs);
      	if R (h (xs!j)) pivot
      	then RETURN (i+1, j+1, swap xs i j)
      	else RETURN (i,   j+1, xs)
      })
      (lo, lo, xs0); \<comment> \<open>i and j are both initialized to lo\<close>
    ASSERT(i < length xs \<and> j = hi \<and> lo \<le> i \<and> hi < length xs \<and> mset xs = mset xs0);
    RETURN (swap xs i hi, i)
  }\<close>

lemma partition_main_correct:
  assumes \<open>lo < length xs\<close> and \<open>hi < length xs\<close> and \<open>hi > lo\<close> and
    \<open>\<And> x y z. \<lbrakk>R (h x) (h y); R (h y) (h z)\<rbrakk> \<Longrightarrow> R (h x) (h z)\<close> and \<open>\<And>x y. R (h x) (h y) \<or> R (h y) (h x)\<close> (* and \<open>\<And>x. R (h x) (h x)\<close> *) \<comment> \<open>TODO: Which properties do we need?\<close>
  shows \<open>partition_main R h lo hi xs \<le> SPEC(\<lambda>(xs', p). mset xs = mset xs' \<and> p < length xs \<and>
     p \<ge> lo \<and> p \<le> hi \<and> isPartition_map R h xs' lo hi p)\<close> \<comment> \<open>TODO: Show that \<open>p\<close> is a valid partiton.\<close>
proof -
  have K: \<open>b \<le> hi - Suc n \<Longrightarrow> n > 0 \<Longrightarrow> Suc n \<le> hi \<Longrightarrow> Suc b \<le> hi - n\<close> for b hi n
    by auto
  have L: \<open>~ R (h x) (h y) \<Longrightarrow> R (h y) (h x)\<close> for x y \<comment> \<open>Corollary of linearity\<close>
    using assms by blast
  have M: \<open>a < Suc b \<equiv> a = b \<or> a < b\<close> for a b
    by linarith
  have N: \<open>(a::nat) \<le> b \<equiv> a = b \<or> a < b\<close> for a b
    by arith

  show ?thesis
    unfolding partition_main_def choose_pivot_def
    apply (refine_vcg WHILEIT_rule[where R = \<open>measure(\<lambda>(i,j,xs). hi-j)\<close>])
    subgoal using assms by blast \<comment> \<open>We feed our assumption to the assertion\<close>
    subgoal by auto \<comment> \<open>WF\<close>
    subgoal \<comment> \<open>Invariant holds before the first iteration\<close>
      unfolding partition_main_inv_def
      using assms apply simp by linarith
    subgoal unfolding partition_main_inv_def by simp
    subgoal unfolding partition_main_inv_def by simp
    subgoal
      unfolding partition_main_inv_def
      apply (auto dest: mset_eq_length)
      done
    subgoal unfolding partition_main_inv_def by (auto dest: mset_eq_length)
    subgoal
      unfolding partition_main_inv_def apply (auto dest: mset_eq_length)
      apply (auto simp add: M) using assms(5) by blast

    subgoal unfolding partition_main_inv_def by simp \<comment> \<open>assertions, etc\<close>
    subgoal unfolding partition_main_inv_def by simp
    subgoal unfolding partition_main_inv_def by (auto dest: mset_eq_length)
    subgoal unfolding partition_main_inv_def by simp
    subgoal unfolding partition_main_inv_def by (auto dest: mset_eq_length)
    subgoal unfolding partition_main_inv_def by (auto dest: mset_eq_length)
    subgoal unfolding partition_main_inv_def by (auto dest: mset_eq_length)
    subgoal unfolding partition_main_inv_def by simp
    subgoal unfolding partition_main_inv_def by simp
    subgoal unfolding partition_main_inv_def by simp

    subgoal \<comment> \<open>After the last iteration, we have a partitioning! :-)\<close>
      unfolding partition_main_inv_def by (auto simp add: isPartition_wrt_def)
    done
qed


definition partition_between :: \<open>('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> ('a list \<times> nat) nres\<close> where
  \<open>partition_between R h lo hi xs0 = do {
    ASSERT(lo < length xs0 \<and> hi < length xs0 \<and> hi > lo);
    k \<leftarrow> choose_pivot R h xs0 lo hi; \<comment> \<open>choice of pivot\<close>
    ASSERT(k < length xs0);
    xs \<leftarrow> RETURN (swap xs0 k hi); \<comment> \<open>move the pivot to the last position, before we start the actual loop\<close>
    ASSERT(length xs = length xs0);
    partition_main R h lo hi xs
  }\<close>


lemma partition_between_correct:
  assumes \<open>lo < length xs\<close> and \<open>hi < length xs\<close> and \<open>hi > lo\<close> and
  \<open>\<And> x y z. \<lbrakk>R (h x) (h y); R (h y) (h z)\<rbrakk> \<Longrightarrow> R (h x) (h z)\<close> and \<open>\<And>x y. R (h x) (h y) \<or> R (h y) (h x)\<close> and \<open>\<And>x. R (h x) (h x)\<close>
  shows \<open>partition_between R h lo hi xs \<le> SPEC(\<lambda>(xs', p). mset xs = mset xs' \<and> p < length xs \<and>
     p \<ge> lo \<and> p \<le> hi \<and> isPartition_map R h xs' lo hi p)\<close> \<comment> \<open>TODO: Maxi: Show that \<open>p\<close> is a valid partiton.\<close>
proof -
  have K: \<open>b \<le> hi - Suc n \<Longrightarrow> n > 0 \<Longrightarrow> Suc n \<le> hi \<Longrightarrow> Suc b \<le> hi - n\<close> for b hi n
    by auto
  show ?thesis
    unfolding partition_between_def choose_pivot_def
    apply (refine_vcg partition_main_correct)
    using assms by (auto dest: mset_eq_length)
qed

(* TODO: Verify! *)
definition quicksort :: \<open>('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list nres\<close> where
\<open>quicksort R h lo hi xs0 = do {
  RECT (\<lambda>f (lo,hi,xs). do {
      ASSERT(mset xs = mset xs0);
      if hi\<le>lo then RETURN xs
      else do{
	      (xs, p) \<leftarrow> partition_between R h lo hi xs; \<comment> \<open>TODO: We could maybe do this abstract\<close>
	      xs \<leftarrow> f (lo, p-1, xs);
        f (p+1, hi, xs)
      }
    })
    (lo, hi, xs0)
  }\<close>



lemma sublist_map: \<open>sublist (map f xs) i j = map f (sublist xs i j)\<close>
  apply (auto simp add: sublist_def)
  by (simp add: drop_map take_map)

lemma sublist_split: \<open>lo \<le> hi \<Longrightarrow> lo < p \<Longrightarrow> p < hi \<Longrightarrow> hi < length xs \<Longrightarrow> sublist xs lo (p-1) @ xs!p # sublist xs (p+1) hi = sublist xs lo hi\<close>
  unfolding sublist_def
  apply simp
  apply (induction xs arbitrary: lo hi p)
   apply simp
  apply simp
  apply (cases lo)
  sorry \<comment> \<open>TODO: I need to sleep.\<close>

lemma take_set: \<open>j \<le> length xs \<Longrightarrow> x \<in> set (take j xs) \<equiv> (\<exists> k. k < j \<and> xs!k = x)\<close>
  apply (induction xs)
   apply simp
    by (meson in_set_conv_iff less_le_trans)

lemma sublist_el: \<open>i \<le> j \<Longrightarrow> j < length xs \<Longrightarrow> x \<in> set (sublist xs i j) \<equiv> (\<exists> k. k < Suc j-i \<and> xs!(i+k)=x)\<close>
  apply (simp add: sublist_def)
  by (auto simp add: take_set)

lemma sublist_el': \<open>i \<le> j \<Longrightarrow> j < length xs \<Longrightarrow> x \<in> set (sublist xs i j) \<equiv> (\<exists> k. i\<le>k\<and>k\<le>j \<and> xs!k=x)\<close>
  apply (simp add: sublist_el)
  by (smt Groups.add_ac(2) le_add1 le_add_diff_inverse less_Suc_eq less_diff_conv nat_less_le order_refl)

lemma partition_sort: \<open>lo < hi \<Longrightarrow> lo < p \<Longrightarrow> p < hi \<Longrightarrow> hi < length xs \<Longrightarrow> isPartition xs lo hi p \<Longrightarrow> sorted_sublist xs lo (p-1) \<Longrightarrow> sorted_sublist xs (p+1) hi \<Longrightarrow> sorted_sublist xs lo hi\<close>
  apply (auto simp add: isPartition_def isPartition_wrt_def sorted_sublist_def  sorted_sublist_wrt_def sublist_map)
  apply (simp add: sublist_split[symmetric])
  apply (auto simp add: List.sorted_wrt_append)
  subgoal by (auto simp add: sublist_el)
  subgoal by (auto simp add: sublist_el)
  apply (auto simp add: sublist_el)
  by (metis Suc_le_eq ab_semigroup_add_class.add.commute le_add1 less_add_Suc1 less_diff_conv order_trans)
  
text \<open>This lemma only holds for good R\<close>
lemma partition_sort_wrt:
\<open>lo < hi \<Longrightarrow> lo < p \<Longrightarrow> p < hi \<Longrightarrow> hi < length xs \<Longrightarrow> isPartition_wrt R xs lo hi p \<Longrightarrow> sorted_sublist_wrt R xs lo (p-1) \<Longrightarrow> sorted_sublist_wrt R xs (p+1) hi \<Longrightarrow> sorted_sublist_wrt R xs lo hi\<close>
  nitpick \<comment> \<open>Creative counter example\<dots>\<close>
  apply (auto simp add: isPartition_def sorted_sublist_wrt_def sublist_map)
  apply (simp add: sublist_split[symmetric])
  apply (auto simp add: List.sorted_wrt_append)
  subgoal apply (auto simp add: sublist_el) sorry
  subgoal apply (auto simp add: sublist_el) sorry
  subgoal apply (auto simp add: sublist_el) sorry
  oops


lemma quicksort_correct:
  assumes \<open>lo < length xs \<or> (lo \<ge> length xs \<and> hi \<le> lo)\<close> and \<open>(hi < length xs \<or> (hi \<ge> length xs \<and> hi \<le> lo))\<close> and
  \<open>\<And> x y z. \<lbrakk>R (h x) (h y); R (h y) (h z)\<rbrakk> \<Longrightarrow> R (h x) (h z)\<close> and \<open>\<And>x y. R (h x) (h y) \<or> R (h y) (h x)\<close> and \<open>\<And>x. R (h x) (h x)\<close>
  shows \<open>quicksort R h lo hi xs \<le> \<Down> Id (SPEC(\<lambda>xs'. mset xs = mset xs'))\<close> \<comment> \<open>TODO: Maxi: Sortedness\<close>
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
      apply (rule partition_between_correct[THEN order_trans])
      subgoal by (auto dest: mset_eq_length)
      subgoal by (auto dest: mset_eq_length)
      subgoal by (auto dest: mset_eq_length)
      subgoal by (auto dest: assms(3)) \<comment> \<open>We need to proof transitivity, etc here\<close>
      subgoal by (rule assms(4)) \<comment> \<open>linearity\<close>
      subgoal by (rule assms(5)) \<comment> \<open>reflexivity\<close>
      
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
    partition_main R h lo hi xs
  }\<close>


lemma partition_main_ref':
  \<open>partition_main R h lo hi xs
    \<le> \<Down> ((\<lambda> a b c d. Id) a b c d) (partition_main R h lo hi xs)\<close>
  by auto

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

  show ?thesis
    apply (subst (2) Down_id_eq[symmetric])
    unfolding partition_between_ref_def
      partition_between_def FOREACH_patterns
      LIST_FOREACH'_def[of \<open>RETURN _\<close>, unfolded nres_monad1, symmetric]
      OP_def
    apply (refine_vcg choose_pivot3_choose_pivot swap partition_main_correct)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    by (auto intro: Refine_Basic.Id_refine dest: mset_eq_length)
qed

text \<open>Technical lemma for sepref\<close>
lemma partition_between_ref_partition_between':
  \<open>(uncurry2 (partition_between_ref R h), uncurry2 (partition_between R h)) \<in>
    nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f \<langle>Id\<rangle>list_rel \<rightarrow>\<^sub>f \<langle>\<langle>Id\<rangle>list_rel \<times>\<^sub>r nat_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto intro: partition_between_ref_partition_between)

text \<open>Example instantiation for pivot\<close>
definition choose_pivot3_impl where
  \<open>choose_pivot3_impl = choose_pivot3 (\<le>) id\<close>

sepref_register choose_pivot3

text \<open>Example instantiation code for pivot\<close>
sepref_definition choose_pivot3_impl_code
  is \<open>uncurry2 (choose_pivot3_impl)\<close>
  :: \<open>(arl_assn nat_assn)\<^sup>k  *\<^sub>a  nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k\<rightarrow>\<^sub>a nat_assn\<close>
  unfolding choose_pivot3_impl_def choose_pivot3_def id_def
  by sepref

declare choose_pivot3_impl_code.refine[sepref_fr_rules]



text \<open>Example instantiation for partition_main\<close>
definition partition_main_impl where
  \<open>partition_main_impl = partition_main (\<le>) id\<close>

sepref_register partition_main_impl

text \<open>Example instantiation code for partition_main\<close>
sepref_definition partition_main_code
  is \<open>uncurry2 (partition_main_impl)\<close>
  :: \<open>nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a (arl_assn nat_assn)\<^sup>d \<rightarrow>\<^sub>a
      arl_assn nat_assn *a nat_assn\<close>
  unfolding partition_main_impl_def partition_main_def
  unfolding id_def
  by sepref

declare partition_main_code.refine[sepref_fr_rules]


text \<open>Example instantiation for partition\<close>
definition partition_between_impl where
  \<open>partition_between_impl = partition_between_ref (\<le>) id\<close>

sepref_register partition_between_ref

text \<open>Example instantiation code for partition\<close>
sepref_definition partition_between_code
  is \<open>uncurry2 (partition_between_impl)\<close>
  :: \<open>nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a (arl_assn nat_assn)\<^sup>d \<rightarrow>\<^sub>a
      arl_assn nat_assn *a nat_assn\<close>
  unfolding partition_between_ref_def partition_between_impl_def
    choose_pivot3_impl_def[symmetric] partition_main_impl_def[symmetric]
  unfolding id_def
  by sepref

declare partition_between_code.refine[sepref_fr_rules]


text \<open>Refined quicksort algorithm: We use the refined partition function.\<close>
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
  have f: \<open>f (x1b, x2e - 1, x1e) \<comment> \<open>Boilerplate code for first recursive call\<close>
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
  have f': \<open>f (x2e + 1, x1c, xsa) \<le> \<Down> Id (fa (x2d + 1, x1a, xsaa))\<close>  \<comment> \<open>Boilerplate code for second recursive call\<close>
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
  \<open>quicksort_impl = quicksort_ref (\<le>) id\<close>

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
  \<open>full_quicksort_impl xs = full_quicksort_ref (\<le>) id xs\<close>

lemma full_quicksort_ref_full_quicksort:
  \<open>(full_quicksort_ref R h, full_quicksort R h) \<in>
    \<langle>Id\<rangle>list_rel \<rightarrow>\<^sub>f \<langle> \<langle>Id\<rangle>list_rel\<rangle>nres_rel\<close>
  unfolding full_quicksort_ref_def full_quicksort_def
  by (intro frefI nres_relI)
     (auto intro!: quicksort_ref_quicksort[unfolded Down_id_eq]
       simp: List.null_def)

text \<open>Executable code for the example instance\<close>
sepref_definition full_quicksort_code
  is \<open>full_quicksort_impl\<close>
  :: \<open>(arl_assn nat_assn)\<^sup>d \<rightarrow>\<^sub>a
      arl_assn nat_assn\<close>
  unfolding full_quicksort_impl_def full_quicksort_ref_def quicksort_impl_def[symmetric] List.null_def
  by sepref

text \<open>Export the code\<close>
export_code \<open>nat_of_integer\<close> \<open>integer_of_nat\<close> \<open>partition_between_code\<close> \<open>full_quicksort_code\<close> in SML_imp module_name IsaQuicksort file "code/quicksort.sml"

text \<open>Final correctness lemma\<close>
lemma full_quicksort_correct:
  assumes
    \<open>\<And> x y z. \<lbrakk>R (h x) (h y); R (h y) (h z)\<rbrakk> \<Longrightarrow> R (h x) (h z)\<close> and \<open>\<And>x y. R (h x) (h y) \<or> R (h y) (h x)\<close> and \<open>\<And>x. R (h x) (h x)\<close>
  shows \<open>full_quicksort R h xs \<le> \<Down> Id (SPEC(\<lambda>xs'. mset xs = mset xs'))\<close>
  unfolding full_quicksort_def
  apply (rule order_trans)
   prefer 1
   apply (rule quicksort_correct[where R=R])
       apply auto
  using assms apply auto
  subgoal by (meson diff_Suc_less length_greater_0_conv)
  subgoal by force
  done

end
